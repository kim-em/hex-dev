"""Check the retained core-use evidence; optionally recompute it on matching sources."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
ARTIFACTS = ('README.md', 'assessment-crosswalk.json.gz', 'audit-imports.json.gz', 'audit.lean.txt', 'check_bindings.py', 'declaration-use.json.gz', 'derive.py', 'downstream-use.json.gz', 'handwritten.json.gz', 'helper-paths.json.gz', 'inputs.json.gz', 'module-roles.json.gz', 'production-import-coverage.json.gz', 'public-dispositions.md', 'retention-decisions.json.gz', 'structure-fields.json.gz', 'summary.json.gz', 'test_tools.py')
HELPERS = ('reports/sign-det-declaration-review/current/check_bindings.py', 'reports/sign-det-declaration-review/current/normalize.py', 'reports/sturm-declaration-review/audit_tools.py', 'scripts/bench/sweep_freshness.py', 'scripts/ci/check_benches_mathlib_free.py', 'scripts/libgraph.py')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(current=False):
    record = json.loads((BASE / 'bindings.json').read_text())
    if set(record['artifacts']) != set(ARTIFACTS):
        raise ValueError('core-use artifact scope differs')
    if set(record['tools']) != set(HELPERS):
        raise ValueError('core-use helper scope differs')
    revision = subprocess.check_output(
        ['git', 'rev-parse', '--verify', 'refs/tags/' + record['input_tag'] + '^{commit}'],
        cwd=ROOT, text=True).strip()
    if revision != record['input_revision']:
        raise ValueError('core-use input tag differs')
    tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', revision],
                                      cwd=ROOT, text=True).splitlines()
    expected = {name for name in tracked if name.endswith('.lean') or
                (name.startswith('reports/sign-det-declaration-review/core-') and
                 name.endswith('.md'))}
    expected.update(('lakefile.lean', 'lake-manifest.json', 'lean-toolchain'))
    if set(record['inputs']) != expected:
        raise ValueError('core-use input scope differs')
    # Use the same batched Git-object framing as the existing companion checker.
    with subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        for name, expected_hash in (record['inputs'] | record['tools']).items():
            process.stdin.write((revision + ':' + name + '\n').encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            if len(header) != 3 or header[1] != b'blob':
                raise ValueError('missing checkpoint source: ' + name)
            contents = process.stdout.read(int(header[2]))
            if process.stdout.read(1) != b'\n' or digest(contents) != expected_hash:
                raise ValueError('checkpoint bytes differ: ' + name)
        process.stdin.close()
        if process.wait() != 0:
            raise ValueError('checkpoint object reader failed')
    for name, expected in record['artifacts'].items():
        if digest((BASE / name).read_bytes()) != expected:
            raise ValueError('core-use artifact differs: ' + name)
    data = {p.name.removesuffix('.gz'): gzip.decompress(p.read_bytes())
            for p in BASE.glob('*.json.gz')}
    decisions = json.loads(data['retention-decisions.json'])['decisions']
    summary = json.loads(data['summary.json'])
    names = [d['name'] for d in decisions]
    if len(names) != len(set(names)) or set(names) != {
            d['name'] for d in summary['public_without_external_production_path']}:
        raise ValueError('retention inventory differs')
    if any(d['decision'] != 'retain' or not d['rationale'] for d in decisions):
        raise ValueError('missing explicit API decision')
    document = (BASE / 'public-dispositions.md').read_text()
    for d in decisions:
        if document.count('## `' + d['public_name'] + '`') != 1 or d['rationale'] not in document:
            raise ValueError('public disposition differs: ' + d['name'])
    if current:
        for name, expected in (record['inputs'] | record['tools']).items():
            if digest((ROOT / name).read_bytes()) != expected:
                raise ValueError('current core-use source differs: ' + name)
        with tempfile.TemporaryDirectory(prefix='signdet-core-use-') as directory:
            output = Path(directory)
            for name, contents in data.items():
                (output / name).write_bytes(contents)
            subprocess.run([sys.executable, str(BASE / 'derive.py'), str(output)],
                           cwd=ROOT, check=True)
            for name in record['derived']:
                if (output / name).read_bytes() != data[name]:
                    raise ValueError('derived core-use evidence differs: ' + name)
    print('Verified core-use archive and 149 public decisions' +
          ('; current-source derivation agrees.' if current else '.'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--current', action='store_true')
    check(parser.parse_args().current)
