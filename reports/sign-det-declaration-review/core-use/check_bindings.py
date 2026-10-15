"""Verify the source-specific core-use archive and optional current derivation."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]
RAW = ('inputs.json', 'declaration-use.json', 'structure-fields.json', 'audit-imports.json')
MANUAL = ('additional-constants.json',)
DERIVED = ('summary.json', 'handwritten.json', 'helper-paths.json', 'downstream-use.json',
           'module-roles.json', 'production-import-coverage.json', 'evidence-import-coverage.json')
ARTIFACTS = ('README.md', 'public-dispositions.md', 'audit.lean.txt', 'derive.py',
             'check_bindings.py', 'test_tools.py', 'evidence-scope.json') + tuple(
                 name + '.gz' for name in RAW + MANUAL + DERIVED +
                 ('assessment-crosswalk.json', 'retention-decisions.json'))
HELPERS = ('reports/sign-det-declaration-review/current/normalize.py',
           'reports/sign-det-declaration-review/current/check_bindings.py',
           'reports/sturm-declaration-review/audit_tools.py',
           'scripts/ci/check_benches_mathlib_free.py',
           'scripts/bench/sweep_freshness.py', 'scripts/libgraph.py')
DECISIONS = {'retain', 'make_private', 'remove', 'open'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(contents):
    return hashlib.sha256(contents).hexdigest()


def read_json(name):
    return json.loads(gzip.decompress((BASE / (name + '.gz')).read_bytes()))


def verify_document(decisions, document):
    """Bind each heading to its own decision, assessment and observed client count."""
    sections = re.split(r'^## `([^`]+)`\s*$', document, flags=re.MULTILINE)
    names = sections[1::2]
    require(len(names) == len(set(names)), 'duplicate disposition heading')
    bodies = dict(zip(names, sections[2::2]))
    require(set(bodies) == {row['public_name'] for row in decisions},
            'public disposition inventory differs')
    for row in decisions:
        require(row['decision'] in DECISIONS and bool(row['rationale']),
                'missing explicit API decision')
        assessment = row['individual_assessment']
        filename = Path(assessment['path']).name
        expected = (f"Decision: {row['decision']}. {row['rationale']}\n\n"
                    f"{assessment['purpose']}\n\n"
                    f"Assessment: [{filename}:{assessment['line']}](../{filename}). "
                    f"Alias-merged named clients: {len(row['clients'])}.")
        require(bodies[row['public_name']].strip() == expected,
                'public disposition section differs: ' + row['name'])


def facts(summary, rows, coverage, evidence, decisions):
    kinds = {row['name']: row['kind'] for row in rows}
    outside = summary['public_without_external_production_path']
    counts = Counter(kinds[row['name']] for row in outside)
    return {
        'Core modules': summary['production_modules'],
        'Attributed constants': summary['attributed_constants'],
        'Handwritten declarations': summary['handwritten'],
        'Structure fields': summary['fields'],
        'Private helpers': summary['private'],
        'Private helpers without a public path':
            len(summary['private_without_handwritten_public_path']),
        'Required production import consumers': coverage['required_modules'],
        'Selected evidence modules': len(evidence['required_modules']),
        'Excluded executable entry points': len(evidence['excluded_entry_points']),
        'Imported environment modules': summary['imported_modules'],
        'Public declarations without an external-core production path': len(outside),
        'Public declarations without direct named clients':
            len(summary['public_without_direct_clients']),
        'Outside-path theorems': counts['theorem'],
        'Outside-path definitions': counts['definition'],
        'Outside-path inductive or structure declarations': counts['inductive'],
        'Open API or integration decisions': sum(row['decision'] == 'open' for row in decisions)}


def verify_data(data):
    rows = data['declaration-use.json']
    summary = data['summary.json']
    decisions = data['retention-decisions.json']['decisions']
    coverage = data['production-import-coverage.json']
    evidence = data['evidence-import-coverage.json']
    all_names = {row['name'] for row in rows}
    handwritten = data['handwritten.json']
    private = {name for name in handwritten if name.startswith('_private.')}
    graph = data['downstream-use.json']
    require(len(all_names) == len(rows), 'duplicate attributed constant')
    require(set(handwritten) <= all_names, 'handwritten constant missing')
    require(summary['production_modules'] == len(set(data['inputs.json']['modules'])) ==
            len({row['module'] for row in rows}), 'module count differs')
    require(summary['imported_modules'] == len(data['audit-imports.json']),
            'imported environment count differs')
    require(summary['source_revision'] == data['inputs.json']['source_revision'],
            'capture source revision differs')
    require(data['inputs.json']['producer_sha256'] == digest((BASE / 'audit.lean.txt').read_bytes()),
            'capture producer differs')
    require({row['helper'] for row in data['helper-paths.json']} == private,
            'private helper inventory differs')
    for row in data['helper-paths.json']:
        path = row['path']
        require(path and path[0] == row['helper'] and path[-1] in set(handwritten) - private and
                all(right in graph['users'].get(left, []) for left, right in zip(path, path[1:])),
                'private helper path differs')
    kinds = {row['name']: row['kind'] for row in rows}
    require(all(kinds[name] == 'theorem' for name in summary['public_without_direct_clients']),
            'non-theorem without direct named clients')
    require(set(summary['public_without_direct_clients']) ==
            {name for name in set(handwritten) - private if not graph['users'].get(name)},
            'direct client inventory differs')
    require(all(row['individual_assessment'] == data['assessment-crosswalk.json'][row['name']]
                for row in decisions), 'individual assessment differs')
    names = [row['name'] for row in decisions]
    require(len(names) == len(set(names)) and set(names) == {
        row['name'] for row in summary['public_without_external_production_path']},
        'retention inventory differs')
    require(not summary['private_without_handwritten_public_path'],
            'private helper without public path')
    require(not coverage['missing_modules'] and not evidence['missing_modules'],
            'missing selected imports')
    require(summary['attributed_constants'] == len(rows), 'constant count differs')
    require(set(summary['axioms']) == {axiom for row in rows for axiom in row['axioms']} <=
            {'propext', 'Classical.choice', 'Quot.sound'}, 'unexpected core axioms')
    require(summary['private'] == len(data['helper-paths.json']), 'private path count differs')
    require(summary['fields'] == len(data['structure-fields.json']), 'field count differs')
    require(summary['handwritten'] == len(data['handwritten.json']), 'source count differs')
    require(summary['handwritten'] + summary['fields'] +
            len(data['additional-constants.json']) == len(rows), 'constant accounting differs')
    verify_document(decisions, (BASE / 'public-dispositions.md').read_text())
    table = re.findall(r'^\| ([^|]+) \| ([\d,]+) \|$',
                       (BASE / 'README.md').read_text(), re.MULTILINE)
    require(len(table) == len(dict(table)), 'duplicate README fact')
    observed = {name: int(number.replace(',', '')) for name, number in table}
    require(observed == facts(summary, rows, coverage, evidence, decisions),
            'README facts differ')
    return len(decisions)


def run_derivation(output):
    subprocess.run([sys.executable, str(BASE / 'derive.py'), str(output)],
                   cwd=ROOT, check=True)


def check(current=False):
    record = json.loads((BASE / 'bindings.json').read_text())
    require(set(record['artifacts']) == set(ARTIFACTS), 'core-use artifact scope differs')
    require({path.name for path in BASE.glob('*.json.gz')} ==
            {name for name in ARTIFACTS if name.endswith('.json.gz')},
            'unbound compressed evidence')
    require(set(record['tools']) == set(HELPERS), 'core-use helper scope differs')
    revision = subprocess.check_output(
        ['git', 'rev-parse', '--verify', 'refs/tags/' + record['input_tag'] + '^{commit}'],
        cwd=ROOT, text=True).strip()
    require(re.fullmatch(r'[0-9a-f]{40}', record['input_revision']) and
            revision == record['input_revision'], 'core-use input tag differs')
    tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', revision],
                                      cwd=ROOT, text=True).splitlines()
    expected = {name for name in tracked if name.endswith('.lean') or
                (name.startswith('reports/sign-det-declaration-review/core-') and
                 name.endswith('.md'))}
    expected.update(('lakefile.lean', 'lake-manifest.json', 'lean-toolchain'))
    require(set(record['inputs']) == expected, 'core-use input scope differs')
    # Batched Git-object framing follows the existing companion checker.
    with subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        for name, expected_hash in (record['inputs'] | record['tools']).items():
            process.stdin.write((revision + ':' + name + '\n').encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            require(len(header) == 3 and header[1] == b'blob', 'missing checkpoint source: ' + name)
            contents = process.stdout.read(int(header[2]))
            require(process.stdout.read(1) == b'\n' and digest(contents) == expected_hash,
                    'checkpoint bytes differ: ' + name)
        process.stdin.close()
        require(process.wait() == 0, 'checkpoint object reader failed')
    for name, expected_hash in record['artifacts'].items():
        require(digest((BASE / name).read_bytes()) == expected_hash,
                'core-use artifact differs: ' + name)
    data = {name.removesuffix('.gz'): read_json(name.removesuffix('.gz'))
            for name in ARTIFACTS if name.endswith('.json.gz')}
    require(data['inputs.json']['source_revision'] == revision, 'raw input revision differs')
    count = verify_data(data)
    if current:
        for name, expected_hash in (record['inputs'] | record['tools']).items():
            require(digest((ROOT / name).read_bytes()) == expected_hash,
                    'current core-use source differs: ' + name)
        with tempfile.TemporaryDirectory(prefix='signdet-core-use-') as directory:
            output = Path(directory)
            # Derived outputs must be freshly written, never preseeded from the archive.
            for name in RAW + MANUAL:
                (output / name).write_text(json.dumps(data[name], indent=2, sort_keys=True) + '\n')
            run_derivation(output)
            for name in DERIVED:
                require((output / name).is_file(), 'derived output missing: ' + name)
                require(json.loads((output / name).read_text()) == data[name],
                        'derived core-use evidence differs: ' + name)
    print(f'Verified core-use archive and {count} public decisions' +
          ('; current-source derivation agrees.' if current else '.'))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--current', action='store_true')
    check(parser.parse_args().current)
