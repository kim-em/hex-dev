"""Verify the source and artifact bytes of the current OrderedFn capture."""
import argparse
import importlib.util
import sys
import hashlib
import subprocess
import json
from pathlib import Path

sys.dont_write_bytecode = True

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[2]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--current', action='store_true', help='also require live source bytes')
    args = parser.parse_args()
    record = json.loads((BASE / 'bindings.json').read_text(encoding='utf-8'))
    revision = subprocess.check_output(['git', 'rev-parse', record['source_tag'] + '^{commit}'], cwd=ROOT, text=True).strip()
    require(revision == record['source_revision'], 'source tag differs')
    complete = record['complete_tag']
    subprocess.run(['git', 'merge-base', '--is-ancestor', revision, complete], cwd=ROOT, check=True)
    paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', revision], cwd=ROOT, text=True).splitlines()
    imported = json.loads((BASE / 'audit-imports.json').read_text(encoding='utf-8'))
    expected_lean = {'lakefile.lean'}
    for module in imported:
        suffix = module.replace('.', '/') + '.lean'
        expected_lean.update(prefix + suffix for prefix in ('', 'adapters/', 'conformance/', 'bench/') if prefix + suffix in paths)
    require({path for path in record['inputs'] if path.endswith('.lean')} == expected_lean, 'imported source closure differs')
    directory = str(BASE.relative_to(ROOT))
    archived_files = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', complete, '--', directory], cwd=ROOT, text=True).splitlines()
    expected_files = {directory + '/' + name for name in ('README.md', 'audit.lean.txt', 'normalize.py', 'check_capture.py', 'bindings.json', 'audit-imports.json', 'declaration-use.json', 'structure-fields.json')}
    require(set(archived_files) == expected_files, 'complete archive file inventory differs')
    for path in archived_files:
        saved = subprocess.check_output(['git', 'show', complete + ':' + path], cwd=ROOT)
        require(saved == (ROOT / path).read_bytes(), 'complete archive differs: ' + path)
    for path, expected in record['inputs'].items():
        committed = subprocess.check_output(['git', 'show', revision + ':' + path], cwd=ROOT)
        require(hashlib.sha256(committed).hexdigest() == expected, 'checkpoint source differs: ' + path)
        if args.current:
            require(digest(ROOT / path) == expected, 'current source differs: ' + path)
    for name, expected in record['artifacts'].items():
        require(digest(BASE / name) == expected, 'artifact differs: ' + name)
    require(digest(BASE / 'audit.lean.txt') == record['producer_sha256'], 'producer differs')
    require(digest(BASE / 'check_capture.py') == record['checker_sha256'], 'checker differs')
    require(digest(BASE / 'normalize.py') == record['normalizer_sha256'], 'normalizer differs')
    require(digest(BASE / 'README.md') == record['readme_sha256'], 'README differs')
    spec = importlib.util.spec_from_file_location('_hex_orderedfn_normalizer', BASE / 'normalize.py')
    normalizer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(normalizer)
    for name, data in normalizer.normalized(BASE).items():
        require((BASE / name).read_text(encoding='utf-8') == json.dumps(data, indent=2, sort_keys=True) + '\n', 'normalized artifact differs: ' + name)
    rows = json.loads((BASE / 'declaration-use.json').read_text(encoding='utf-8'))
    fields = json.loads((BASE / 'structure-fields.json').read_text(encoding='utf-8'))
    imports = json.loads((BASE / 'audit-imports.json').read_text(encoding='utf-8'))
    require(len(rows) == len({row['name'] for row in rows}) == record['compiled_constants'], 'constant inventory differs')
    require({row['module'] for row in rows} == set(record['modules']), 'module inventory differs')
    require(set(record['modules']) <= set(imports), 'missing production import')
    require(sorted({axiom for row in rows for axiom in row['axioms']}) == record['axioms'] ==
            ['Classical.choice', 'Quot.sound', 'propext'], 'unexpected axioms')
    require(all(row['kind'] != 'axiom' for row in rows), 'owned axiom declaration')
    require(len(fields) == len({field['projection'] for field in fields}) == record['fields'], 'field inventory differs')
    require({field['projection'] for field in fields} <= {row['name'] for row in rows}, 'field projection not captured')
    print(f"Verified {len(rows)} constants, {len(fields)} fields and {len(record['modules'])} production modules.")


if __name__ == '__main__':
    main()
