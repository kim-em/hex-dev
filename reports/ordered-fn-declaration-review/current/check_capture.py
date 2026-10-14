"""Verify the source and artifact bytes of the current OrderedFn capture."""
import argparse
import hashlib
import subprocess
import json
from pathlib import Path

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
    record = json.loads((BASE / 'bindings.json').read_text())
    revision = subprocess.check_output(['git', 'rev-parse', record['source_tag'] + '^{commit}'], cwd=ROOT, text=True).strip()
    require(revision == record['source_revision'], 'source tag differs')
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
    from normalize import normalized
    for name, data in normalized(BASE).items():
        require((BASE / name).read_text() == json.dumps(data, indent=2, sort_keys=True) + '\n', 'normalized artifact differs: ' + name)
    rows = json.loads((BASE / 'declaration-use.json').read_text())
    fields = json.loads((BASE / 'structure-fields.json').read_text())
    imports = json.loads((BASE / 'audit-imports.json').read_text())
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
