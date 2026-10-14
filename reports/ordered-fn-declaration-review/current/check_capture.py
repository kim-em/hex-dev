"""Verify the source and artifact bytes of the current OrderedFn capture."""
import hashlib
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
    record = json.loads((BASE / 'bindings.json').read_text())
    for path, expected in record['inputs'].items():
        require(digest(ROOT / path) == expected, 'source differs: ' + path)
    for name, expected in record['artifacts'].items():
        require(digest(BASE / name) == expected, 'artifact differs: ' + name)
    require(digest(BASE / 'audit.lean.txt') == record['producer_sha256'], 'producer differs')
    require(digest(BASE / 'check_capture.py') == record['checker_sha256'], 'checker differs')
    require(digest(BASE / 'README.md') == record['readme_sha256'], 'README differs')
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
