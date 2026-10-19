"""Bind original-workload oracle identities to the verified archive inventory."""
import json
from pathlib import Path

from scripts.oracle.real_closure_number_field_samples import require

SOURCE_MANIFEST = (Path(__file__).resolve().parents[2] /
                   'reports/bench-results/real-closure-cade24-inputs/source.json')


def require_source_hashes(names, expected):
    document = json.loads(SOURCE_MANIFEST.read_text())
    require(type(document) is dict and
            document.get('schema') == 'real-closure-cade24-inputs-v1' and
            type(document.get('scripts')) is list and
            all(type(entry) is dict for entry in document['scripts']),
            'wrong CADE-24 source manifest')
    actual = []
    for name in names:
        entries = [entry for entry in document['scripts'] if entry.get('name') == name]
        require(len(entries) == 1, 'missing or duplicate original script identity')
        actual.append(entries[0].get('sha256'))
    require(actual == expected, 'original source manifest differs from oracle identities')
