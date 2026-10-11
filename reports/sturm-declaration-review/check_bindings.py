"""Bind and check the root-package audit inputs and retained reference reports."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from scripts.ci.check_benches_mathlib_free import _lean_lib_source_dirs


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    roots = list(dict.fromkeys([ROOT] + [ROOT / source
        for source in _lean_lib_source_dirs(ROOT / 'lakefile.lean')]))
    paths = set()
    imported = json.loads((BASE / 'audit-imports.json').read_text())
    for module in imported:
        relative = Path(*module.split('.')).with_suffix('.lean')
        for root in roots:
            candidate = root / relative
            if candidate.is_file():
                paths.add(candidate.relative_to(ROOT).as_posix())
                break
    paths.update(json.loads((BASE / 'source-occurrences.json').read_text())['files'])
    paths.update(('lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
                  'HexSturmMathlib/LintTests.lean', 'conformance/HexSturm/Conformance.lean',
                  'scripts/ci/check_benches_mathlib_free.py', 'scripts/libgraph.py'))
    paths.update('reports/sturm-declaration-review/' + name
                 for name in ('audit.lean.txt', 'normalize.py', 'manifest.json', 'check_bindings.py'))
    return {path: digest(ROOT / path) for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', metavar='INPUT_REVISION')
    args = parser.parse_args()
    rows = json.loads((BASE / 'declaration-use.json').read_text())
    downstream = json.loads((BASE / 'downstream-use.json').read_text())
    binding = BASE / 'usage-bindings.json'
    if args.write:
        revision = subprocess.check_output(
            ['git', 'rev-parse', '--verify', args.write + '^{commit}'], cwd=ROOT, text=True).strip()
        artifacts = ('README.md', 'zero-references.md', 'declaration-use.json', 'audit-imports.json',
                     'module-roles.json', 'downstream-use.json', 'source-fields.json',
                     'generated-origins.json', 'helper-paths.json', 'source-occurrences.json')
        result = {
            'input_revision': revision,
            'scope': 'All root-package sources in the actual compiled imported-module table, plus lexical-match sources, lint/control/config and audit tools. External dependency bytes are governed by the recorded lock/toolchain, not separately inventoried. Selected imported environment; no external-client or automation-registration completeness claim. Artifact hashes are separate from source-input hashes. Manual re-attestation.',
            'compiled_attributed_constants': len(rows),
            'handwritten_declarations': 126,
            'source_written_structure_fields': 8,
            'private_paths_to_public_interfaces': len(json.loads((BASE / 'helper-paths.json').read_text())),
            'public_without_downstream_production_path': len(downstream['public_without_downstream_production_path']),
            'inputs': inputs(),
            'artifacts': {'reports/sturm-declaration-review/' + name: digest(BASE / name)
                          for name in artifacts},
        }
        binding.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    result = json.loads(binding.read_text())
    assert re.fullmatch(r'[0-9a-f]{40}', result['input_revision']), 'expected a full commit SHA'
    assert result['inputs'] == inputs(), 'input scope or current bytes differ'
    for path, expected in result['inputs'].items():
        committed = subprocess.check_output(['git', 'show', result['input_revision'] + ':' + path], cwd=ROOT)
        assert hashlib.sha256(committed).hexdigest() == expected, path
    for path, expected in result['artifacts'].items():
        assert digest(ROOT / path) == expected, path
    occurrences = json.loads((BASE / 'source-occurrences.json').read_text())
    for path, expected in occurrences['files'].items():
        assert digest(ROOT / path) == expected, path
    assert result['compiled_attributed_constants'] == len(rows) == 241
    assert result['handwritten_declarations'] == 126
    assert result['source_written_structure_fields'] == 8
    assert result['public_without_downstream_production_path'] == len(downstream['public_without_downstream_production_path'])
    dispositions = re.findall(r'^\| `([^`]+)` \|', (BASE / 'zero-references.md').read_text(), re.MULTILINE)
    expected = downstream['public_without_downstream_production_path']
    assert len(dispositions) == len(set(dispositions)), 'duplicate API disposition'
    assert set(dispositions) == set(expected), 'missing or extra downstream-use disposition'
    fields = json.loads((BASE / 'source-fields.json').read_text())
    assert len(fields) == len({row['name'] for row in fields}) == 8
    helpers = json.loads((BASE / 'helper-paths.json').read_text())
    assert len(helpers) == len({row['helper'] for row in helpers}) == 22
    origins = json.loads((BASE / 'generated-origins.json').read_text())
    assert sum(origins['counts'].values()) == 107
    assert all(origins['counts'][kind] == len(values) for kind, values in origins['artifacts'].items())
    assert all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for row in rows)
    print(f"Checked {len(result['inputs'])} source inputs and {len(result['artifacts'])} artifacts at {result['input_revision']}")


if __name__ == '__main__':
    main()
