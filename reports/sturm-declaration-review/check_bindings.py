"""Bind and check the root-package audit inputs and retained reference reports."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
import shutil
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from audit_tools import SourceIndex, client_status, disposition_rows


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    index = SourceIndex()
    imported = json.loads((BASE / 'audit-imports.json').read_text())
    roles = {module: index.resolve(module) for module in sorted(imported)}
    assert roles == json.loads((BASE / 'module-roles.json').read_text()), 'incorrect module source roles'
    paths = {role['path'] for role in roles.values() if role['package'] == 'root'}
    # The coverage scan reads every tracked production import header. Bind all
    # tracked Lean sources so its absence claims also refer to the checkpoint.
    paths.update(subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines())
    paths.update(json.loads((BASE / 'source-occurrences.json').read_text())['files'])
    paths.update(('lakefile.lean', 'lake-manifest.json', 'lean-toolchain',
                  'HexSturmMathlib/LintTests.lean', 'conformance/HexSturm/Conformance.lean',
                  'scripts/ci/check_benches_mathlib_free.py', 'scripts/libgraph.py'))
    paths.update('reports/sturm-declaration-review/' + name
                 for name in ('audit.lean.txt', 'normalize.py', 'manifest.json', 'check_bindings.py', 'audit_tools.py', 'test_audit_tools.py'))
    return {path: digest(ROOT / path) for path in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', metavar='INPUT_REVISION')
    args = parser.parse_args()
    rows = json.loads((BASE / 'declaration-use.json').read_text())
    downstream = json.loads((BASE / 'downstream-use.json').read_text())
    fields = json.loads((BASE / 'source-fields.json').read_text())
    helpers = json.loads((BASE / 'helper-paths.json').read_text())
    binding = BASE / 'usage-bindings.json'
    if args.write:
        revision = subprocess.check_output(
            ['git', 'rev-parse', '--verify', args.write + '^{commit}'], cwd=ROOT, text=True).strip()
        artifacts = ('README.md', 'zero-references.md', 'declaration-use.json', 'audit-imports.json',
                     'module-roles.json', 'downstream-use.json', 'source-fields.json', 'structure-fields.json', 'production-import-coverage.json',
                     'generated-origins.json', 'helper-paths.json', 'source-occurrences.json')
        result = {
            'input_revision': revision,
            'scope': 'All tracked root-package Lean sources (including the production coverage scan), plus lint/control/config and audit tools. External dependency bytes are governed by the recorded lock/toolchain, not separately inventoried. Selected imported environment; no external-client or automation-registration completeness claim. Artifact hashes are separate from source-input hashes. Manual re-attestation.',
            'compiled_attributed_constants': len(rows),
            'handwritten_declarations': json.loads((BASE / 'manifest.json').read_text())['declaration_count'],
            'source_written_structure_fields': len(fields),
            'private_paths_to_public_interfaces': len(helpers),
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
    assert result['compiled_attributed_constants'] == len(rows)
    manifest = json.loads((BASE / 'manifest.json').read_text())
    assert result['handwritten_declarations'] == manifest['declaration_count']
    for module in manifest['modules']:
        assert digest(ROOT / module['path']) == module['reviewed_sha256'], module['path']
        reviewed = subprocess.check_output(['git', 'show', manifest['reviewed_revision'] + ':' + module['path']], cwd=ROOT)
        assert hashlib.sha256(reviewed).hexdigest() == module['reviewed_sha256'], module['path']
    assert result['source_written_structure_fields'] == len(fields)
    assert result['private_paths_to_public_interfaces'] == len(helpers)
    assert result['public_without_downstream_production_path'] == len(downstream['public_without_downstream_production_path'])
    table = disposition_rows((BASE / 'zero-references.md').read_text())
    dispositions = [name for name, _, _ in table]
    expected = downstream['public_without_downstream_production_path']
    assert len(dispositions) == len(set(dispositions)), 'duplicate API disposition'
    assert set(dispositions) == set(expected), 'missing or extra downstream-use disposition'
    assert len(fields) == len({row['name'] for row in fields})
    assert {row['name'] for row in fields} == {
        row['projection'] for row in json.loads((BASE / 'structure-fields.json').read_text())}
    assert len(helpers) == len({row['helper'] for row in helpers})
    origins = json.loads((BASE / 'generated-origins.json').read_text())
    assert sum(origins['counts'].values()) + manifest['declaration_count'] + len(fields) == len(rows)
    assert all(origins['counts'][kind] == len(values) for kind, values in origins['artifacts'].items())
    roles = json.loads((BASE / 'module-roles.json').read_text())
    for name, status, _ in table:
        assert status.strip() == client_status(name, downstream, roles), (name, status)
    derived = ('declaration-use.json', 'module-roles.json', 'downstream-use.json',
               'source-fields.json', 'generated-origins.json', 'helper-paths.json', 'source-occurrences.json',
               'production-import-coverage.json')
    with tempfile.TemporaryDirectory() as directory:
        temp = Path(directory)
        for name in ('declaration-use.json', 'manifest.json', 'audit-imports.json', 'structure-fields.json'):
            shutil.copyfile(BASE / name, temp / name)
        subprocess.run([sys.executable, str(BASE / 'normalize.py'), '--output-dir', str(temp)], cwd=ROOT, check=True)
        for name in derived:
            assert (temp / name).read_bytes() == (BASE / name).read_bytes(), ('incorrect derivation', name)
    assert all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for row in rows)
    print(f"Checked {len(result['inputs'])} source inputs and {len(result['artifacts'])} artifacts at {result['input_revision']}")


if __name__ == '__main__':
    main()
