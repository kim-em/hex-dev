"""Bind the current companion audit to its committed source checkpoint."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from normalize import derive, require, lexical_references, reference_disposition, REFERENCE_INPUTS
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "reports/sturm-declaration-review"))
from audit_tools import disposition_rows

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
ARTIFACTS = ("README.md", "declaration-use.json", "structure-fields.json",
             "helper-paths.json", "downstream-use.json", "module-roles.json",
             "audit-imports.json", "production-import-coverage.json", "public-dispositions.md", "generated-origins.json",
             "field-dispositions.md", "source-references.json")
TOOLS = ("audit.lean.txt", "normalize.py", "check_bindings.py", "reproduce.py", "test_tools.py")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_paths(revision=None):
    if revision is None:
        paths = set(subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines())
    else:
        paths = {path for path in subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', revision], cwd=ROOT, text=True).splitlines() if path.endswith('.lean')}
    paths.update(("lakefile.lean", "lake-manifest.json", "lean-toolchain",
                  "scripts/libgraph.py", "scripts/ci/check_benches_mathlib_free.py",
                  "scripts/bench/sweep_freshness.py",
                  "reports/sturm-declaration-review/audit_tools.py",
                  "reports/sign-det-declaration-review/manifest.json",
                  "reports/sign-det-declaration-review/companion.md"))
    paths.update(REFERENCE_INPUTS)
    paths.update(str((BASE / name).relative_to(ROOT)) for name in TOOLS)
    return paths


def inputs():
    return {path: digest(ROOT / path) for path in sorted(input_paths())}


def verify_checkpoint(record):
    require(set(record['inputs']) == input_paths(record['input_revision']), 'checkpoint input scope differs')
    with subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        for path, expected in record['inputs'].items():
            process.stdin.write((record['input_revision'] + ':' + path + '\n').encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            require(len(header) == 3 and header[1] == b'blob', 'checkpoint object missing: ' + path)
            data = process.stdout.read(int(header[2]))
            require(process.stdout.read(1) == b'\n', 'invalid git object framing')
            require(hashlib.sha256(data).hexdigest() == expected, 'checkpoint differs: ' + path)
        process.stdin.close()
        require(process.wait() == 0, 'git checkpoint reader failed')


def verify_archive(record, complete=True):
    """Verify the named input checkpoint and the complete saved report tree."""
    require(re.fullmatch(r'[0-9a-f]{40}', record['input_revision']), 'full checkpoint SHA required')
    tagged = subprocess.check_output(['git', 'rev-parse', record['input_tag'] + '^{commit}'], cwd=ROOT, text=True).strip()
    require(tagged == record['input_revision'], 'checkpoint tag differs')
    verify_checkpoint(record)
    if complete:
        tag = record['archive_tag']
        subprocess.run(['git', 'merge-base', '--is-ancestor', record['input_revision'], tag], cwd=ROOT, check=True)
        binding_path = str((BASE / 'bindings.json').relative_to(ROOT))
        saved = subprocess.check_output(['git', 'show', tag + ':' + binding_path], cwd=ROOT)
        require(saved == (BASE / 'bindings.json').read_bytes(), 'complete archive binding differs')
        for path, expected in record['artifacts'].items():
            saved = subprocess.check_output(['git', 'show', tag + ':' + path], cwd=ROOT)
            require(hashlib.sha256(saved).hexdigest() == expected, 'complete archive artifact differs: ' + path)


def verify_structure(manifest, current):
    rows = json.loads((BASE / "declaration-use.json").read_text())
    require(len(rows) == 453, "unexpected attributed constant inventory")
    require({a for row in rows for a in row["axioms"]} ==
            {"propext", "Classical.choice", "Quot.sound"}, "unexpected axioms")
    if current:
        for module in manifest['modules']:
            require(digest(ROOT / module['path']) == module['reviewed_sha256'], module['path'])
        for name, expected in derive(BASE).items():
            require((BASE / name).read_text() == json.dumps(expected, indent=2, sort_keys=True) + '\n',
                    'derived artifact differs: ' + name)
    graph = json.loads((BASE / "downstream-use.json").read_text())
    disposition = (BASE / "public-dispositions.md").read_text()
    table = disposition_rows(disposition)
    names = [row[0] for row in table]
    for name, status, _purpose in table:
        expected = 'None' if not graph['filtered_users']['Hex.SignDet.' + name] else 'Companion and/or evidence references only'
        require(status == expected, 'client status differs: ' + name)
    require(len(names) == len(set(names)) == 64, "duplicate or incomplete public dispositions")
    require({"Hex.SignDet." + name for name in names} ==
            set(graph["public_without_downstream_production_path"]), "disposition inventory differs")
    fields = json.loads((BASE / "structure-fields.json").read_text())
    require({field['structure'] for field in fields} == {'Hex.SignDet.Node.Counted'}, 'unexpected field structure')
    require(len(fields) == 5, "unexpected source structure fields")
    paths = json.loads((BASE / "helper-paths.json").read_text())
    require(len(paths) == 17, "unexpected private helper paths")
    origins = json.loads((BASE / 'generated-origins.json').read_text())
    require(origins['handwritten'] == manifest['declaration_count'], 'handwritten count differs')
    require(origins['fields'] == len(fields) and origins['handwritten'] + origins['fields'] + sum(origins['counts'].values()) == len(rows), 'constant accounting differs')
    references = json.loads((BASE / 'source-references.json').read_text())
    if current:
        require(references == lexical_references(graph), 'supplementary references differ')
    by_name = {row['name']: row for row in references['declarations']}
    require(set(by_name) == set(graph['public_without_downstream_production_path']), 'reference inventory differs')
    for name, _status, purpose in table:
        record = by_name['Hex.SignDet.' + name]
        require(record['has_direct_term_reference'] == bool(graph['filtered_users'][record['name']]), 'term-reference status differs')
        require(purpose.endswith(reference_disposition(record)), 'reference disposition differs: ' + name)
        for path, line in re.findall(r'\[([^\]]+):(\d+)\]', purpose):
            require(any(ref['path'] == path and ref['line'] == int(line) for ref in record['references']), 'citation differs: ' + name)
    require('| Field | Reference clients | Disposition |' in (BASE / 'field-dispositions.md').read_text(), 'field table header differs')
    field_table = re.findall(r'^\| `([^`]+)` \| (\d+) \| ([^|]+) \|$', (BASE / 'field-dispositions.md').read_text(), re.MULTILINE)
    require(len(field_table) == len(fields), 'field disposition count differs')
    require({row[0] for row in field_table} == {row['field'] for row in fields}, 'field dispositions differ')
    for name, count, _purpose in field_table:
        field = next(row for row in fields if row['field'] == name)
        require(int(count) == len(graph['filtered_users'][field['projection']]), 'field references differ: ' + name)
    readme = (BASE / 'README.md').read_text()
    coverage = json.loads((BASE / 'production-import-coverage.json').read_text())
    imports = json.loads((BASE / 'audit-imports.json').read_text())
    counts = {
        'individually assessed declarations': manifest['declaration_count'],
        'compiled': len(rows),
        'companion production modules': len(manifest['modules']),
        'public declarations without a path': len(names),
        'tracked Hex production modules': coverage['required_modules'],
        'modules.': len(imports),
        'additional constants': sum(origins['counts'].values()),
    }
    for phrase, count in counts.items():
        require(re.search(r'(?<![\d,])' + re.escape(f'{count:,}') + r'\s+' + re.escape(phrase), readme),
                'README count differs: ' + phrase)
    direct_zero = sum(not graph['filtered_users']['Hex.SignDet.' + name] for name in names)
    require(direct_zero == 28 and 'Twenty-eight have no direct' in readme, 'README direct-reference count differs')
    require(len(paths) == 17 and 'seventeen private helpers' in readme, 'README helper count differs')
    require(len(fields) == 5 and 'Five structure fields' in readme, 'README field count differs')
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', metavar='INPUT_REVISION')
    parser.add_argument('--tag', default='audit/issue-10575-sign-det-current-reviewed-input-v5')
    parser.add_argument('--current', action='store_true', help='also require current source bytes and recompute derived evidence')
    args = parser.parse_args()
    binding = BASE / "bindings.json"
    if args.write:
        manifest = json.loads((BASE.parent / 'manifest.json').read_text())
        rows = verify_structure(manifest, True)
        revision = subprocess.check_output(["git", "rev-parse", args.write + "^{commit}"], cwd=ROOT, text=True).strip()
        record = {
            "input_revision": revision, "input_tag": args.tag,
            "archive_tag": args.tag.replace("-input", "-complete"),
            "scope": "All tracked root-package Lean sources, current audit tools and assessment, source-role/parser helpers, toolchain and lock. External bytes are governed by the exact dependency pins. Artifact hashes are separate. This is manual source/use attestation, not computational performance or external-client completeness.",
            "inputs": inputs(),
            "artifacts": {str((BASE / name).relative_to(ROOT)): digest(BASE / name) for name in ARTIFACTS},
            "compiled_constants": len(rows), "handwritten_declarations": manifest["declaration_count"],
        }
        binding.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    record = json.loads(binding.read_text())
    if args.current or args.write:
        require(record['inputs'] == inputs(), 'current source input scope or bytes differ')
    verify_archive(record, complete=not bool(args.write))
    for path, expected in record["artifacts"].items():
        require(digest(ROOT / path) == expected, "artifact differs: " + path)
    captured_manifest = json.loads(subprocess.check_output(['git', 'show', record['input_revision'] + ':reports/sign-det-declaration-review/manifest.json'], cwd=ROOT))
    verify_structure(captured_manifest, args.current and not args.write)
    print(f"Verified {len(record['inputs'])} source inputs and {len(record['artifacts'])} current audit artifacts.")


if __name__ == "__main__":
    main()
