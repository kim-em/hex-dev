"""Bind the current companion audit to its committed source checkpoint."""
import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from normalize import derive, require
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


def inputs():
    paths = set(subprocess.check_output(["git", "ls-files", "*.lean"], cwd=ROOT, text=True).splitlines())
    paths.update(("lakefile.lean", "lake-manifest.json", "lean-toolchain",
                  "scripts/libgraph.py", "scripts/ci/check_benches_mathlib_free.py",
                  "reports/sturm-declaration-review/audit_tools.py",
                  "reports/sign-det-declaration-review/manifest.json",
                  "reports/sign-det-declaration-review/companion.md"))
    paths.update(str((BASE / name).relative_to(ROOT)) for name in TOOLS)
    return {path: digest(ROOT / path) for path in sorted(paths)}


def verify_structure(manifest, current):
    rows = json.loads((BASE / "declaration-use.json").read_text())
    require(len(rows) == 451, "unexpected attributed constant inventory")
    require({a for row in rows for a in row["axioms"]} ==
            {"propext", "Classical.choice", "Quot.sound"}, "unexpected axioms")
    if current:
        for module in manifest['modules']:
            require(digest(ROOT / module['path']) == module['reviewed_sha256'], module['path'])
        for name, expected in derive(BASE).items():
            require((BASE / name).read_text() == json.dumps(expected, indent=2, sort_keys=True) + '\n',
                    'derived artifact differs: ' + name)
    graph = json.loads((BASE / "downstream-use.json").read_text())
    disposition = (BASE / "public-dispositions.md", "generated-origins.json",
             "field-dispositions.md", "source-references.json").read_text()
    table = disposition_rows(disposition)
    names = [row[0] for row in table]
    for name, status, _purpose in table:
        expected = 'None' if not graph['filtered_users']['Hex.SignDet.' + name] else 'Companion and/or evidence references only'
        require(status == expected, 'client status differs: ' + name)
    require(len(names) == len(set(names)) == 64, "duplicate or incomplete public dispositions")
    require({"Hex.SignDet." + name for name in names} ==
            set(graph["public_without_downstream_production_path"]), "disposition inventory differs")
    fields = json.loads((BASE / "structure-fields.json").read_text())
    require(len(fields) == 5, "unexpected source structure fields")
    paths = json.loads((BASE / "helper-paths.json").read_text())
    require(len(paths) == 17, "unexpected private helper paths")
    origins = json.loads((BASE / 'generated-origins.json').read_text())
    require(origins['handwritten'] == manifest['declaration_count'], 'handwritten count differs')
    require(origins['fields'] == len(fields) and origins['handwritten'] + origins['fields'] + sum(origins['counts'].values()) == len(rows), 'constant accounting differs')
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', metavar='INPUT_REVISION')
    parser.add_argument('--tag', default='audit/issue-10575-sign-det-current-reviewed-input')
    parser.add_argument('--current', action='store_true', help='also require current source bytes and recompute derived evidence')
    args = parser.parse_args()
    binding = BASE / "bindings.json"
    if args.write:
        manifest = json.loads((BASE.parent / 'manifest.json').read_text())
        rows = verify_structure(manifest, True)
        revision = subprocess.check_output(["git", "rev-parse", args.write + "^{commit}"], cwd=ROOT, text=True).strip()
        record = {
            "input_revision": revision, "input_tag": args.tag,
            "scope": "All tracked root-package Lean sources, current audit tools and assessment, source-role/parser helpers, toolchain and lock. External bytes are governed by the exact dependency pins. Artifact hashes are separate. This is manual source/use attestation, not computational performance or external-client completeness.",
            "inputs": inputs(),
            "artifacts": {str((BASE / name).relative_to(ROOT)): digest(BASE / name) for name in ARTIFACTS},
            "compiled_constants": len(rows), "handwritten_declarations": manifest["declaration_count"],
        }
        binding.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    record = json.loads(binding.read_text())
    require(re.fullmatch(r"[0-9a-f]{40}", record["input_revision"]), "full checkpoint SHA required")
    tagged = subprocess.check_output(['git', 'rev-parse', record['input_tag'] + '^{commit}'], cwd=ROOT, text=True).strip()
    require(tagged == record['input_revision'], 'checkpoint tag differs')
    if args.current or args.write:
        require(record['inputs'] == inputs(), 'current source input scope or bytes differ')
    for path, expected in record["inputs"].items():
        committed = subprocess.check_output(["git", "show", record["input_revision"] + ":" + path], cwd=ROOT)
        require(hashlib.sha256(committed).hexdigest() == expected, "checkpoint differs: " + path)
    for path, expected in record["artifacts"].items():
        require(digest(ROOT / path) == expected, "artifact differs: " + path)
    captured_manifest = json.loads(subprocess.check_output(['git', 'show', record['input_revision'] + ':reports/sign-det-declaration-review/manifest.json'], cwd=ROOT))
    verify_structure(captured_manifest, args.current and not args.write)
    print(f"Verified {len(record['inputs'])} source inputs and {len(record['artifacts'])} current audit artifacts.")


if __name__ == "__main__":
    main()
