"""Normalize the compiled inventory before comparing its committed SHA-256."""

import argparse
import hashlib
import json
import re
import subprocess
from collections import deque
from pathlib import Path

from audit_tools import SourceIndex, production_coverage, reference_graph

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
args = parser.parse_args()
source_root = Path(__file__).resolve().parents[2]
path = args.output_dir / "declaration-use.json"
rows = json.loads(path.read_text(encoding="utf-8"))
index = SourceIndex()
imports = json.loads(path.with_name("audit-imports.json").read_text())
roles = {module: index.resolve(module) for module in sorted(imports)}
assert all(module in roles for row in rows for module in row["user_modules"].values())
coverage = production_coverage(set(imports), index)
assert not coverage["missing_modules"], coverage["missing_modules"]
path.with_name("production-import-coverage.json").write_text(json.dumps(coverage, indent=2, sort_keys=True) + "\n")
path.with_name("module-roles.json").write_text(json.dumps(roles, indent=2, sort_keys=True) + "\n")

rows.sort(key=lambda row: (row["module"], row["name"]))
for row in rows:
    row["users_by_category"] = {}
    for user, module in row["user_modules"].items():
        category = roles[module]["category"]
        row["users_by_category"].setdefault(category, []).append(user)
    for users in row["users_by_category"].values():
        users.sort()
    row["users"].sort()
    row["axioms"].sort()
path.write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")

# Trace every private production helper to a handwritten declaration, allowing
# compiler-generated intermediate users. This is scoped to the imported audit.
manifest = json.loads(path.with_name("manifest.json").read_text(encoding="utf-8"))
handwritten = set()
private = []
public = set()
for module in manifest["modules"]:
    module_name = module["path"].removesuffix(".lean").replace("/", ".")
    owned = [row for row in rows if row["module"] == module_name]
    for name in module["handwritten_declarations"]:
        suffix = name.removeprefix("_root_.")
        matches = [row["name"] for row in owned
                   if row["name"] == suffix or row["name"].endswith("." + suffix)]
        assert len(matches) == 1, (module_name, name, matches)
        handwritten.add(matches[0])
        if matches[0].startswith("_private."):
            private.append(matches[0])
        else:
            public.add(matches[0])
owned_modules = {m['path'].removesuffix('.lean').replace('/', '.') for m in manifest['modules']}
structure_fields = json.loads(path.with_name("structure-fields.json").read_text())
field_names = {field["projection"] for field in structure_fields}
users, live, graph_modules, aliases = reference_graph(rows, handwritten, field_names, roles)
by_name = {row["name"]: row for row in rows}
no_downstream = sorted(public - live)
path.with_name("downstream-use.json").write_text(json.dumps({
    "scope": "Reachability to compiled production users outside the Sturm pair in the selected imported environment. Generated constants are merged with their existing base; self-edges are excluded and real clients through equations remain connected. Production means source role, not runtime or performance. Anonymous examples, automation registration and external client projects are not roots.",
    "public_with_downstream_production_path": sorted(public & live),
    "public_without_downstream_production_path": no_downstream,
    "filtered_users": users, "user_modules": graph_modules, "generated_aliases": aliases}, indent=2, sort_keys=True) + "\n")
paths = []
for name in sorted(private):
    queue = deque([[name]])
    seen = {name}
    found = None
    while queue:
        chain = queue.popleft()
        if len(chain) > 1 and chain[-1] in public:
            found = chain
            break
        for user in users.get(chain[-1], []):
            if user not in seen:
                seen.add(user)
                queue.append(chain + [user])
    assert found is not None, name
    paths.append({"helper": name, "path": found,
                  "public_terminal_has_downstream_production_path": found[-1] in live,
                  "helper_has_downstream_production_path": name in live})
path.with_name("helper-paths.json").write_text(
    json.dumps(paths, indent=2, sort_keys=True) + "\n", encoding="utf-8")

# Keep compiler attribution distinct from handwritten source ownership.
field_purposes = {
    "sign": "Retain the sign provider used by preparation and endpoint guards.",
    "head": "Retain the exact polynomial input binding.",
    "lower": "Expose the excluded lower endpoint.",
    "upper": "Expose the excluded upper endpoint.",
    "squarefree": "Reuse the retained squarefree derivative chain for prepared queries.",
    "endpoints_valid": "Supply the original nonzero-head, order and endpoint-nonvanishing proofs.",
    "last_constant": "Supply the nonzero constant terminal-chain proof.",
    "produced": "Authenticate the exact actual producer chain, rather than an arbitrary accepted chain.",
}
source_fields = []
for field, purpose in field_purposes.items():
    name = "Hex.Sturm.PreparedDomain." + field
    assert name in by_name, name
    source_fields.append({"name": name, "disposition": purpose,
                          "has_downstream_production_path": name in live})
path.with_name("source-fields.json").write_text(json.dumps(source_fields, indent=2, sort_keys=True) + "\n")
assert field_names == {row["name"] for row in source_fields}, "unassessed source-written structure fields"
origins = {'local_base': [], 'foreign_base': [], 'unresolved': []}
for row in rows:
    if row['name'] in handwritten or row['name'] in field_names:
        continue
    category = 'unresolved' if row['base_module'] is None else (
        'local_base' if row['base_module'] in owned_modules else 'foreign_base')
    origins[category].append({key: row[key] for key in
                             ('name', 'module', 'base_declaration', 'base_module')})
path.with_name('generated-origins.json').write_text(json.dumps({
    'scope': 'Compiler constants attributed by Lean to audited modules, excluding the 126 manifest declarations and eight source-written fields assessed separately. Existing raw/private or decoded ancestors distinguish local and foreign bases; unresolved entries remain explicit.',
    'counts': {key: len(value) for key, value in origins.items()},
    'artifacts': origins}, indent=2, sort_keys=True) + '\n')

# Source occurrences supplement, rather than replace, compiled references.
source_files = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=source_root,
                                       text=True).splitlines()
source = {name: (source_root / name).read_text() for name in source_files
          if (source_root / name).is_file()}
no_production = [by_name[name] for name in no_downstream]
occurrences = []
source_hashes = {}
for row in no_production:
    short = row['name'].split('.')[-1]
    pattern = re.compile(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])")
    matches = []
    for name, text in source.items():
        for line_number, line in enumerate(text.splitlines(), 1):
            if pattern.search(line):
                matches.append({'path': name, 'line': line_number, 'text': line.strip()})
                source_hashes[name] = hashlib.sha256((source_root / name).read_bytes()).hexdigest()
    occurrences.append({'name': row['name'], 'matches': matches})
path.with_name('source-occurrences.json').write_text(json.dumps({
    'scope': 'Repository-wide lexical matches in tracked Lean sources for public declarations without a downstream production-reference path in the selected compiled audit. Matches include declarations, comments, anonymous examples, diagnostics, unused simp arguments and coincident names in other namespaces; they are source candidates, not compiled-use or production-liveness claims.',
    'files': source_hashes, 'declarations': occurrences}, indent=2, sort_keys=True) + '\n')
