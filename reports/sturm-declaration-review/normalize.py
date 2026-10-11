"""Normalize the compiled inventory before comparing its committed SHA-256."""

import hashlib
import json
import re
import subprocess
from collections import deque
from pathlib import Path

path = Path(__file__).with_name("declaration-use.json")
rows = json.loads(path.read_text(encoding="utf-8"))
def user_category(module):
    parts = module.split(".")
    if module.startswith(("HexManual", "RealClosureConsumer")) or any(
        part in {"Tests", "Conformance", "Fixtures", "Diagnostics", "ProofProbe", "DepthThree"}
        or part.endswith(("Tests", "Conformance", "Examples", "Checks"))
        or "Bench" in part for part in parts
    ):
        return "tests/conformance/manual"
    if parts[0] in {"HexSturm", "HexSturmMathlib"}:
        return "Sturm production"
    if parts[0].startswith("Hex"):
        return "other Hex production"
    return "other imported module"


rows.sort(key=lambda row: (row["module"], row["name"]))
for row in rows:
    row["users_by_category"] = {}
    for user, module in row["user_modules"].items():
        category = user_category(module)
        row["users_by_category"].setdefault(category, []).append(user)
    for users in row["users_by_category"].values():
        users.sort()
for row in rows:
    row["users"].sort()
    row["axioms"].sort()
path.write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")

# Trace every private production helper to a handwritten declaration, allowing
# compiler-generated intermediate users. This is scoped to the imported audit.
manifest = json.loads(path.with_name("manifest.json").read_text(encoding="utf-8"))
handwritten = set()
private = []
public = set()
source_root = Path(__file__).resolve().parents[2]
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
users = {row["name"]: row["users"] for row in rows}
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
    paths.append({"helper": name, "path": found})
path.with_name("helper-paths.json").write_text(
    json.dumps(paths, indent=2, sort_keys=True) + "\n", encoding="utf-8")

# Keep compiler attribution distinct from handwritten source ownership.
owned_modules = {m['path'].removesuffix('.lean').replace('/', '.') for m in manifest['modules']}
origins = {'local_base': [], 'foreign_base': [], 'unresolved': []}
for row in rows:
    if row['name'] in handwritten:
        continue
    category = 'unresolved' if row['base_module'] is None else (
        'local_base' if row['base_module'] in owned_modules else 'foreign_base')
    origins[category].append({key: row[key] for key in
                             ('name', 'module', 'base_declaration', 'base_module')})
path.with_name('generated-origins.json').write_text(json.dumps({
    'scope': 'Compiler artifacts attributed by Lean to audited modules. Ancestor lookup is partial; unresolved origins are explicit. Handwritten source ownership comes from the manifest.',
    'counts': {key: len(value) for key, value in origins.items()},
    'artifacts': origins}, indent=2, sort_keys=True) + '\n')

# Source occurrences supplement, rather than replace, compiled references.
source_files = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=source_root,
                                       text=True).splitlines()
source = {name: (source_root / name).read_text() for name in source_files
          if (source_root / name).is_file()}
no_production = [row for row in rows if row['name'] in public and not any(
    row['users_by_category'].get(category) for category in
    ('Sturm production', 'other Hex production'))]
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
                source_hashes[name] = hashlib.sha256(text.encode()).hexdigest()
    occurrences.append({'name': row['name'], 'matches': matches})
path.with_name('source-occurrences.json').write_text(json.dumps({
    'scope': 'Repository-wide lexical matches in tracked Lean sources for public declarations without production users in the selected compiled audit. Matches include declarations, comments, anonymous examples, diagnostics, unused simp arguments and coincident names in other namespaces; they are source candidates, not compiled-use or production-liveness claims.',
    'files': source_hashes, 'declarations': occurrences}, indent=2, sort_keys=True) + '\n')
