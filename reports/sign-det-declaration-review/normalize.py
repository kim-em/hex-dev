"""Normalize the compiled inventory before comparing its committed SHA-256."""

import json
import re
from collections import deque
from pathlib import Path

path = Path(__file__).with_name("declaration-use.json")
rows = json.loads(path.read_text(encoding="utf-8"))
rows.sort(key=lambda row: (row["module"], row["name"]))
for row in rows:
    row["users"].sort()
    row["axioms"].sort()
path.write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n", encoding="utf-8")

# Trace every private production helper to a handwritten declaration, allowing
# compiler-generated intermediate users. This is scoped to the imported audit.
manifest = json.loads(path.with_name("manifest.json").read_text(encoding="utf-8"))
handwritten = set()
private = []
source_root = Path(__file__).resolve().parents[2]
for module in manifest["modules"]:
    module_name = module["path"].removesuffix(".lean").replace("/", ".")
    owned = [row for row in rows if row["module"] == module_name]
    private_names = set(re.findall(
        r"(?m)^private\s+(?:theorem|def|opaque)\s+([\w.']+)",
        (source_root / module["path"]).read_text(encoding="utf-8"),
    ))
    for name in module["handwritten_declarations"]:
        suffix = name.removeprefix("_root_.")
        matches = [row["name"] for row in owned
                   if row["name"] == suffix or row["name"].endswith("." + suffix)]
        assert len(matches) == 1, (module_name, name, matches)
        handwritten.add(matches[0])
        if name in private_names:
            private.append(matches[0])
users = {row["name"]: row["users"] for row in rows}
paths = []
for name in sorted(private):
    queue = deque([[name]])
    seen = {name}
    found = None
    while queue:
        chain = queue.popleft()
        if len(chain) > 1 and chain[-1] in handwritten:
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
