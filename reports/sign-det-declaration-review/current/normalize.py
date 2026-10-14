"""Reproduce the companion's reference graph using the existing audit helpers."""
import argparse
import json
import re
import subprocess
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "reports/sturm-declaration-review"))
from audit_tools import SourceIndex, reference_graph
from scripts.ci.check_benches_mathlib_free import _parse_imports


def require(condition, message):
    if not condition:
        raise ValueError(message)


def derive(directory):
    rows = json.loads((directory / "declaration-use.json").read_text())
    fields = json.loads((directory / "structure-fields.json").read_text())
    manifest = json.loads((BASE.parent / "manifest.json").read_text())
    imports = json.loads((directory / "audit-imports.json").read_text())
    index = SourceIndex()
    roles = {module: index.resolve(module) for module in sorted(imports)}
    owned = {m["path"].removesuffix(".lean").replace("/", ".") for m in manifest["modules"]}
    handwritten = set()
    for module in manifest["modules"]:
        name = module["path"].removesuffix(".lean").replace("/", ".")
        for declaration in module["handwritten_declarations"]:
            suffix = declaration.removeprefix("_root_.")
            matches = [row["name"] for row in rows if row["module"] == name and
                       (row["name"] == suffix or row["name"].endswith("." + suffix))]
            require(len(matches) == 1, (name, declaration, matches))
            handwritten.add(matches[0])
    # The borrowed graph uses this category for its selected module roots.
    # Substitute the companion roots without changing the archival helper.
    graph_roles = {module: dict(role) for module, role in roles.items()}
    for module in owned:
        graph_roles[module]["category"] = "Sturm production"
    for module, role in graph_roles.items():
        if module not in owned and role["category"] == "Sturm production":
            role["category"] = "other Hex production"
    users, live, modules, aliases = reference_graph(
        rows, handwritten, {f["projection"] for f in fields}, graph_roles)
    for module in owned:
        roles[module]["category"] = "SignDet companion production"
    private = {name for name in handwritten if name.startswith("_private.")}
    paths = []
    for name in sorted(private):
        queue, seen, found = deque([[name]]), {name}, None
        while queue:
            chain = queue.popleft()
            if len(chain) > 1 and chain[-1] in handwritten - private:
                found = chain
                break
            for user in users.get(chain[-1], []):
                if user not in seen:
                    seen.add(user)
                    queue.append(chain + [user])
        require(found is not None, "private helper has no public path: " + name)
        paths.append({"helper": name, "path": found})
    public = handwritten - private
    downstream = {
        "scope": "Compiler-alias merged paths in the current imported environment; evidence and external packages are not production roots. Anonymous examples, automation registration and external client projects are outside this model. Alias targets outside selected modules are not inventoried.",
        "public_with_downstream_production_path": sorted(public & live),
        "public_without_downstream_production_path": sorted(public - live),
        "filtered_users": users, "user_modules": modules, "generated_aliases": aliases,
    }
    production = {}
    for file in subprocess.check_output(["git", "ls-files", "*.lean"], cwd=ROOT, text=True).splitlines():
        path = ROOT / file
        for source in index.project:
            if path.is_relative_to(source):
                name = ".".join(path.relative_to(source).with_suffix("").parts)
                if not name.startswith("Hex"):
                    continue
                role = index.resolve(name)
                if role["path"] == file and role["category"] in {
                        "Sturm production", "SignDet companion production",
                        "other Hex production", "other root-package production"}:
                    production[name] = file
    cache = {}

    def reaches(name, visiting=frozenset()):
        if name.split(".")[0] in {"HexSignDet", "HexSignDetMathlib"}:
            return True
        if name in cache:
            return cache[name]
        if name in visiting:
            return False
        role = index.resolve(name)
        cache[name] = role["path"] is not None and any(
            reaches(parent, visiting | {name}) for parent in _parse_imports(ROOT / role["path"]))
        return cache[name]

    required = {name: path for name, path in production.items() if reaches(name)}
    missing = {name: path for name, path in required.items() if name not in roles}
    require(not missing, ("missing production imports", missing))
    coverage = {
        "scope": "All tracked Hex production modules resolved with the existing source-role index and import parser, following transitive imports to either SignDet module root. Evidence modules and external projects are outside this production coverage model.",
        "production_modules": len(production), "required_modules": len(required),
        "covered_modules": dict(sorted(required.items())), "missing_modules": missing,
    }
    rows.sort(key=lambda row: (row["module"], row["name"]))
    for row in rows:
        row["users"].sort()
        row["axioms"].sort()
    fields.sort(key=lambda row: (row["structure"], row["field"]))
    return {"declaration-use.json": rows, "structure-fields.json": fields,
            "module-roles.json": roles, "downstream-use.json": downstream,
            "helper-paths.json": paths, "production-import-coverage.json": coverage}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=BASE)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in derive(args.directory).items():
        expected = json.dumps(value, indent=2, sort_keys=True) + "\n"
        if args.check:
            require((args.directory / name).read_text() == expected, "derived artifact differs: " + name)
        else:
            (args.directory / name).write_text(expected)
    print("Companion reference graph, helper paths and production coverage verified.")


if __name__ == "__main__":
    main()
