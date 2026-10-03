#!/usr/bin/env python3
"""Print the source-bound real-closure package inventory; never stage or publish."""

from functools import cache
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

import yaml

from release.check_trust_surface import code_without_comments_and_strings

ROOT = Path(__file__).resolve().parents[1]
FAMILY = ["HexOrderedFn", "HexOrderedFnMathlib", "HexSturm", "HexSturmMathlib",
          "HexSignDet", "HexSignDetMathlib", "HexRealClosure", "HexRealClosureMathlib"]
ADAPTERS = ["HexRealRootsMathlib", "HexSturmMathlib", "HexSignDetMathlib",
            "HexRealClosureMathlib", "HexRCF"]
IMPORT = re.compile(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([\w. \t]+)$", re.M)
SOURCE_INPUTS: set[Path] = set()


def module_name(path: Path) -> str:
    relative = path.relative_to(ROOT)
    if relative.parts[0] == "adapters":
        relative = Path(*relative.parts[1:])
    return ".".join(relative.with_suffix("").parts)


@cache
def imports(module: str) -> tuple[str, ...]:
    relative = Path(*module.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "adapters"):
        path = base / relative
        if path.is_file():
            SOURCE_INPUTS.add(path)
            return tuple(module for line in IMPORT.findall(
                code_without_comments_and_strings(path.read_text())) for module in line.split())
    return ()


def import_closure(modules: list[str], libraries: dict) -> tuple[list[str], list[str]]:
    seen = set()
    pending = list(modules)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(imports(module))
    roots = {module.split(".")[0] for module in seen}
    external = roots - libraries.keys() - {"Hex", "Init", "Lean", "Std"}
    return sorted(roots & libraries.keys()), sorted(external)


def main() -> None:
    SOURCE_INPUTS.update(ROOT / path for path in
                         ["libraries.yml", "scripts/release/released.yml", "lake-manifest.json", "lean-toolchain"])
    libraries = yaml.safe_load((ROOT / "libraries.yml").read_text())["libraries"]
    released = yaml.safe_load((ROOT / "scripts/release/released.yml").read_text())["repos"]
    published = {entry["lib"]: entry["repo"] for entry in released if "lib" in entry}
    selected = set(FAMILY + ADAPTERS + libraries["HexRCF"]["adapter_deps"] +
                   ["HexPolyFp", "HexRealFormula", "HexRealFormulaMathlib", "HexReflect", "HexReflectMathlib"])

    def declared_closure(name: str) -> list[str]:
        seen = set()
        pending = list(libraries[name]["deps"])
        while pending:
            dependency = pending.pop()
            if dependency not in seen:
                seen.add(dependency)
                pending.extend(libraries[dependency]["deps"])
        return sorted(seen)

    for name in list(selected):
        selected.update(declared_closure(name))
    records = []
    for name in sorted(selected):
        info = libraries[name]
        public, external = import_closure([name], libraries)
        adapter_files = sorted((ROOT / "adapters" / name).rglob("*.lean"))
        semantic, semantic_external = import_closure(
            [name] + [module_name(path) for path in adapter_files if not path.stem.endswith("Tests")],
            libraries)
        records.append({
            "library": name, "phase": info["done_through"], "mathlib": info["mathlib"],
            "publishedRepo": published.get(name), "directHexDependencies": info["deps"],
            "declaredUnpublishedHexClosure": [dep for dep in declared_closure(name) if dep not in published],
            "publicImportUnpublishedHexClosure": [dep for dep in public if dep != name and dep not in published],
            "semanticImportUnpublishedHexClosure": [dep for dep in semantic if dep != name and dep not in published],
            "publicImportExternalRoots": external, "semanticImportExternalRoots": semantic_external,
        })
    adapters = []
    for name in ADAPTERS:
        paths = sorted((ROOT / "adapters" / name).rglob("*.lean"))
        roots = {module.split(".")[0] for path in paths for module in imports(module_name(path))}
        adapters.append({"namespace": name,
                         "target": "HexRCFRealFormula + HexRCFRealCoefficients" if name == "HexRCF" else "HexQuerySemantics",
                         "directImportRoots": sorted(roots - {name}),
                         "modules": [str(path.relative_to(ROOT)) for path in paths]})
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    digest = sha256()
    for path in sorted(SOURCE_INPUTS):
        digest.update(str(path.relative_to(ROOT)).encode() + b"\0" + path.read_bytes() + b"\0")
    result = {
        "sourceBaseRevision": subprocess.check_output(
            ["git", "merge-base", "origin/main", "HEAD"], cwd=ROOT, text=True).strip(),
        "sourceInputSHA256": digest.hexdigest(),
        "scope": "Preparation snapshot; declared dependency closures differ from current public and development semantic import closures. Not staged split-package validation.",
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "externalPins": [{key: package[key] for key in ("name", "url", "rev")} for package in manifest["packages"]
                         if package["name"] in {"mathlib", "TauCeti", "verso"}],
        "libraries": records, "adapters": adapters,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
