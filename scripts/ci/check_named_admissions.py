#!/usr/bin/env python3
"""Keep optional root/sign adapters' sole source admission at #10389's theorem."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from check_dag import IMPORT_ALL_RE, parse_imports  # noqa: E402

BRIDGE = Path("adapters/HexRealRootsMathlib/TarskiSoundness.lean")
ROOT_MODULES = (
    "HexRCF.RealCoefficients",
    "HexSignDetMathlib.RootProducer",
    "HexSignDetMathlib.SelectedRoot",
)
ADMISSION = re.compile(r"\b(?:sorry|admit)\b")
DECLARATION = re.compile(r"\b(?:theorem|lemma|axiom|def|example)\s+([A-Za-z0-9_]+)")


def code_only(source: str) -> str:
    """Mask Lean comments and strings while retaining source positions."""
    result: list[str] = []
    depth = 0
    quoted = False
    i = 0
    while i < len(source):
        pair = source[i : i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\" and i + 1 < len(source):
                result.extend("  ")
                i += 2
            elif source[i] == '"':
                quoted = False
                result.append(" ")
                i += 1
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                result.extend(" " * (len(source) - i))
                break
            result.extend(" " * (end - i))
            i = end
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif source[i] == '"':
            quoted = True
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def module_file(module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "adapters", ROOT / "conformance", ROOT / "bench"):
        candidate = base / relative
        if candidate.is_file():
            return candidate
    return None


def import_cone(start: str) -> set[Path]:
    pending = [start]
    seen: set[str] = set()
    paths: set[Path] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_file(module)
        if path is None:
            if module == "Hex" or module.startswith("Hex.") or module.startswith("HexRCF."):
                raise ValueError(f"missing local import {module}")
            continue
        paths.add(path.relative_to(ROOT))
        pending.extend(parse_imports(path))
        for line in path.read_text(encoding="utf-8").splitlines():
            if match := IMPORT_ALL_RE.match(line.split("--", 1)[0]):
                pending.append(match.group(1))
    return paths


def check() -> None:
    roots = [module for module in ROOT_MODULES if module_file(module) is not None]
    if "HexRCF.RealCoefficients" not in roots:
        raise ValueError("the optional rcf adapter module is missing")
    paths = set().union(*(import_cone(module) for module in roots))
    if BRIDGE not in paths:
        raise ValueError(f"the optional adapter no longer imports {BRIDGE}")
    for relative in sorted(paths):
        source = code_only((ROOT / relative).read_text(encoding="utf-8"))
        admissions = list(ADMISSION.finditer(source))
        if relative != BRIDGE:
            if admissions:
                line = source.count("\n", 0, admissions[0].start()) + 1
                raise ValueError(f"unapproved admission in {relative}:{line}")
            continue
        if len(admissions) != 1 or admissions[0].group() != "sorry":
            raise ValueError(f"expected one check_rootSum sorry in {BRIDGE}, got {len(admissions)}")
        declarations = list(DECLARATION.finditer(source, 0, admissions[0].start()))
        if not declarations or declarations[-1].group(1) != "check_rootSum":
            raise ValueError(f"the {BRIDGE} sorry is not in check_rootSum")
        if not re.search(r":=\s*by\s*$", source[declarations[-1].end() : admissions[0].start()]):
            raise ValueError(f"the {BRIDGE} admission is no longer the direct theorem body")
    print(f"{len(roots)} adapter import cones: {len(paths)} local modules, only check_rootSum is admitted")


if __name__ == "__main__":
    try:
        check()
    except ValueError as error:
        raise SystemExit(str(error)) from error
