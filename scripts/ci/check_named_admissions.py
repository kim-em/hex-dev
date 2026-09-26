#!/usr/bin/env python3
"""Audit admissions reachable from the optional RCF and present sign adapters."""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BRIDGE = Path("adapters/HexRealRootsMathlib/TarskiSoundness.lean")
ADMISSION = re.compile(
    r"\b[A-Za-z_]*[sS]orry[A-Za-z_]*\b|\b(?:admit|admitGoal|axiom)\b|^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*constant\b|(?<!\.)\bstop\b(?!\s*:=)",
    re.MULTILINE,
)
DECLARATION = re.compile(
    r"\b(?:theorem|lemma|axiom|def|example|instance|abbrev|opaque|structure)\s+([A-Za-z0-9_]+)"
)
IMPORT = re.compile(r"\bimport\s+(?:all\s+)?(\S+)")
EXTERNAL = {"Batteries", "Mathlib", "Lean", "Init", "Std", "Lake", "Qq", "Verso"}


def code_only(source: str) -> str:
    """Mask Lean comments and strings while retaining source positions."""
    result: list[str] = []
    depth = 0
    quoted = False
    raw = False
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
            if source[i] == "\\" and not raw and i + 1 < len(source):
                result.extend("  ")
                i += 2
            elif source[i] == '"':
                quoted = False
                raw = False
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
        elif source[i] == "'":
            if i > 0 and (source[i - 1].isalnum() or source[i - 1] == "_"):
                result.append(source[i])
                i += 1
                continue
            # Lean character literals include escaped quotes such as '\"'.
            end = i + 1
            if end < len(source) and source[end] == "\\":
                end += 1
            if end + 1 < len(source) and source[end + 1] == "'":
                result.extend(" " * (end + 2 - i))
                i = end + 2
            else:
                result.append(source[i])
                i += 1
        elif source[i] == '"':
            hash_start = i - 1
            while hash_start >= 0 and source[hash_start] == "#":
                hash_start -= 1
            if hash_start < i - 1 and hash_start >= 0 and source[hash_start] == "r" and (
                hash_start == 0 or not source[hash_start - 1].isalnum()
            ):
                delimiter = '"' + source[hash_start + 1:i]
                end = source.find(delimiter, i + 1)
                if end < 0:
                    raise ValueError("unterminated raw string")
                result.extend("\n" if c == "\n" else " " for c in source[i:end + len(delimiter)])
                i = end + len(delimiter)
                continue
            if i > 0 and source[i - 1] == "!":
                # Interpolation can elaborate arbitrary terms. Scan the whole
                # literal, including braces and nested strings, before masking.
                end = interpolation_end(source, i)
                if re.search(r"(?i)sorry|admit|\bstop\b|\baxiom\b", source[i + 1:end]):
                    raise ValueError("admission inside an interpolated string")
                result.extend("\n" if c == "\n" else " " for c in source[i:end + 1])
                i = end + 1
                continue
            quoted = True
            raw = i > 0 and source[i - 1] == "r" and (i == 1 or not source[i - 2].isalnum())
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def interpolation_end(source: str, quote: int) -> int:
    """Find the outer quote, respecting escapes and nested interpolation text."""
    braces = 0
    inner = False
    i = quote + 1
    while i < len(source):
        c = source[i]
        if c == "\\":
            i += 2
            continue
        if c == '"':
            if braces == 0:
                return i
            inner = not inner
        elif not inner:
            if c == "{":
                braces += 1
            elif c == "}" and braces:
                braces -= 1
        i += 1
    raise ValueError("unterminated interpolated string")


def module_file(module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".lean")
    for base in (ROOT, ROOT / "adapters", ROOT / "conformance", ROOT / "bench",
                 ROOT / "experiments", ROOT / "examples"):
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
            if module.split(".", 1)[0] not in EXTERNAL:
                raise ValueError(f"missing local import {module}")
            continue
        paths.add(path.relative_to(ROOT))
        pending.extend(match.group(1) for match in IMPORT.finditer(
            code_only(path.read_text(encoding="utf-8"))))
    return paths


def check() -> None:
    if module_file("HexRCF.RealCoefficients") is None:
        raise ValueError("the optional rcf adapter module is missing")
    roots = ["HexRCF.RealCoefficients"] + [
        "HexSignDetMathlib." + path.stem
        for path in sorted((ROOT / "adapters/HexSignDetMathlib").glob("*.lean"))]
    paths = set().union(*(import_cone(module) for module in roots))
    if BRIDGE not in paths:
        raise ValueError(f"the optional adapter no longer imports {BRIDGE}")
    for relative in sorted(paths):
        source = code_only((ROOT / relative).read_text(encoding="utf-8"))
        admissions = list(ADMISSION.finditer(source))
        if relative == Path("HexRCF/Tactic.lean"):
            # Only these two checks may mention the bridge's admitted axiom.
            approved = {"unless axioms.contains ``sorryAx do",
                        "unless ordinaryAxiom dependency || dependency == ``sorryAx do"}
            admissions = [match for match in admissions if not
                          (match.group().strip() == "sorryAx" and
                           source.splitlines()[source.count("\n", 0, match.start())].strip() in approved)]
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
    print(f"{len(roots)} present adapter import cones: {len(paths)} local modules, only check_rootSum is admitted")


if __name__ == "__main__":
    try:
        check()
    except ValueError as error:
        raise SystemExit(str(error)) from error
