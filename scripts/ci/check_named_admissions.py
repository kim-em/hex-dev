#!/usr/bin/env python3
"""Audit all development adapters and sign-determination conformance import cones.

RCF conformance (including intentional negative admission probes) and Sturm
semantic replay conformance remain kernel-checked tests outside this source
scan; the message below reports only the scanned cones.
"""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BRIDGE = Path("adapters/HexRealRootsMathlib/TarskiSoundness.lean")
ADMISSION = re.compile(
    r"\b[A-Za-z_]*[sS]orry[A-Za-z_]*\b|\b(?:admit|admitGoal|axiom)\b|^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*constant\b(?!\s*:)|(?<!\.)\bstop\b(?!\s*:=)",
    re.MULTILINE,
)
IMPORT = re.compile(r"\bimport\s+(?:all\s+)?(\S+)")
EXTERNAL = {"Batteries", "Mathlib", "Lean", "Init", "Std", "Lake", "Qq", "Verso", "TauCeti"}


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
    roots = ["HexRCF.RealCoefficients", "HexSignDetMathlib.SelectedProducerConformance",
             "HexSignDetMathlib.CompletionConformance", "HexSignDetMathlib.QueryHandleConformance",
             "HexSignDetMathlib.TableConformance", "HexSignDetMathlib.ReencodingConformance",
             "HexSignDetMathlib.RootListConformance", "HexSignDetMathlib.RefinementConformance",
             "HexSignDetMathlib.ConvertConformance", "HexRealClosure.BaseTests",
             "HexRealClosure.QAdjoinTests",
             "HexRealClosure.TowerCatalog", "HexRealClosure.TowerTests",
             "HexRealClosure.RootFrame", "HexRealClosure.RootFrameTests",
             "HexRealClosure.LiteralSupport", "HexRealClosure.CodecSupport",
             "HexRealClosure.FrameFormat", "HexRealClosure.FrameFormatTests",
             "HexRealClosureMathlib.BaseTests", "HexRealClosure.BaseCatalogTests",
             "HexRealClosure.BisectionTests", "HexRealClosure.DeflationConformance",
             "HexRealClosure.BisectionFrontierTests", "HexRealClosure.IsolationTests",
             "HexRealClosure.IsolationConformance", "HexRealClosure.RootOrderTests",
             "HexRealClosure.RootFactorsTests", "HexRealClosureMathlib.Bisection",
             "HexRealClosureMathlib.BisectionRoots", "HexRealClosureMathlib.BisectionFrontier",
             "HexRealClosureMathlib.BisectionCounts", "HexRealClosureMathlib.Isolation",
             "HexRealClosureMathlib.BisectionFactor", "HexRealClosureMathlib.IsolationFactor",
             "HexRealClosureMathlib.IsolationRoots", "HexRealClosureMathlib.RootOrder",
             "HexRealClosureMathlib.RootFactors", "HexRealClosureMathlib.Specialize",
             "HexRealClosureMathlib.SpecializePolynomial",
             "HexRealClosureMathlib.SpecializeRegular", "HexRealClosureMathlib.SpecializeQuery", "HexRealClosureMathlib.SpecializeTarski",
             "HexRealClosureMathlib.SpecializeReduction", "HexRealClosureMathlib.SpecializeMoment",
             "HexRealClosureMathlib.SpecializeReplay", "HexRealClosureMathlib.SpecializeSample", "HexRealClosureMathlib.SpecializeSelected", "HexRealClosureMathlib.SpecializeDescriptor",
             "HexRealClosureMathlib.TransportPolynomial", "HexRealClosureMathlib.TransportProduct",
             "HexRealClosureMathlib.TransportArithmetic", "HexRealClosureMathlib.TransportQuery", "HexRealClosureMathlib.TransportTests",
             "HexRealClosureMathlib.TransportRing", "HexRealClosureMathlib.TransportPower",
             "HexRealClosureMathlib.TransportTarski", "HexRealClosureMathlib.TransportClosed",
             "HexRealClosureMathlib.TransportClosedQuery", "HexRealClosureMathlib.TransportClosedReduction",
             "HexRealClosureMathlib.TransportPreparation", "HexRealClosureMathlib.TransportMoment",
             "HexRealClosureMathlib.TransportReplay", "HexRealClosureMathlib.TransportSample", "HexRealClosureMathlib.TransportDescriptor",
             "HexRealClosureMathlib.TransportSelected", "HexRealClosureMathlib.TransportRegular",
             "HexRealClosureMathlib.TransportReduction",
             "HexRealClosureMathlib.SpecializeTests", "HexRealClosureMathlib.Algebraic",
             "HexRealClosureMathlib.AlgebraicClean", "HexRealClosureMathlib.AlgebraicValue",
             "HexRealClosureMathlib.AlgebraicTransport", "HexRealClosureMathlib.AlgebraicYun",
             "HexRealClosureMathlib.AlgebraicReencode",
             "HexRealClosure.AlgebraicReencodeTests",
             "HexRealClosureMathlib.AlgebraicRoots",
             "HexRealClosureMathlib.BaseClean", "HexRealClosureMathlib.AlgebraicTower",
             "HexRealClosureMathlib.Union", "HexRealClosureMathlib.UnionTests",
             "HexRealClosureMathlib.QAdjoin"] + [
        ".".join(path.relative_to(ROOT / "adapters").with_suffix("").parts)
        for path in sorted((ROOT / "adapters").rglob("*.lean"))] + [
        "HexSignDetMathlib." + ".".join(path.relative_to(
            ROOT / "conformance/HexSignDetMathlib").with_suffix("").parts)
        for path in sorted((ROOT / "conformance/HexSignDetMathlib").rglob("*.lean"))]
    # Named roots remain mandatory; the glob also audits unnamed conformance
    # modules, including their own declarations and imported dependencies.
    roots = list(dict.fromkeys(roots))
    for path in sorted((ROOT / "adapters").rglob("*.lean")):
        module = ".".join(path.relative_to(ROOT / "adapters").with_suffix("").parts)
        if module_file(module) != path:
            raise ValueError(f"adapter module {module} is shadowed by another source file")
    for path in sorted((ROOT / "conformance/HexSignDetMathlib").rglob("*.lean")):
        module = "HexSignDetMathlib." + ".".join(path.relative_to(
            ROOT / "conformance/HexSignDetMathlib").with_suffix("").parts)
        if module_file(module) != path:
            raise ValueError(f"conformance module {module} is shadowed by another source file")
    paths = set().union(*(import_cone(module) for module in roots))
    if BRIDGE not in paths:
        raise ValueError(f"the optional adapter no longer imports {BRIDGE}")
    for relative in sorted(paths):
        source = code_only((ROOT / relative).read_text(encoding="utf-8"))
        admissions = list(ADMISSION.finditer(source))
        if relative == Path("HexBareissMathlib/Tactic.lean"):
            # This Lean elaborator API prevents failed elaboration from inserting
            # an admitted term; it is the opposite of an admission.
            admissions = [match for match in admissions if not (
                match.group() == "withoutErrToSorry" and
                "Term.withoutErrToSorry (elabArgument" in
                source.splitlines()[source.count("\n", 0, match.start())]
            )]
        if admissions:
            line = source.count("\n", 0, admissions[0].start()) + 1
            raise ValueError(f"unapproved admission in {relative}:{line}")
    print(f"{len(roots)} scanned adapter/conformance import cones: "
          f"{len(paths)} local modules, no admissions in these cones")


if __name__ == "__main__":
    try:
        check()
    except ValueError as error:
        raise SystemExit(str(error)) from error
