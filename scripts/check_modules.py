#!/usr/bin/env python3
"""Require the module header in tracked Lean sources, without invoking Lean.

Lake configuration is a build script. Files in reports/ are retained artifacts,
not current source. The manual (HexManual.lean and HexManual/) is not module
code: its chapters render library docstrings and evaluate library definitions,
which a module could only see through `import all`. EXEMPT_FILES names the
other sources that inspect library internals. Every other tracked .lean
file is checked, including tests, benchmarks, conformance drivers, examples and
experiments.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def first_token(text: str) -> str:
    """Skip whitespace and nested Lean comments, then read the header token."""
    i = 1 if text.startswith("\ufeff") else 0
    while i < len(text):
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                return ""
        else:
            start = i
            while i < len(text) and not text[i].isspace():
                if text.startswith(("--", "/-"), i):
                    break
                i += 1
            return text[start:i]
    return ""


EXEMPT_ROOTS = {"reports", "HexManual", "HexManual.lean"}

# Sources that inspect the libraries themselves, which a module could do only
# through `import all`. Each stays a legacy (non-module) source; nothing imports it.
EXEMPT_FILES = {
    # Environment linters that check imported docstrings.
    "HexECPPTheory/LintTests.lean",
    "HexLatticeEnumTheory/LintTests.lean",
    "HexOrderedFnTheory/LintTests.lean",
    "HexRCF/LintTests.lean",
    "HexSmithTheory/LintTests.lean",
    "HexSparsePolyTheory/LintTests.lean",
    "HexSturmTheory/LintTests.lean",
    "HexTruncatedSeriesTheory/LintTests.lean",
    "conformance/HexPolyFast/Lint.lean",
    "conformance/HexSignDetTheory/Diagnostics/Lint.lean",
    # Kernel-replay audits that walk private declaration bodies and axiom closures.
    "experiments/KernelReplay/AxiomClosureNative.lean",
    "experiments/KernelReplay/AxiomClosureTest.lean",
    "experiments/KernelReplay/ConstructedBaseAudit.lean",
    "experiments/KernelReplay/GuardDependencyControls.lean",
    "experiments/KernelReplay/GuardLiveFrameAudit.lean",
    "experiments/KernelReplay/ProviderHistoryAudit.lean",
    "experiments/KernelReplay/RationalCodecAudit.lean",
    "experiments/KernelReplay/SupportAudit.lean",
    "experiments/KernelReplay/FiniteChecks.lean",  # imports the two audits above
    # Real-closure conformance audits that check library theorems' proof terms.
    "conformance/HexRCF/AlgebraicCellsConformance.lean",
    "conformance/HexRCF/AlgebraicPreparationConformance.lean",
    "conformance/HexRCF/CellCodecProofs.lean",
    "conformance/HexRCF/CellDecisionProofs.lean",
    "conformance/HexRCF/CellDiscoverProofs.lean",
    "conformance/HexRCF/CellExecutionProofs.lean",
    "conformance/HexRCF/GatherCellsConformance.lean",
    "conformance/HexRCF/MaximalCoefficientsKernel.lean",
    "conformance/HexRCF/NamedConstantProofs.lean",
    # Times the `meta` function `quoteTerms` from compiled code, which a module may not call.
    "bench/HexReflect/Bench.lean",
}


def is_source(path: Path) -> bool:
    return (path.suffix == ".lean" and path.name != "lakefile.lean"
            and path.parts[0] not in EXEMPT_ROOTS and path.as_posix() not in EXEMPT_FILES)


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    paths = subprocess.check_output(["git", "ls-files", "-z", "*.lean"], cwd=root)
    sources = [Path(p.decode()) for p in paths.split(b"\0") if p and is_source(Path(p.decode()))]
    offenders = [p for p in sources if first_token((root / p).read_text(encoding="utf-8")) != "module"]
    for path in offenders:
        print(f"{path}: missing module header", file=sys.stderr)
    if offenders:
        print(f"{len(offenders)} non-module Lean sources", file=sys.stderr)
        return 1
    print(f"module headers checked: {len(sources)} Lean sources")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
