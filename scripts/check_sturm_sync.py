#!/usr/bin/env python3
"""Check that the Sturm development agrees with a Mathlib checkout.

Usage: python3 scripts/check_sturm_sync.py /path/to/mathlib
Module paths, the parser namespace, and Verso name markup may differ.
"""

import argparse
import difflib
import re
from pathlib import Path

MODULES = {
    "HexRealRootsMathlib.SturmChainDefs": "Mathlib.Analysis.Polynomial.Sturm.Defs",
    "HexRealRootsMathlib.SturmTheorem": "Mathlib.Analysis.Polynomial.Sturm.Basic",
    "HexRealRootsMathlib.SturmCertificate": "Mathlib.Analysis.Polynomial.Sturm.Certificate",
    "HexPolyZMathlib.PolyParse": "Mathlib.Tactic.RealRootCount.Parse",
    "HexRealRootsMathlib.RealRootCount": "Mathlib.Tactic.RealRootCount",
    "HexRealRootsMathlib.RealRootCountTests": "MathlibTest.RealRootCount",
    "HexRealRootsMathlib.SturmTests": "MathlibTest.Sturm",
}


# Mathlib master has moved the Sign modules since Hex's pinned Mathlib release.
RENAMES = MODULES | {
    "HexRealRootsMathlib.Sign": "Mathlib.Topology.Instances.Sign.Connected",
    "Mathlib.Data.Sign.Basic": "Mathlib.Basic.Sign.Basic",
}


def mathlib_text(text: str) -> str:
    for source, target in sorted(RENAMES.items(), key=lambda item: -len(item[0])):
        text = text.replace(source, target)
    return re.sub(r"\{name\}(`[^`]+`)", r"\1", text)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mathlib", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    different = False
    for source, target in MODULES.items():
        src = root / (source.replace(".", "/") + ".lean")
        dst = args.mathlib / (target.replace(".", "/") + ".lean")
        expected = mathlib_text(src.read_text()).splitlines(keepends=True)
        actual = dst.read_text().splitlines(keepends=True)
        diff = list(difflib.unified_diff(expected, actual, fromfile=str(src), tofile=str(dst)))
        if diff:
            different = True
            print("".join(diff), end="")
    if different:
        raise SystemExit(1)
    print(f"All {len(MODULES)} Sturm library and test modules agree with Mathlib.")


if __name__ == "__main__":
    main()
