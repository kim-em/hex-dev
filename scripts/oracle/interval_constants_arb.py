#!/usr/bin/env python3
"""Check committed analytic source cuts against independent 256-bit Arb bounds.

This is fixture validation, not soundness evidence or runtime-provider testing.
The exact dyadic endpoints are read from the Lean proof probes, so this check
cannot silently validate a separate copy of the fixture table.
"""
import hashlib
import json
from pathlib import Path
import re

import flint
from flint import arb, fmpq, ctx

ROOT = Path(__file__).resolve().parents[2]


def main():
    ctx.prec = 256
    rows = []
    for path in sorted((ROOT / "bench/HexIntervalMathlib/Constants").glob("Precision*.lean")):
        source = path.read_text()
        matches = re.findall(
            r"theorem (pi|exp)_bounds : \((\d+) / 2 \^ (\d+) : ℝ\) ≤ "
            r"(Real\.pi|Real\.exp 1) ∧\s*"
            r"(Real\.pi|Real\.exp 1) ≤ (\d+) / 2 \^ (\d+)", source)
        if len(matches) != 2:
            raise ValueError(f"{path}: expected both source theorems")
        for name, lower, k, subject, upper_subject, upper, upper_k in matches:
            expected_subject = "Real.pi" if name == "pi" else "Real.exp 1"
            if subject != expected_subject or upper_subject != subject or k != upper_k:
                raise ValueError(f"{path}: mismatched subject or grid")
            k = int(k)
            lo, hi = fmpq(int(lower), 2**k), fmpq(int(upper), 2**k)
            value = arb.pi() if name == "pi" else arb(1).exp()
            # Arb comparison is strict and requires the whole ball to separate.
            if not arb(lo) < value or not value < arb(hi):
                raise ValueError(f"{path}: independent Arb ball is not inside the Lean cuts")
            if hi - lo != fmpq(1, 2**k):
                raise ValueError(f"{path}: wrong fixture width")
            rows.append({"source": str(path.relative_to(ROOT)),
                         "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                         "subject": subject, "precision": k, "lower": str(lo),
                         "upper": str(hi), "arb": str(value), "accepted": True})
    if len(rows) != 6:
        raise ValueError("expected three precision pairs")
    print(json.dumps({"python_flint": flint.__version__, "arb_precision": ctx.prec,
                      "fixtures": rows}, indent=2))


if __name__ == "__main__":
    main()
