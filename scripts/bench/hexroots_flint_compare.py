#!/usr/bin/env python3
"""Informational python-flint comparator for hex-roots complex root isolation.

Times `flint.fmpz_poly.complex_roots()` on the same seed-`0xC0FFEE` dense
integer polynomial ladder that `bench/HexRoots/Bench.lean`'s whole-polynomial
drivers use (`seededPoly`), so the ratio `hex isolateAll?@32 / flint` per degree
in `reports/hexroots-performance.md` is apples-to-apples on the input.

This is an `informational` process-call comparator (SPEC/benchmarking.md
§External comparators): FLINT's `complex_roots` is a multiprecision Arb
ball-arithmetic engine, structurally different from hex-roots' decidable
exact-integer Pellet / Newton-Kantorovich certificates, so it orients but does
not gate Phase 4. All degrees run in one warm process; the process-startup and
per-call floors are measured separately and reported.

Reproduce under a `python-flint >= 0.9.0` virtualenv:

    python3 -m venv /tmp/rootsvenv && /tmp/rootsvenv/bin/pip install python-flint
    /tmp/rootsvenv/bin/python scripts/bench/hexroots_flint_compare.py

Emits one JSON object on stdout: {"prec_bits", "overhead_s", per-degree rows}.
"""
from __future__ import annotations

import json
import statistics
import sys
import time

MASK64 = (1 << 64) - 1


from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def verify_lcg_matches_lean() -> None:
    """Tether this reimplementation to the Lean bench family: the LCG
    multiplier and increment literals must appear in
    bench/HexRoots/Bench.lean, or the comparator is no longer
    apples-to-apples and must fail loudly rather than time a divergent
    input family."""
    src = (REPO_ROOT / "bench" / "HexRoots" / "Bench.lean").read_text()
    for lit in ("6364136223846793005", "1442695040888963407"):
        if lit not in src:
            raise SystemExit(
                f"hexroots_flint_compare: LCG literal {lit} not found in "
                "bench/HexRoots/Bench.lean; the Lean seeded family has "
                "changed and this script must be updated to match"
            )


def lcg_next(s: int) -> int:
    """The LCG step from conformance/HexRoots/EmitFixtures.lean, UInt64 wraparound."""
    return (6364136223846793005 * s + 1442695040888963407) & MASK64


def seeded_coeffs(degree: int) -> list[int]:
    """Replicates `Hex.RootsBench.seededCoeffs`: degree+1 coefficients in
    [-10, 10] (constant term first), leading coefficient forced nonzero."""
    s = 0xC0FFEE
    out: list[int] = []
    for _ in range(degree + 1):
        s = lcg_next(s)
        out.append((s % 21) - 10)
    if out[degree] == 0:
        out[degree] = 1
    return out


def time_call(poly, repeats: int) -> float:
    """Median wall time (seconds) of `poly.complex_roots()` over `repeats`."""
    ts = []
    for _ in range(repeats):
        t0 = time.perf_counter()
        poly.complex_roots()
        ts.append(time.perf_counter() - t0)
    return statistics.median(ts)


def main() -> int:
    verify_lcg_matches_lean()
    import flint
    from flint import ctx, fmpz_poly

    prec_bits = 32  # match hex isolateAll?@32 (half-width 2^-32)
    ctx.prec = prec_bits

    ladder = [int(a) for a in sys.argv[1:]] or [4, 6, 8, 10, 12, 14, 16, 18, 20]

    # Per-call floor: a trivial sub-millisecond input (x^2 - 2).
    trivial = fmpz_poly([-2, 0, 1])
    trivial.complex_roots()  # warm
    overhead_s = time_call(trivial, 200)

    rows = []
    for d in ladder:
        coeffs = seeded_coeffs(d)
        p = fmpz_poly(coeffs)
        p.complex_roots()  # warm
        # Fewer repeats at high degree to keep total time bounded.
        repeats = 50 if d <= 12 else (20 if d <= 16 else 8)
        med = time_call(p, repeats)
        nroots = sum(m for _, m in p.complex_roots())
        rows.append({
            "degree": d,
            "median_s": med,
            "n_roots": nroots,
            "repeats": repeats,
            "coeffs_head": coeffs[:5],
        })

    print(json.dumps({
        "comparator": "python-flint fmpz_poly.complex_roots",
        "python_flint_version": flint.__version__,
        "prec_bits": prec_bits,
        "overhead_s": overhead_s,
        "rows": rows,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
