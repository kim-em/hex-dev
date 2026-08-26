#!/usr/bin/env python3
"""Informational python-flint comparator for hex-roots complex root isolation.

Times `flint.fmpz_poly.complex_roots()` on the historical unregistered
fixed-separation isolation diagnostic ladder (degrees 4–10, including the
canonical fixed `runIsolate` degree 8), plus the canonical degree-12
`runIsolateAll` input, so each ratio in `reports/hex-roots-performance.md`
uses identical polynomials.

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

from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]


def verify_family_matches_lean() -> None:
    """Tether this reimplementation to the Lean fixed-separation family."""
    src = (REPO_ROOT / "bench" / "HexRoots" / "Bench.lean").read_text()
    if "DensePoly.ofCoeffs #[-(2 * (Int.ofNat i) + 1), 2]" not in src:
        raise SystemExit(
            "hexroots_flint_compare: separatedPoly linear factor not found in "
            "bench/HexRoots/Bench.lean; update the comparator family"
        )


def separated_coeffs(degree: int) -> list[int]:
    """Replicate `separatedPoly d = ∏_{i=0}^{d-1} (2X-(2i+1))`."""
    coeffs = [1]
    for i in range(degree):
        factor = [-(2 * i + 1), 2]
        product = [0] * (len(coeffs) + 1)
        for j, a in enumerate(coeffs):
            product[j] += a * factor[0]
            product[j + 1] += a * factor[1]
        coeffs = product
    return coeffs


def time_call(poly, repeats: int) -> float:
    """Median wall time (seconds) of `poly.complex_roots()` over `repeats`."""
    ts = []
    for _ in range(repeats):
        t0 = time.perf_counter()
        poly.complex_roots()
        ts.append(time.perf_counter() - t0)
    return statistics.median(ts)


def main() -> int:
    verify_family_matches_lean()
    import flint
    from flint import ctx, fmpz_poly

    prec_bits = 32
    ctx.prec = prec_bits

    ladder = [int(a) for a in sys.argv[1:]] or [4, 5, 6, 7, 8, 9, 10, 12]

    # Per-call floor: a trivial sub-millisecond input (x^2 - 2).
    trivial = fmpz_poly([-2, 0, 1])
    trivial.complex_roots()  # warm
    overhead_s = time_call(trivial, 200)

    rows = []
    for d in ladder:
        coeffs = separated_coeffs(d)
        p = fmpz_poly(coeffs)
        p.complex_roots()  # warm
        repeats = 50
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
        "family": "fixed-separation-product",
        "python_flint_version": flint.__version__,
        "prec_bits": prec_bits,
        "overhead_s": overhead_s,
        "rows": rows,
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
