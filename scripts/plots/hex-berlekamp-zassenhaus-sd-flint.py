#!/usr/bin/env python3
"""Time python-flint on the Swinnerton-Dyer tier-crossover ladders.

Produces the informational FLINT curve for
`scripts/plots/hex-berlekamp-zassenhaus-sd.py`. FLINT is *informational
only* at the BZ level (see the library SPEC §External comparators); the
gating comparator is the verified Isabelle extraction, whose rungs are
lean-bench registrations (`runIsabelleAdvSwinnertonDyer*Checksum`).

The inputs are recomputed from sympy `minimal_polynomial` — the same
source the Lean bench pins its literals from — and cross-checked against
the constant coefficients that `bench/HexBerlekampZassenhaus/Bench.lean`
pins with `#guard`, so the two input sets cannot drift apart silently.

Usage: hex-berlekamp-zassenhaus-sd-flint.py OUTPUT.json
"""

from __future__ import annotations

import json
import subprocess
import sys
import time
from pathlib import Path

import sympy
from flint import fmpz_poly
from sympy import Poly, expand, minimal_polynomial, sqrt, symbols

x = symbols("x")
PRIMES = [2, 3, 5, 7, 11]

# Constant coefficients pinned by #guard in bench/HexBerlekampZassenhaus/Bench.lean.
PINS = {
    ("pair", 2): -8,
    ("pair", 3): -40896,
    ("pair", 4): 107460921600,
    ("pair", 5): 11101827931906700692775396966400,
    ("blocks", 3): -1039528705604601600,
    ("blocks", 4): -30893529063662744356454400,
}


def sd(k: int) -> Poly:
    return Poly(minimal_polynomial(sum(sqrt(p) for p in PRIMES[:k]), x), x)


def shift(p: Poly, a: int) -> Poly:
    return Poly(expand(p.as_expr().subs(x, x + a)), x)


def coeffs_asc(p: Poly) -> list[int]:
    return [int(c) for c in reversed(p.all_coeffs())]


def build_families() -> dict[str, dict[int, list[int]]]:
    ladder = {k: sd(k) for k in range(1, 6)}
    pair = {k: Poly(expand(ladder[k].as_expr() * shift(ladder[k], 1).as_expr()), x)
            for k in range(1, 6)}
    sd4 = ladder[4]
    blocks = {}
    for m in range(1, 5):
        prod = Poly(1, x)
        for i in range(m):
            prod = Poly(expand(prod.as_expr() * shift(sd4, i).as_expr()), x)
        blocks[m] = prod
    for (fam, param), pin in PINS.items():
        p = {"pair": pair, "blocks": blocks}[fam][param]
        got = int(p.all_coeffs()[-1])
        assert got == pin, f"{fam}[{param}] constant coefficient {got} != Lean pin {pin}"
    return {
        "ladder": {k: coeffs_asc(p) for k, p in ladder.items()},
        "pair": {k: coeffs_asc(p) for k, p in pair.items()},
        "blocks": {m: coeffs_asc(p) for m, p in blocks.items()},
    }


def time_flint(coeffs: list[int], min_total: float = 0.5) -> tuple[float, int]:
    """Median-of-3 per-call seconds (auto-tuned inner repeats), factor count."""
    p = fmpz_poly(coeffs)
    _, fac = p.factor()
    nfac = sum(m for _, m in fac)
    reps = 1
    while True:
        t0 = time.perf_counter()
        for _ in range(reps):
            p.factor()
        dt = time.perf_counter() - t0
        if dt >= min_total or reps >= 1 << 20:
            break
        reps *= 2
    samples = []
    for _ in range(3):
        t0 = time.perf_counter()
        for _ in range(reps):
            p.factor()
        samples.append((time.perf_counter() - t0) / reps)
    samples.sort()
    return samples[1], nfac


def main() -> int:
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    if out is None:
        print(__doc__, file=sys.stderr)
        return 2
    families = build_families()
    results = []
    for fam, rungs in families.items():
        for param, coeffs in sorted(rungs.items()):
            median_s, nfac = time_flint(coeffs)
            results.append({
                "family": fam,
                "param": param,
                "degree": len(coeffs) - 1,
                "median_seconds_per_call": median_s,
                "factor_count_with_multiplicity": nfac,
            })
            print(f"{fam:7s} {param} | deg {len(coeffs)-1:3d} | {median_s*1e3:10.3f} ms | {nfac} factors")
    git_commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True
    ).stdout.strip()
    out.write_text(json.dumps({
        "generator": "scripts/plots/hex-berlekamp-zassenhaus-sd-flint.py",
        "engine": f"python-flint (fmpz_poly.factor), sympy {sympy.__version__} inputs",
        "git_commit": git_commit,
        "timestamp_unix": int(time.time()),
        "results": results,
    }, indent=1) + "\n")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
