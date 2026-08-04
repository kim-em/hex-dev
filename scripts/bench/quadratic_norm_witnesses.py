#!/usr/bin/env python3
"""Off-corpus witnesses for the iterated-quadratic-norm certificate (issue #9133).

Every polynomial of this class the committed corpus contains is a
Swinnerton-Dyer row: consecutive prime radicands, small integer translation, and
`hoeij_S7`--`hoeij_S9` are `SD_7`--`SD_9` vendored from a second source. So the
corpus cannot by itself show that the recogniser keys on the mathematics rather
than on that shape. These witnesses do: composite radicands, negative radicands,
non-monotone orders, large translations, radicands sharing prime support, and
the dependent and perturbed cases that must be refused.

Each case is emitted as an ascending integer coefficient list, built here by an
independent Python implementation of the iterated norm, and fed to
``hexbz_factor_service --entry quadraticNormCertificate``. Agreement is a
differential check of the Lean implementation against this one; the `expect`
field is what the mathematics says the answer must be.

Run::

    lake build hexbz_factor_service
    python3 scripts/bench/quadratic_norm_witnesses.py \\
        --output reports/bench-results/hexbz-quadratic-norm-witnesses.json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"


def quad_norm(g: list[int], d: int) -> list[int]:
    """`N_d(g)` in `Z[t]/(t^2 - d)`, independently of the Lean implementation."""
    n = len(g)
    h = [(gi, 0) for gi in g]
    for i in range(n - 1):
        for j in range(n - 2, i - 1, -1):
            a, b = h[j + 1]
            ha, hb = h[j]
            h[j] = (ha - b * d, hb - a)
    out = [0] * (2 * n - 1)
    for i, (ai, bi) in enumerate(h):
        for j, (aj, bj) in enumerate(h):
            out[i + j] += ai * aj - bi * bj * d
    return out


def iterated_norm(c: int, ds: list[int]) -> list[int]:
    g = [-c, 1]
    for d in ds:
        g = quad_norm(g, d)
    return g


def independent(ds: list[int]) -> bool:
    for mask in range(1, 1 << len(ds)):
        prod = 1
        for i, d in enumerate(ds):
            if mask >> i & 1:
                prod *= d
        if prod >= 0 and isqrt(prod) ** 2 == prod:
            return False
    return True


# (name, translation, radicands, note). `expect` is derived: a case is certified
# exactly when its radicands are independent square classes.
CASES = [
    ("gaussian_sqrt2", 0, [-1, 2], "a negative radicand: roots +-i +- sqrt 2"),
    ("negative_pair", 3, [-2, -5], "both radicands negative, translated"),
    ("composite_coprime", 7, [6, 10, 21],
     "composite radicands with shared prime support, still independent"),
    ("descending_primes", 0, [13, 11, 7, 5, 3, 2],
     "SD_6's radicands in the opposite order: same field, other tower"),
    ("mixed_signs", -11, [-1, 6, 35, 22],
     "mixed signs and composites, large negative translation"),
    ("large_translation", 1000003, [2, 3, 5],
     "translation far outside the corpus range"),
    ("nonconsecutive_primes", -2, [3, 17, 101, 1009],
     "sparse primes, degree 16"),
    ("squarefull_radicands", 0, [12, 20, 45],
     "radicands with square factors: 12 = 4*3, 20 = 4*5, 45 = 9*5"),
    ("deg1024", 3, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29],
     "degree 1024, an order of magnitude past the corpus"),
    ("dependent_product", 0, [2, 3, 6],
     "2 * 3 * 6 = 36: dependent, must be refused"),
    ("dependent_pair", 5, [7, 28],
     "7 * 28 = 196: dependent, must be refused"),
    ("dependent_squarefull", 0, [2, 3, 5, 30],
     "2 * 3 * 5 * 30 = 900: dependent, must be refused"),
    ("repeated_radicand", 0, [2, 3, 2], "a repeated radicand is dependent"),
    ("zero_radicand", 0, [2, 0], "a zero radicand is dependent"),
]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args(argv[1:])

    if not SERVICE.exists():
        raise SystemExit(f"missing {SERVICE}; run `lake build hexbz_factor_service`")

    cases = []
    for name, c, ds, note in CASES:
        coeffs = iterated_norm(c, ds)
        cases.append({
            "name": name, "translation": c, "radicands": ds, "note": note,
            "degree": len(coeffs) - 1, "expect": independent(ds),
            "coeffs": coeffs,
        })

    # One perturbed case: a certified polynomial with one coefficient moved by 1
    # must be refused, since the identification is an exact equality.
    base = next(c for c in cases if c["name"] == "descending_primes")
    perturbed = list(base["coeffs"])
    perturbed[len(perturbed) // 2] += 1
    cases.append({
        "name": "perturbed_sd6", "translation": None, "radicands": None,
        "note": "SD_6 with one middle coefficient moved by 1, must be refused",
        "degree": len(perturbed) - 1, "expect": False, "coeffs": perturbed,
    })

    payload = "".join(json.dumps({"coeffs": c["coeffs"]}) + "\n" for c in cases)
    completed = subprocess.run(
        [str(SERVICE), "--entry", "quadraticNormCertificate"], input=payload,
        text=True, capture_output=True, check=True)
    replies = [json.loads(line)["result"]
               for line in completed.stdout.splitlines() if line.strip()]

    rows, failures = [], []
    for case, reply in zip(cases, replies):
        got = bool(reply.get("certified"))
        nanos = sum(reply[s]["nanos"] for s in
                    ("recovery", "independence", "construction", "equality")
                    if s in reply)
        row = {
            "name": case["name"], "degree": case["degree"],
            "note": case["note"], "expect": case["expect"], "certified": got,
            "declared_translation": case["translation"],
            "declared_radicands": case["radicands"],
            "recovered_translation": reply.get("translation"),
            "recovered_radicands": reply.get("radicands"),
            "certificate_nanos": nanos,
        }
        # A certified case must recover the same square classes it was built
        # from, up to order; the radicands themselves are only determined up to
        # the tower order.
        if got and sorted(reply.get("radicands") or []) != sorted(case["radicands"]):
            failures.append(f"{case['name']}: recovered "
                            f"{reply.get('radicands')} != {case['radicands']}")
        if got != case["expect"]:
            failures.append(f"{case['name']}: certified={got}, "
                            f"expected {case['expect']}")
        rows.append(row)
        print(f"  {case['name']:24s} deg={case['degree']:5d} "
              f"expect={str(case['expect']):5s} got={str(got):5s} "
              f"{nanos / 1e3:9.1f} us", file=sys.stderr)

    record = {"schema": "hexbz-quadratic-norm-witnesses/1", "cases": rows,
              "failures": failures}
    if args.output:
        Path(args.output).write_text(
            json.dumps(record, indent=1, sort_keys=True) + "\n")
    if failures:
        print("\nFAILURES:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(f"\n{len(rows)} witnesses agree with the mathematics.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
