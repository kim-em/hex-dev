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

A second, randomized pass puts the *theorem* to the production factorizer:
for each random translation and radicand tuple it compares three verdicts --
the arithmetic independence test, the certificate, and whether
``Hex.ZPoly.factorize`` returns a single factor of full degree. All three must
agree, in both directions. A certified-but-reducible case would refute the
theorem; an independent-but-reducible case would refute it too; and a
dependent-but-irreducible case would show the independence hypothesis is
stronger than it needs to be. The seed is fixed so the run is reproducible.

Run::

    lake build hexbz_factor_service
    python3 scripts/bench/quadratic_norm_witnesses.py \\
        --output reports/bench-results/hexbz-quadratic-norm-witnesses.json
"""

from __future__ import annotations

import argparse
import json
import random
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


# Radicands the random pass draws from: negative, prime, composite, and
# square-full, so dependent tuples arise often rather than by accident.
RADICAND_POOL = (-7, -6, -5, -3, -2, -1, 2, 3, 5, 6, 7, 10, 11, 12, 13, 14, 15,
                 20, 21, 22, 30, 45)


def random_pass(count: int, seed: int) -> "tuple[list, list[str]]":
    """Independence, certificate, and production factorization must agree."""
    rng = random.Random(seed)
    cases = [(rng.randint(-4, 4),
              [rng.choice(RADICAND_POOL) for _ in range(rng.randint(1, 4))])
             for _ in range(count)]
    payload = "".join(json.dumps({"coeffs": iterated_norm(c, ds)}) + "\n"
                      for c, ds in cases)
    certified = [json.loads(line)["result"] for line in subprocess.run(
        [str(SERVICE), "--entry", "quadraticNormCertificate"], input=payload,
        text=True, capture_output=True, check=True).stdout.splitlines() if line.strip()]
    factored = [json.loads(line)["result"] for line in subprocess.run(
        [str(SERVICE), "--entry", "factor"], input=payload,
        text=True, capture_output=True, check=True).stdout.splitlines() if line.strip()]

    failures, agreed = [], 0
    for (c, ds), cert, fact in zip(cases, certified, factored):
        got = bool(cert.get("certified"))
        degrees = sorted(len(f["coeffs"]) - 1 for f in fact["factors"])
        irreducible = degrees == [2 ** len(ds)]
        indep = independent(ds)
        if got != indep:
            failures.append(f"certificate {got} but independence {indep} "
                            f"for c={c}, ds={ds}")
        if indep != irreducible:
            failures.append(f"independence {indep} but production factor "
                            f"degrees {degrees} for c={c}, ds={ds}")
        if got == indep == irreducible:
            agreed += 1
    return [{"cases": len(cases), "seed": seed, "agreed": agreed,
             "certified": sum(1 for c in certified if c.get("certified"))}], failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    parser.add_argument("--random", type=int, default=250,
                        help="randomized independence/certificate/factorization "
                             "agreement cases (0 disables)")
    parser.add_argument("--seed", type=int, default=20260804)
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

    random_summary = []
    if args.random:
        random_summary, random_failures = random_pass(args.random, args.seed)
        failures.extend(random_failures)
        summary = random_summary[0]
        print(f"  {'randomized agreement':24s} {summary['cases']} cases, "
              f"{summary['certified']} certified, {summary['agreed']} agreeing "
              f"with the production factorizer", file=sys.stderr)

    record = {"schema": "hexbz-quadratic-norm-witnesses/2", "cases": rows,
              "random": random_summary, "failures": failures}
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
