#!/usr/bin/env python3
"""Deterministic generator for the hex Berlekamp-Zassenhaus factorization corpus.

Regenerating with a fixed toolchain (Python + sympy) produces a byte-identical
``bench/corpus/hexbz-factor-corpus.jsonl``. Every record is one factorization
instance:

    {"name","family","degree","coeffs","provenance","expectedFactorDegrees?","combined"}

``coeffs`` is the integer coefficient list in **ascending** degree order (the
suite line protocol), ``expectedFactorDegrees`` (optional) is the sorted degree
multiset of the irreducible factorization for cross-checks, and ``combined`` is
the mix-doctrine flag: every family is capped at an equal count, spread across
its degree range, so the combined cactus plot is a balanced mixture.

The suite needs no network at sweep time; the Hoeij-Zimmermann literature
coefficients are vendored under ``scripts/bench/vendor/hoeij/`` and parsed here.

Run: ``python3 scripts/bench/gen_factor_corpus.py`` (writes the corpus and prints
a per-family summary). ``--check`` regenerates in memory and diffs against the
committed file without writing.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import sys
from pathlib import Path

from sympy import (
    Poly,
    chebyshevt_poly,
    chebyshevu_poly,
    cyclotomic_poly,
    divisors,
    factor_list,
    laguerre_poly,
    legendre_poly,
    symbols,
    totient,
)

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
VENDOR_DIR = ROOT / "scripts" / "bench" / "vendor" / "hoeij"
CONWAY_CACHE = ROOT / "scripts" / "oracle" / "luebeck_conway_cache.json"

X = symbols("x")

# Mix doctrine: every family contributes exactly this many instances to the
# combined chart, spread across its own degree range. Per-family charts use all.
COMBINED_CAP = 15

# First 40 primes; SD_k uses the first k of them.
PRIMES = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
]


# --------------------------------------------------------------------------
# Pure-integer polynomial arithmetic (ascending coefficient lists).
# Used for the Swinnerton-Dyer construction, which needs exact bigint results
# far larger than numpy can hold.
# --------------------------------------------------------------------------
def p_trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def p_add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def p_sub(a, b):
    n = max(len(a), len(b))
    return p_trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def p_scale(a, c):
    return [c * x for x in a]


def p_shift1(a):
    """Multiply by x."""
    return [0] + list(a)


def p_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return p_trim(out)


def p_compose_shift(a, c):
    """Return a(x + c) via Horner, exact integer arithmetic."""
    result = [0]
    for coeff in reversed(a):
        result = p_add(p_mul(result, [c, 1]), [coeff])
    return p_trim(result)


def swinnerton_dyer(k):
    """Minimal polynomial of sqrt(p_1)+...+sqrt(p_k), monic, degree 2^k.

    Uses g_j = A^2 - p * B^2 where g_{j-1}(x - y) = A(x) + y B(x) (mod y^2 - p),
    with the recurrence a' = x*a - p*b, b' = x*b - a for (x - y)^i.
    """
    g = [0, 1]  # g_0 = x
    for p in PRIMES[:k]:
        # Build A = sum c_i a_i, B = sum c_i b_i where (x-y)^i = a_i + y b_i.
        a_i, b_i = [1], [0]  # (x - y)^0
        A, B = [0], [0]
        for ci in g:
            if ci != 0:
                A = p_add(A, p_scale(a_i, ci))
                B = p_add(B, p_scale(b_i, ci))
            # (x - y)^{i+1}: a' = x a - p b, b' = x b - a
            a_next = p_sub(p_shift1(a_i), p_scale(b_i, p))
            b_next = p_sub(p_shift1(b_i), a_i)
            a_i, b_i = a_next, b_next
        g = p_sub(p_mul(A, A), p_scale(p_mul(B, B), p))
    return p_trim(g)


# --------------------------------------------------------------------------
# sympy -> ascending int coefficient list
# --------------------------------------------------------------------------
def poly_to_coeffs(expr):
    poly = Poly(expr, X)
    coeffs = [int(c) for c in poly.all_coeffs()[::-1]]
    return p_trim(coeffs)


def irreducible_factor_degrees(coeffs):
    """Sorted degree multiset of the irreducible factorization over Q."""
    expr = sum(c * X**i for i, c in enumerate(coeffs))
    _, factors = factor_list(expr, X)
    degs = []
    for fac, mult in factors:
        degs.extend([Poly(fac, X).degree()] * mult)
    return sorted(degs)


# --------------------------------------------------------------------------
# Vendored Hoeij-Zimmermann Maple-format parser
# --------------------------------------------------------------------------
def parse_maple_assignments(text):
    """Return {name: sympy expr} for each ``name := <expr>`` polynomial statement.

    Handles ``#`` comments, ``\\`` line continuations, and ``:``/``;`` terminators.
    Only the first assignment to each name is kept.
    """
    text = re.sub(r"#[^\n]*", "", text)
    text = text.replace("\\\n", "")
    text = text.replace("\\", "")
    text = text.replace(":=", "\x00")  # protect the assignment operator
    out = {}
    for statement in re.split(r"[:;]", text):
        if "\x00" not in statement:
            continue
        name, rhs = statement.split("\x00", 1)
        name = name.strip()
        rhs = rhs.strip()
        if not name or not rhs or name in out:
            continue
        # Only keep statements whose RHS is a bare polynomial (no function calls).
        if re.search(r"[A-Za-z_]\w*\s*\(", rhs):
            continue
        expr_text = rhs.replace("^", "**").replace("X", "x")
        try:
            from sympy import sympify

            out[name] = sympify(expr_text)
        except Exception:
            continue
    return out


def hoeij_poly(filename, assignment):
    text = (VENDOR_DIR / filename).read_text()
    exprs = parse_maple_assignments(text)
    expr = exprs[assignment]
    poly = Poly(expr, X)
    if not poly.domain.is_ZZ:
        poly = Poly(poly * poly.rep.dom.convert(1), X)  # keep integer form
    coeffs = [int(c) for c in poly.all_coeffs()[::-1]]
    return p_trim(coeffs)


# --------------------------------------------------------------------------
# Family builders. Each returns a list of (name, degree, coeffs, provenance,
# expectedFactorDegrees|None) tuples in deterministic order.
# --------------------------------------------------------------------------
def family_cyclotomic():
    # n values chosen so degrees phi(n) span ~4..1030, log-spaced, mixing primes
    # (many small mod-p factors, single big irreducible) with highly-composite n.
    ns = [
        5, 7, 8, 12, 11, 15, 13, 21, 17, 24, 19, 32, 23, 35, 29, 45, 37, 48,
        41, 55, 53, 64, 61, 105, 89, 128, 121, 165, 151, 210, 179, 256,
        257, 385, 331, 512, 509, 1031, 25, 27, 49, 81, 243, 275, 625,
    ]
    seen = set()
    out = []
    for n in ns:
        deg = int(totient(n))
        if deg in seen:
            continue
        seen.add(deg)
        coeffs = poly_to_coeffs(cyclotomic_poly(n, X))
        out.append((
            f"cyclo_phi{n}",
            deg,
            coeffs,
            f"Phi_{n}(x), the {n}th cyclotomic polynomial (irreducible)",
            [deg],
        ))
    return out


def family_cyclotomic_products():
    out = []
    # x^n - 1 = prod_{d|n} Phi_d : structured heavy reducibles.
    for n in [6, 12, 15, 20, 24, 30, 36, 48, 60, 105, 120]:
        coeffs = [-1] + [0] * (n - 1) + [1]
        degs = sorted(int(totient(d)) for d in divisors(n))
        out.append((
            f"xpow{n}_minus1",
            n,
            coeffs,
            f"x^{n} - 1 = prod_(d|{n}) Phi_d(x)",
            degs,
        ))
    # Phi_a * Phi_b pairs.
    for a, b in [(7, 11), (12, 13), (15, 17), (24, 35), (32, 45), (64, 105), (105, 128), (128, 165)]:
        ca = poly_to_coeffs(cyclotomic_poly(a, X))
        cb = poly_to_coeffs(cyclotomic_poly(b, X))
        coeffs = p_mul(ca, cb)
        degs = sorted([int(totient(a)), int(totient(b))])
        out.append((
            f"cyclo_phi{a}_x_phi{b}",
            len(coeffs) - 1,
            coeffs,
            f"Phi_{a}(x) * Phi_{b}(x)",
            degs,
        ))
    return out


def family_swinnerton_dyer():
    out = []
    for k in range(2, 8):  # SD2..SD7, degrees 4..128
        coeffs = swinnerton_dyer(k)
        deg = 2 ** k
        primes = ", ".join(str(p) for p in PRIMES[:k])
        out.append((
            f"sd{k}",
            deg,
            coeffs,
            f"Swinnerton-Dyer SD_{k}: min poly of sqrt(p) sum over p in {{{primes}}}",
            [deg],
        ))
    # Shifted variants SD_k(x + c): still irreducible, degree 2^k.
    for k, c in [(2, 1), (3, 1), (3, 2), (4, 1), (4, 3), (5, 1), (5, 2), (6, 1), (6, 5)]:
        coeffs = p_compose_shift(swinnerton_dyer(k), c)
        deg = 2 ** k
        out.append((
            f"sd{k}_shift{c}",
            deg,
            coeffs,
            f"Swinnerton-Dyer SD_{k}(x + {c}) (irreducible)",
            [deg],
        ))
    return out


def family_sd_products():
    out = []
    # SD_k(x) * SD_k(x+1): two irreducible degree-2^k factors, high r.
    for k in [2, 3, 4, 5, 6]:
        base = swinnerton_dyer(k)
        coeffs = p_mul(base, p_compose_shift(base, 1))
        deg = 2 ** (k + 1)
        out.append((
            f"sd{k}_x_sd{k}shift1",
            deg,
            coeffs,
            f"SD_{k}(x) * SD_{k}(x + 1)",
            sorted([2 ** k, 2 ** k]),
        ))
    # SD_k * Phi_m: mixed-shape high-r reducibles.
    for k, m in [(2, 12), (3, 15), (3, 24), (4, 17), (4, 35), (5, 11), (5, 45), (6, 13), (6, 105)]:
        base = swinnerton_dyer(k)
        cm = poly_to_coeffs(cyclotomic_poly(m, X))
        coeffs = p_mul(base, cm)
        deg = len(coeffs) - 1
        out.append((
            f"sd{k}_x_phi{m}",
            deg,
            coeffs,
            f"SD_{k}(x) * Phi_{m}(x)",
            sorted([2 ** k, int(totient(m))]),
        ))
    return out


def family_chebyshev():
    out = []
    ns = [3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 18, 20, 24]
    for n in ns:
        for kind, builder in (("T", chebyshevt_poly), ("U", chebyshevu_poly)):
            coeffs = poly_to_coeffs(builder(n, X))
            out.append((
                f"chebyshev_{kind}{n}",
                n,
                coeffs,
                f"Chebyshev {kind}_{n}(x) (structured reducible)",
                irreducible_factor_degrees(coeffs),
            ))
    return out


def family_legendre():
    out = []
    ns = [3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38]
    for n in ns:
        coeffs = poly_to_coeffs((2 ** n) * legendre_poly(n, X))
        out.append((
            f"legendre_P{n}",
            n,
            coeffs,
            f"2^{n} * P_{n}(x), integerized Legendre (irreducible in practice)",
            irreducible_factor_degrees(coeffs),
        ))
    return out


def family_laguerre():
    out = []
    import math

    ns = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32]
    for n in ns:
        coeffs = poly_to_coeffs(math.factorial(n) * laguerre_poly(n, X))
        out.append((
            f"laguerre_L{n}",
            n,
            coeffs,
            f"{n}! * L_{n}(x), integerized Laguerre (Schur-irreducible)",
            irreducible_factor_degrees(coeffs),
        ))
    return out


def family_wilkinson():
    out = []
    ns = [4, 6, 8, 10, 12, 14, 16, 18, 20, 24, 28, 32, 40, 48, 56]
    for n in ns:
        coeffs = [1]
        for i in range(1, n + 1):
            coeffs = p_mul(coeffs, [-i, 1])
        out.append((
            f"wilkinson_{n}",
            n,
            coeffs,
            f"prod_(i=1..{n}) (x - i), fully split",
            [1] * n,
        ))
    return out


def family_random_products():
    out = []
    for i in range(30):
        name = f"randprod_{i:02d}"
        seed = int(hashlib.sha256(name.encode()).hexdigest(), 16) % (2 ** 32)
        rng = random.Random(seed)
        n_factors = 3 if i % 3 == 0 else 2
        height = rng.choice([4, 8, 16])
        product = [1]
        for _ in range(n_factors):
            deg = rng.randint(3, 10)
            fac = [rng.randint(-height, height) for _ in range(deg)]
            lead = 0
            while lead == 0:
                lead = rng.randint(-height, height)
            fac.append(lead)
            product = p_mul(product, fac)
        out.append((
            name,
            len(product) - 1,
            product,
            f"seeded random product of {n_factors} dense height-{height} factors "
            f"(sha256({name}) seed)",
            irreducible_factor_degrees(product),
        ))
    return out


def family_hoeij_zimmermann():
    """Vendored literature benchmark set (Hart-van Hoeij-Novocin, ISSAC 2011).

    Only instances whose integer coefficients are directly recoverable from the
    vendored knapsack files are included. The full M12 5/6-set resolvents
    (deg 792/924) and Trager T1-T3 (deg 900/2401) require a Maple resolvent
    computation and are not in the vendored knapsack directory; S7-S9 regenerate
    exactly as the Swinnerton-Dyer SD7-SD9 polynomials.
    """
    out = []
    cite = "Hart-van Hoeij-Novocin, Practical Polynomial Factoring in Polynomial Time (ISSAC 2011); coeffs vendored from math.fsu.edu/~hoeij/knapsack/polys"
    vendored = [
        ("hoeij_P7", "P7", "P7", "P7"),
        ("hoeij_M12_f132", "Mathieu_group_M12", "f132", "degree-132 factor of the M12 6-set resolvent"),
        ("hoeij_F190", "F_190", "f", "F_190"),
        ("hoeij_F192", "F_192", "f", "F_192"),
        ("hoeij_F256", "F_256", "f", "F_256"),
        ("hoeij_F351", "F_351", "f", "F_351"),
        ("hoeij_F630", "F_630", "f", "F_630"),
    ]
    for name, filename, assignment, label in vendored:
        coeffs = hoeij_poly(filename, assignment)
        out.append((name, len(coeffs) - 1, coeffs, f"{label}; {cite}", None))
    # S7-S9 are the Swinnerton-Dyer polynomials, regenerated exactly.
    for k in [7, 8, 9]:
        coeffs = swinnerton_dyer(k)
        deg = 2 ** k
        out.append((
            f"hoeij_S{k}",
            deg,
            coeffs,
            f"S{k} = Swinnerton-Dyer SD_{k} (deg {deg}); {cite}",
            [deg],
        ))
    return out


def family_conway():
    """Lifted Conway polynomials from Frank Lübeck's tables (issue #8557).

    Each ``C_{p,n}`` is monic and irreducible over 𝔽_p. Its coefficients are
    read from the committed cache (``scripts/oracle/luebeck_conway_cache.json``,
    ascending order, non-negative representatives ``0..p-1``) and taken verbatim
    as a monic integer polynomial. A monic integer polynomial irreducible modulo
    a prime is irreducible over ℚ (its degree is preserved because it is monic),
    so every lift is irreducible over ℤ — ``expectedFactorDegrees = [n]``. This
    is the recombination worst case (like Swinnerton-Dyer), but the tables sweep
    two axes at once: degree grows with n (small primes), coefficient height
    grows with p (a lift has height up to p - 1, so high primes at low degree
    load the height axis). The differential-correctness cross-check in
    ``factor_sweep.py`` verifies the ``[n]`` labels against FLINT/NTL/PARI.
    """
    payload = json.loads(CONWAY_CACHE.read_text())
    if payload.get("coefficient_order") != "ascending":
        raise ValueError(f"{CONWAY_CACHE}: expected ascending coefficient_order")
    out = []
    for entry in sorted(payload["entries"], key=lambda e: (e["p"], e["n"])):
        p, n, coeffs = entry["p"], entry["n"], [int(c) for c in entry["coeffs"]]
        if len(coeffs) != n + 1 or coeffs[-1] != 1:
            raise ValueError(f"cache entry ({p},{n}) is not monic degree n: {coeffs}")
        out.append((
            f"conway_p{p}_n{n}",
            n,
            coeffs,
            f"Conway polynomial C_{{{p},{n}}} lifted from F_{p} "
            f"(representatives 0..{p - 1}), Lübeck table; irreducible over Z",
            [n],
        ))
    return out


FAMILIES = [
    ("cyclotomic", family_cyclotomic),
    ("cyclotomic-products", family_cyclotomic_products),
    ("swinnerton-dyer", family_swinnerton_dyer),
    ("sd-products", family_sd_products),
    ("chebyshev", family_chebyshev),
    ("legendre", family_legendre),
    ("laguerre", family_laguerre),
    ("wilkinson", family_wilkinson),
    ("random-products", family_random_products),
    ("hoeij-zimmermann", family_hoeij_zimmermann),
    ("conway", family_conway),
]


def mark_combined(records):
    """Set the mix-doctrine ``combined`` flag: cap each family at COMBINED_CAP,
    spread across its degree range (sorted by degree then name)."""
    by_family = {}
    for rec in records:
        by_family.setdefault(rec["family"], []).append(rec)
    for fam_records in by_family.values():
        ordered = sorted(fam_records, key=lambda r: (r["degree"], r["name"]))
        n = len(ordered)
        if n <= COMBINED_CAP:
            picks = set(range(n))
        else:
            # Evenly spaced indices across the sorted range, endpoints included.
            picks = {round(j * (n - 1) / (COMBINED_CAP - 1)) for j in range(COMBINED_CAP)}
        for idx, rec in enumerate(ordered):
            rec["combined"] = idx in picks


def build_records():
    records = []
    for family_name, builder in FAMILIES:
        for name, degree, coeffs, provenance, expected in builder():
            rec = {
                "name": name,
                "family": family_name,
                "degree": degree,
                "coeffs": coeffs,
                "provenance": provenance,
            }
            if expected is not None:
                rec["expectedFactorDegrees"] = expected
            rec["combined"] = False  # set by mark_combined
            records.append(rec)
    mark_combined(records)
    return records


def serialize(records):
    lines = []
    for rec in records:
        # Fixed key order for byte-identical output.
        ordered = {"name": rec["name"], "family": rec["family"], "degree": rec["degree"],
                   "coeffs": rec["coeffs"], "provenance": rec["provenance"]}
        if "expectedFactorDegrees" in rec:
            ordered["expectedFactorDegrees"] = rec["expectedFactorDegrees"]
        ordered["combined"] = rec["combined"]
        lines.append(json.dumps(ordered, separators=(",", ":"), ensure_ascii=True))
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="regenerate in memory and diff against the committed corpus")
    args = parser.parse_args()

    records = build_records()
    text = serialize(records)

    if args.check:
        if not CORPUS_PATH.exists():
            print(f"MISSING {CORPUS_PATH}", file=sys.stderr)
            return 1
        current = CORPUS_PATH.read_text()
        if current != text:
            print("CORPUS DIFFERS from committed file", file=sys.stderr)
            return 1
        print(f"OK corpus byte-identical ({len(records)} instances)")
        return 0

    CORPUS_PATH.parent.mkdir(parents=True, exist_ok=True)
    CORPUS_PATH.write_text(text)

    # Per-family summary.
    by_family = {}
    for rec in records:
        by_family.setdefault(rec["family"], []).append(rec)
    print(f"wrote {len(records)} instances to {CORPUS_PATH.relative_to(ROOT)}")
    total_combined = 0
    for family_name, _ in FAMILIES:
        recs = by_family[family_name]
        degs = [r["degree"] for r in recs]
        combined = sum(1 for r in recs if r["combined"])
        total_combined += combined
        print(f"  {family_name:22s} n={len(recs):3d}  deg {min(degs):4d}..{max(degs):4d}  combined={combined}")
    print(f"  {'TOTAL':22s} n={len(records):3d}  combined={total_combined}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
