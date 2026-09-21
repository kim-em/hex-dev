# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison
"""Inspect retained data; this does not implement polynomial division or queries."""
import json
from pathlib import Path

root = Path(__file__).resolve().parents[3]
fixtures = root / "reports/bench-results/sturm-ec8f7c14f914/fixtures.jsonl"
rows = []
for line in fixtures.read_text().splitlines():
    r = json.loads(line)
    c = r["certificate"]
    stored = []
    products = []
    for key in ("squarefree", "remainders"):
        ch = c[key]
        chain = ch["chain"]
        stored += [x for p in chain for x in p]
        for i, (left, (q, right)) in enumerate(ch["steps"]):
            stored += [left, right, *q]
            products += [left*x for x in chain[i]]
            products += [a*b for a in q for b in chain[i+1]]
            products += [right*x for x in chain[i+2]]
        left, (q, right) = ch["initial"]
        stored += [left, right, *q]
        products += [a*b for a in q for b in c["head"]]
        if len(chain) > 1:
            products += [right*x for x in chain[1]]
        if ch["terminal"] is not None:
            left, q = ch["terminal"]
            stored += [left, *q]
            products += [left*x for x in chain[-2]]
            products += [a*b for a in q for b in chain[-1]]
    rows.append(dict(family=r["family"], parameter=r["parameter"],
                     max_stored_bits=max(abs(x).bit_length() for x in stored),
                     stored_outside_small_int=sum(not -(2**31) <= x < 2**31 for x in stored),
                     max_identity_product_bits=max([0]+[abs(x).bit_length() for x in products])))
print(json.dumps({
    "runtime_source": "Lean 4.34.0 include/lean/lean.h: LEAN_MAX_SMALL_INT and lean_int_mul",
    "small_int_range_on_this_64_bit_host": [-2**31, 2**31-1],
    "identity_product_scope": "Scalar products and quotient-times-polynomial terms visible in the retained replay identities; excludes initial F*P-prime, additions, Horner intermediates and producer intermediates. Not a peak-intermediate bound.",
    "fixtures": rows,
    "fibonacci_pseudo_division_multiplications": {
        "source": "HexPoly/PseudoDiv.lean, powers/active/quotient/remainder loops",
        "per_nonconstant_step": "3*m + 7 for dividend degree m+1 and divisor degree m",
        "final_constant_step": 6,
        "whole_gcd": "3*n*(n+1)/2 + 7*n + 6",
        "scope": "Calls to scalar Mul in pseudoDivMod only; excludes coefficient constructors, normalization, allocation, equality, hashing and arithmetic inside F7 operations. Coefficients remain in F7."
    }
}, indent=2))
