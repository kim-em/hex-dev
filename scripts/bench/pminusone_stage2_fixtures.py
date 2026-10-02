#!/usr/bin/env python3
"""Prepare and independently verify the SPEC's Pollard p-1 stage-2 families.

All prime assertions use trial division, the full-order criterion, or recursive
Pocklington witnesses. No probable-prime assumption enters the committed data.
Preparation, including every cofactor-order exclusion, is outside timing.
"""
from __future__ import annotations

import argparse
from functools import cache
import json
from math import gcd, isqrt, lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "conformance-fixtures/HexPrimality/pminusone-stage2.jsonl"
PRIMITIVE = [
    (67, 4175126843, 62315326), (127, 1245980999, 9810874),
    (257, 2889804119, 11244374), (509, 4034518259, 7926362),
    (1021, 1984454399, 1943638), (2039, 3821489723, 1874198),
    (4093, 1266840803, 309514), (8191, 2407646159, 293938),
    (16381, 3346015823, 204262), (32749, 3530931683, 107818),
]
INTEGRATION = [
    (67, 640593315381498719, 9561094259425354, 14),
    (127, 989082332266914563, 7788049860369406, 5),
    (257, 109241628152434139, 425064700982234, 2),
    (509, 152168461520334179, 298955720079242, 2),
    (1021, 525357598587673739, 514552006452178, 2),
    (2039, 73929628837078823, 36257787561098, 5),
    (4093, 100085828142782543, 24452926494694, 5),
    (8191, 277827051595988963, 33918575460382, 2),
    (16381, 369205211213026103, 22538624700142, 5),
    (32749, 738117420304950359, 22538624700142, 7),
]
M = lcm(*range(1, 65))


def primes(bound: int) -> list[int]:
    sieve = bytearray(b"\x01") * (bound + 1)
    sieve[:2] = b"\x00\x00"
    for q in range(2, isqrt(bound) + 1):
        if sieve[q]:
            sieve[q*q:bound+1:q] = b"\x00" * ((bound - q*q) // q + 1)
    return [q for q in range(2, bound + 1) if sieve[q]]


SMALL = primes(1000)
INTERVAL = [q for q in primes(65498) if q > 64]


def is_small_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def certify_interval(lower: int, upper: int, forbidden: set[int] | None = None) -> dict:
    """Find a prime in a wide interval with a recursively certified large factor."""
    forbidden = forbidden or set()
    if upper < 65536:
        for n in range(max(2, lower), upper + 1):
            if n not in forbidden and is_small_prime(n):
                return {"n": n, "kind": "trial"}
    child_bits = (upper.bit_length() + 1) // 2 + 1
    child = certified_bits(child_bits)
    q = child["n"]
    assert q * q > upper
    k = max(1, (lower - 1 + 2*q - 1) // (2*q))
    while (n := 2*k*q + 1) <= upper:
        k += 1
        if n in forbidden or any(n % d == 0 for d in SMALL):
            continue
        for w in (2, 3, 5, 7, 11, 13, 17):
            if pow(w, n - 1, n) != 1:
                break
            if gcd(pow(w, (n - 1) // q, n) - 1, n) == 1:
                return {"n": n, "kind": "pocklington", "witness": w, "factor": child}
    raise ValueError(f"no certified prime in [{lower}, {upper}]")


@cache
def certified_bits(bits: int) -> dict:
    return certify_interval(1 << (bits - 1), (1 << bits) - 1)


def verify_prime(cert: dict) -> int:
    n = cert["n"]
    if cert["kind"] == "trial":
        assert n < 65536 and is_small_prime(n)
    else:
        assert cert["kind"] == "pocklington"
        q = verify_prime(cert["factor"])
        w = cert["witness"]
        assert n > 2 and (n - 1) % q == 0 and q*q > n
        assert 1 < w < n and pow(w, n - 1, n) == 1
        assert gcd(pow(w, (n - 1) // q, n) - 1, n) == 1
    return n


def factor_predecessor(q: int, k: int) -> list[list[int]]:
    factors = []
    for ell in SMALL:
        if ell > 64:
            break
        e = 0
        while k % ell == 0:
            k //= ell
            e += 1
        if e:
            factors.append([ell, e])
    assert k == 1
    return factors + [[q, 1]]


def full_order_witness(p: int, factors: list[list[int]], w: int) -> bool:
    return pow(w, p - 1, p) == 1 and all(
        gcd(pow(w, (p - 1) // ell, p) - 1, p) == 1 for ell, _ in factors)


def cofactor_suitable(r: int, b2: int) -> bool:
    x = pow(2, M, r)
    return x != 1 and all(pow(x, s, r) != 1 for s in INTERVAL if s <= b2)


def generate() -> list[dict]:
    rows, used = [], set()
    for family, table, sizes in (("primitive", PRIMITIVE, (64, 128, 256, 512)),
                                  ("integration", INTEGRATION, (128, 256, 512))):
        for entry in table:
            q, p, k = entry[:3]
            factors = factor_predecessor(q, k)
            w = entry[3] if len(entry) == 4 else next(
                a for a in range(2, 100) if full_order_witness(p, factors, a))
            for bits in sizes:
                lower = ((1 << (bits - 1)) + p - 1) // p
                upper = ((1 << bits) - 1) // p
                while True:
                    cert = certify_interval(lower, upper, used | {p})
                    r = cert["n"]
                    if cofactor_suitable(r, 2*q):
                        break
                    lower = r + 1
                used.add(r)
                rows.append({"family": family, "bits": bits, "q": q, "p": p, "k": k,
                             "witness": w, "p_minus_one": factors, "r": r,
                             "r_certificate": cert, "n": p*r,
                             "base": 2, "b1": 64, "x": pow(2, M, p*r),
                             "order_quotient": q, "excluded_through": 2*q})
    return rows


def verify(rows: list[dict]) -> None:
    expected = {(family, bits, entry[0]): entry for family, table, sizes in
                (("primitive", PRIMITIVE, (64, 128, 256, 512)),
                 ("integration", INTEGRATION, (128, 256, 512)))
                for entry in table for bits in sizes}
    assert len(rows) == len(expected) == 70
    seen, cofactors = set(), set()
    for row in rows:
        key = row["family"], row["bits"], row["q"]
        assert key not in seen
        seen.add(key)
        entry = expected[key]
        q, p, k = entry[:3]
        assert (row["q"], row["p"], row["k"]) == (q, p, k)
        assert p == k*q + 1 and M % k == 0 and is_small_prime(q)
        factors = factor_predecessor(q, k)
        assert row["p_minus_one"] == factors
        assert full_order_witness(p, factors, row["witness"])
        if len(entry) == 4:
            assert row["witness"] == entry[3]
        assert pow(2, M, p) != 1 and pow(2, M*q, p) == 1
        r = verify_prime(row["r_certificate"])
        assert row["r"] == r and r != p and r not in cofactors
        cofactors.add(r)
        assert row["n"] == p*r and (p*r).bit_length() == row["bits"]
        assert row["base"] == 2 and row["b1"] == 64
        assert row["order_quotient"] == q and row["excluded_through"] == 2*q
        assert row["x"] == pow(2, M, p*r) and gcd(row["x"] - 1, p*r) == 1
        assert cofactor_suitable(r, 2*q)


def lean_certificate(cert: dict) -> str:
    if cert["kind"] == "trial":
        return f"(.small {cert['n']})"
    return (f"(.pock {cert['n']} [({cert['witness']}, 0, "
            f"{lean_certificate(cert['factor'])})])")


def render_lean(rows: list[dict], family: str) -> str:
    namespace = "PrimalityBench" if family == "primitive" else "IntFactorBench"
    header = f"""/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality

public section

/-! Exact stage-2 inputs and replayable prime certificates.
Generated by scripts/bench/pminusone_stage2_fixtures.py from the shared
SPEC family; the JSONL companion retains the order and primality witnesses. -/

namespace Hex.{namespace}.Stage2

open Hex.Nat

structure Input where
  bits : Nat
  q : Nat
  p : Nat
  r : Nat
  x : Nat
  certP : PrimeCert
  certR : PrimeCert

def Input.subject (input : Input) : Nat := input.p * input.r

instance : Inhabited Input := ⟨⟨0, 0, 0, 0, 0, .small 0, .small 0⟩⟩
instance : Hashable Input where
  hash input := hash (input.subject, input.q)

def inputs : Array Input := #[
"""
    values = []
    for row in rows:
        if row["family"] != family:
            continue
        entries = ", ".join(f"({row['witness']}, {e-1}, .small {q})"
                            for q, e in row["p_minus_one"])
        cert_p = f"(.pock {row['p']} [{entries}])"
        cert_r = lean_certificate(row["r_certificate"])
        values.append(f"  ⟨{row['bits']}, {row['q']}, {row['p']}, {row['r']}, {row['x']},\n"
                      f"    {cert_p},\n    {cert_r}⟩")
    return header + ",\n".join(values) + f"""]

#guard inputs.all fun input =>
  input.subject.log2 + 1 == input.bits && input.p != input.r &&
  input.certP.subject == input.p && checkPrime input.certP &&
  input.certR.subject == input.r && checkPrime input.certR &&
  (PMinusOne.start input.subject 2 64).residue == some input.x

end Hex.{namespace}.Stage2
"""


LEAN_FIXTURES = {
    "primitive": ROOT / "bench/HexPrimality/PMinusOneFixtures.lean",
    "integration": ROOT / "bench/HexIntFactor/PMinusOneFixtures.lean",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate deterministic witnesses")
    args = parser.parse_args()
    if args.write:
        rows = generate()
        verify(rows)
        FIXTURES.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
        for family, path in LEAN_FIXTURES.items():
            path.write_text(render_lean(rows, family))
    else:
        rows = [json.loads(line) for line in FIXTURES.read_text().splitlines()]
        verify(rows)
        for family, path in LEAN_FIXTURES.items():
            assert path.read_text() == render_lean(rows, family), f"stale Lean fixtures: {path}"
    print(f"Verified {len(rows)} exact prime/order fixtures ({FIXTURES.relative_to(ROOT)})")


if __name__ == "__main__":
    main()
