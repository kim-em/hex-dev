/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexPrimality

/-!
Deterministic fixture emission for `hex-primality`.

Every case is fixed data (no randomness beyond the reproducible seeds baked
into `isPrime`), so repeated runs emit identical JSONL and CI can diff the
stream against the committed snapshot. The oracle recomputes each `isprime`,
`nextprime`, and `segment` result with PARI, replays each `certcheck` with an
independent Python reimplementation of the checker, and cross-checks every
primality verdict with python-flint.

Only operations for which the driver can independently recompute the result
are emitted. Multiplicative order, p−1 and rho route selection, search
accounting and bounded failures, sieve bitsets, and elaborator behavior remain
in `HexPrimality.Conformance`, where algebraic identities and route traces test
them directly; emitting Lean's observations of those properties would create
ceremonial fixtures rather than independent oracle evidence.

The certificate serialization is
`{"t":"small","n":N}` / `{"t":"pock","n":N,"f":[[a,e,child],…]}` /
`{"t":"pock3","n":N,"r":R,"s":S,"w":W,"f":[…]}`, produced here because the
shared emission library cannot depend on `HexPrimality`.
-/

open Hex.Conformance.Emit
open Hex.Nat (PrimeCert)

private def lib : String := "HexPrimality"

private def quote (s : String) : String := "\"" ++ s ++ "\""

private def emitNextPrimeFixture (case : String) (n : Nat) : IO Unit := do
  let line := "{\"kind\":\"nextprime\",\"lib\":" ++ quote lib ++
    ",\"case\":" ++ quote case ++ ",\"n\":" ++ toString n ++ "}\n"
  match (← IO.getEnv "HEX_FIXTURE_OUTPUT") with
  | none => IO.print line
  | some path =>
      let handle ← IO.FS.Handle.mk path IO.FS.Mode.append
      handle.putStr line

mutual

private partial def certJson : PrimeCert → String
  | .small n => "{\"t\":\"small\",\"n\":" ++ toString n ++ "}"
  | .pock n f =>
      "{\"t\":\"pock\",\"n\":" ++ toString n ++ ",\"f\":" ++ factorsJson f ++ "}"
  | .pock3 n r s w f =>
      "{\"t\":\"pock3\",\"n\":" ++ toString n ++ ",\"r\":" ++ toString r ++
        ",\"s\":" ++ toString s ++ ",\"w\":" ++ toString w ++
        ",\"f\":" ++ factorsJson f ++ "}"

private partial def factorsJson (f : List (Nat × Nat × PrimeCert)) : String :=
  "[" ++ String.intercalate ","
    (f.map fun x =>
      "[" ++ toString x.1 ++ "," ++ toString x.2.1 ++ "," ++
        certJson x.2.2 ++ "]") ++ "]"

end

/-- The `isprime` verdict surface: zero/one/small edges, prime squares and
near-square-root semiprimes (the inputs that break a trial-division bound
off by one), every SPEC Carmichael number (where Fermat tests pass on
coprime bases and Miller-Rabin must not), the base-specific strong pseudoprimes (which catch
a quietly truncated base list), Fermat primes `2^k + 1`, and
certificate-tier inputs whose `n - 1` factors over the committed table. -/
private def isPrimeCases : List (String × Nat) :=
  [ ("edge/zero", 0), ("edge/one", 1), ("edge/two", 2), ("edge/three", 3),
    ("edge/four", 4), ("small/prime/5", 5), ("small/composite/6", 6),
    ("small/prime/7", 7), ("small/composite/9", 9),
    ("square/49", 49), ("square/121", 121), ("square/10201", 10201),
    ("semiprime/91", 91), ("semiprime/899", 899), ("semiprime/10403", 10403),
    ("carmichael/561", 561), ("carmichael/1105", 1105),
    ("carmichael/1729", 1729), ("carmichael/2465", 2465),
    ("carmichael/6601", 6601), ("carmichael/8911", 8911),
    ("strongpsp/2047", 2047), ("strongpsp/1373653", 1373653),
    ("strongpsp/25326001", 25326001), ("strongpsp/3215031751", 3215031751),
    ("fermat/257", 257), ("fermat/65537", 65537),
    ("table/99991", 99991), ("trial/100003", 100003),
    ("cert/10000019", 10000019), ("cert/99999989", 99999989),
    ("cert/mersenne31", 2147483647),
    ("cert/mersenne31-succ2", 2147483649) ]

/-- The `nextPrime?` value surface: the bottom edge, an ordinary table result,
the table/trial boundary, and a certificate-tier result. The generator state
and bounded failures remain core-only route properties. -/
private def nextPrimeCases : List (String × Nat × Nat) :=
  [ ("edge/zero", 0, 4),
    ("table/after-90", 90, 16),
    ("trial/after-99991", 99991, 16),
    ("cert/after-10000000", 10000000, 32) ]

/-- The `certcheck` surface: accepted certificates one, two, and three
levels deep plus the accepted cube-root node, and one rejected certificate
per checker clause: the F-squared bound, composite and non-dividing
factors, failed gcd witnesses, table misses, subjects below two and even
subjects, duplicate and noncanonically ordered subjects, the bounded-product
abort, and for the cube-root arm the even-cofactor, decomposition, r-range,
size-bound, and both strict witness-window conditions. No oracle produces the
negatives, so they are constructed by hand. -/
private def certCases : List (String × Nat × PrimeCert) :=
  [ ("accept/small", 97, .small 97),
    ("accept/pock1", 7, .pock 7 [(2, 0, .small 3)]),
    ("accept/pock2", 31, .pock 31 [(3, 0, .small 3), (3, 0, .small 5)]),
    ("accept/nested-pock", 4200127,
      .pock 4200127 [(2, 0, .pock 100003 [(2, 0, .small 2381)])]),
    ("accept/pock3", 199, .pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]),
    ("reject/bound", 13, .pock 13 [(2, 0, .small 3)]),
    ("reject/unsorted-subjects", 31,
      .pock 31 [(3, 0, .small 5), (3, 0, .small 3)]),
    ("reject/composite-factor", 7, .pock 7 [(2, 0, .small 4)]),
    ("reject/gcd-witness", 7, .pock 7 [(6, 0, .small 3)]),
    ("reject/nondividing", 11, .pock 11 [(2, 0, .small 7)]),
    ("reject/table-miss", 100003, .small 100003),
    ("reject/pock3-witness", 199,
      .pock3 199 9 2 7 [(3, 0, .small 2), (2, 0, .small 3)]),
    ("reject/pock3-odd-F", 199, .pock3 199 9 2 8 [(2, 0, .small 3)]),
    ("reject/one", 1, .pock 1 []),
    ("reject/even", 8, .pock 8 [(3, 0, .small 7)]),
    ("reject/duplicate-subject", 17,
      .pock 17 [(3, 1, .small 2), (3, 1, .small 2)]),
    ("reject/product-abort", 97, .pock 97 [(5, 1048576, .small 2)]),
    ("reject/pock3-even-R", 193,
      .pock3 193 8 2 0 [(5, 0, .small 2), (5, 0, .small 3)]),
    ("reject/pock3-decomp", 199,
      .pock3 199 8 2 8 [(3, 0, .small 2), (2, 0, .small 3)]),
    ("reject/pock3-r-range", 199,
      .pock3 199 33 0 0 [(3, 0, .small 2), (2, 0, .small 3)]),
    ("reject/pock3-witness-high", 199,
      .pock3 199 9 2 9 [(3, 0, .small 2), (2, 0, .small 3)]),
    ("reject/pock3-size", 43, .pock3 43 1 5 0 [(3, 0, .small 2)]) ]

/-- The `segment` surface: the SPEC's `[1, 100]` and `[1, 10^4]`, plus one
segment straddling `primeTableBound` to check that the table and fallback
agree across the boundary. The release-gated `hotPathCandidates` migration is
tracked separately by issue #9849. -/
private def segmentCases : List (String × Nat × Nat) :=
  [ ("edge/empty", 10, 10),
    ("basic/1-100", 1, 101),
    ("table/1-10000", 1, 10000),
    ("straddle/99950-100050", 99950, 100050) ]

private def emitCase : IO Unit := do
  for (case, n) in isPrimeCases do
    emitIsPrimeFixture lib s!"isprime/{case}" (Int.ofNat n)
    emitResult lib s!"isprime/{case}" "isprime" (boolValue (Hex.Nat.isPrime n))
  for (case, n, fuel) in nextPrimeCases do
    let case := s!"nextprime/{case}"
    emitNextPrimeFixture case n
    match Hex.Nat.nextPrime? n (Hex.Rand.ofSeed n) fuel with
    | .ok (p, _) => emitResult lib case "nextprime" (toString p)
    | .error _ => throw <| IO.userError (case ++ ": bounded search exhausted")
  for (case, n, cert) in certCases do
    emitCertCheckFixture lib s!"certcheck/{case}" (Int.ofNat n) (certJson cert)
    emitResult lib s!"certcheck/{case}" "certcheck"
      (boolValue (Hex.Nat.checkPrime cert))
  for (case, lo, hi) in segmentCases do
    emitSegmentFixture lib s!"segment/{case}" (Int.ofNat lo) (Int.ofNat hi)
    emitResult lib s!"segment/{case}" "segment"
      (intListValue ((Hex.Nat.primesIn lo hi).toList.map Int.ofNat))

def main : IO Unit := emitCase
