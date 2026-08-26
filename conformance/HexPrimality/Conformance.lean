/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality

/-!
Core conformance checks for the `hex-primality` decision, certificate, and
segment surfaces.

Oracle: PARI (via cypari2) recomputes `isprime` verdicts and `segment`
listings and an independent Python reimplementation replays `certcheck`
cases (`scripts/oracle/primality_pari.py`); python-flint is the second
opinion on large verdicts where available.
Mode: `if_available`
Covered operations:
- `Hex.Nat.isPrime` / `Hex.Nat.isPrime?`
- `Hex.Nat.checkPrime` on `PrimeCert` values
- `Hex.Nat.primeCert?`
- `Hex.Nat.rhoFactor?`, its counted internal form, and batched-Brent route
  instrumentation
- `Hex.Nat.millerRabin` / `Hex.Nat.isProbablePrime`
- `Hex.Nat.isTablePrime`
- `Hex.Nat.primesIn`
- `Hex.Nat.nextPrime?`
Covered properties:
- the total decision agrees with trial division on an initial segment
- a `.composite` certificate-search verdict never contradicts `isPrime`
- accepted certificates replay; each rejection reason rejects
- the committed table window and the runtime segment listing agree
Covered edge cases:
- `0`, `1`, `2`, and the parity edge `4`
- Carmichael numbers, where a Fermat test would pass and Miller-Rabin
  must not
- base-specific strong pseudoprimes, which catch a truncated base list
- prime squares and semiprimes with a factor just below the square root
- the certificate tier at `2^31 - 1` (deterministic: `n - 1` factors over
  the committed table)
-/

open Hex.Nat

-- Decision spot values.
/-- info: true -/
#guard_msgs in
#eval isPrime 2147483647

/-- info: false -/
#guard_msgs in
#eval isPrime 561

#guard isPrime 0 = false
#guard isPrime 1 = false
#guard isPrime 2 = true
#guard isPrime 4 = false
#guard isPrime 49 = false
#guard isPrime 10403 = false     -- 101 · 103
#guard isPrime 1729 = false      -- Carmichael
#guard isPrime 3215031751 = false -- strong pseudoprime to 2, 3, 5, 7
#guard isPrime 65537 = true
#guard isPrime 10007 = true

-- Agreement with trial division on an initial segment.
#guard (List.range 2000).all fun n => isPrime n == isPrimeTrial n

-- Certificate checker: accepted shapes and one rejection per clause.
#guard checkPrime (.pock 7 [(2, 0, .small 3)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)]) = true
#guard checkPrime (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true
#guard checkPrime (.pock 13 [(2, 0, .small 3)]) = false      -- F² ≤ n
#guard checkPrime (.pock 7 [(2, 0, .small 4)]) = false       -- composite factor
#guard checkPrime (.pock 7 [(6, 0, .small 3)]) = false       -- gcd witness fails
#guard checkPrime (.pock 11 [(2, 0, .small 7)]) = false      -- 7 ∤ 10
#guard checkPrime (.pock 1 []) = false                       -- n < 2
#guard checkPrime (.pock 8 [(3, 0, .small 7)]) = false       -- even n
#guard checkPrime (.pock 17 [(3, 1, .small 2), (3, 1, .small 2)]) = false
  -- duplicate subjects: each entry alone passes its witness check
#guard checkPrime (.pock 97 [(5, 1048576, .small 2)]) = false
  -- bounded-product abort on a huge exponent
#guard checkPrime (.pock3 193 8 2 0 [(5, 0, .small 2), (5, 0, .small 3)]) = false
  -- cofactor R = 32 is even
#guard checkPrime (.pock3 199 8 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- decomposition 33 ≠ 2·6·2 + 8
#guard checkPrime (.pock3 199 33 0 0 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- r = 33 outside [1, 2F)
#guard checkPrime (.pock3 199 9 2 7 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- witness window upper side: 65 < 64 fails
#guard checkPrime (.pock3 199 9 2 9 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- witness window lower side: 81 < 65 fails
#guard checkPrime (.pock3 43 1 5 0 [(3, 0, .small 2)]) = false
  -- cube-size bound: 43 ≥ (F+1)(2F² + (r-1)F + 1) = 27

-- Certificate search round-trips through the checker.
#guard (match primeCert? 2147483647 (Hex.Rand.ofSeed 0) 8 with
        | .ok (c, _) => checkPrime c.raw && (c.raw.subject == 2147483647)
        | .error _ => false)
#guard (match primeCert? 2147483649 (Hex.Rand.ofSeed 0) 8 with
        | .error f => f.stop == .composite
        | .ok _ => false)

-- Counted compatibility forms retain successful randomized work without
-- changing the ordinary pair-returning entry points.
#guard (match Internal.rhoFactorCounted? 9 (Hex.Rand.ofSeed 2) 8 with
  | .ok success => success.factor == 3 && success.attempts == 4
  | .error _ => false)

#guard (match Internal.primeCertCounted? 1000003
    (Hex.Rand.ofSeed 3) 16 with
  | .ok success =>
      success.attempts == 8 &&
        success.rand == ((Hex.Rand.ofSeed 3).words 8).2
  | .error _ => false)

-- Fuel two certifies an earlier child and finds its witness before a later
-- recursive child exhausts. The failure retains that successful work.
#guard (match Internal.primeCertCounted? 1000003
    (Hex.Rand.ofSeed 3) 2 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 2 &&
        failure.rand == ((Hex.Rand.ofSeed 3).words 2).2
  | .ok _ => false)

-- A deeper child consumes its own randomized subtotal before exhaustion;
-- the parent retains both its earlier witness and that child subtotal.
#guard (match Internal.primeCertCounted? 1000000007
    (Hex.Rand.ofSeed 3) 3 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 7 &&
        failure.rand == ((Hex.Rand.ofSeed 3).words 7).2
  | .ok _ => false)

-- This strong pseudoprime passes the fixed Miller--Rabin screen, then its
-- first certificate witness search consumes all 32 candidates. The retained
-- total also includes the preceding four partial-factor rho restarts.
#guard (match Internal.primeCertCounted? 3317044064679887385961981
    (Hex.Rand.ofSeed 0) 2 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 36
  | .ok _ => false)

-- Routine gcds are genuinely batched: this fixed restart performs 95
-- polynomial steps but only seven gcds.
private def rhoBatchTrace : Hex.Nat.Internal.RhoTrace :=
  Hex.Nat.Internal.rhoTrace 100160063 1 2 256

#guard rhoBatchTrace.factor == some 10007
#guard rhoBatchTrace.steps == 95
#guard rhoBatchTrace.gcds == 7
#guard (match rhoFactor? 100160063 (Hex.Rand.ofSeed 1) 8 with
  | .ok (d, _) => 1 < d && d < 100160063 && 100160063 % d == 0
  | .error _ => false)

-- Collisions for 11 and 13 share the cycle-boundary batch, so the route
-- returns their proper composite product rather than pretending it is prime.
#guard (Hex.Nat.Internal.rhoTrace 2431 1 1 32).factor == some 143

-- A whole-modulus batch is replayed and recovers the proper factor 3.
private def rhoRecoveryTrace : Hex.Nat.Internal.RhoTrace :=
  Hex.Nat.Internal.rhoTrace 9 1 0 32

#guard rhoRecoveryTrace.factor == some 3
#guard rhoRecoveryTrace.recoveries == 1

-- Seed 213 first draws the fixed pair `(c, x) = (71, 61)` modulo 91; the
-- route rejects it and advances to a non-fixed pair.
#guard Hex.Nat.Internal.rhoDrawTrace 91 (Hex.Rand.ofSeed 213) == (37, 6, 1)
-- Seed 40 first draws the globally degenerate offset `c = n - 2` and then
-- advances to the usable pair `(81, 74)`.
#guard Hex.Nat.Internal.rhoDrawTrace 91 (Hex.Rand.ofSeed 40) == (81, 74, 1)
#guard Hex.Nat.Internal.rhoRestartCap == 8

-- Miller-Rabin filter behaviour on the adversarial families.
#guard isProbablePrime 561 = false
#guard isProbablePrime 1373653 = false
#guard millerRabin 2047 2 = true
#guard millerRabin 2047 3 = false

-- Table and segments agree across the boundary.
#guard (primesIn 0 100).size = 25
#guard (primesIn 9950 10050).toList = [9967, 9973, 10007, 10009, 10037, 10039]
#guard (primesIn 9950 10050).toList.all fun p => isTablePrime p == decide (p < 10000)

-- Next-prime search across the table edge.
#guard (match nextPrime? 9973 (Hex.Rand.ofSeed 0) 64 with
        | .ok (p, _) => p == 10007
        | .error _ => false)
