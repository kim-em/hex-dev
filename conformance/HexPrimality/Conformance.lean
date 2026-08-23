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

-- Certificate checker: accepted shapes and every rejection reason.
#guard checkPrime (.pock 7 [(2, 0, .small 3)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)]) = true
#guard checkPrime (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true
#guard checkPrime (.pock 13 [(2, 0, .small 3)]) = false
#guard checkPrime (.pock 7 [(2, 0, .small 4)]) = false
#guard checkPrime (.pock 7 [(6, 0, .small 3)]) = false
#guard checkPrime (.pock 11 [(2, 0, .small 7)]) = false

-- Certificate search round-trips through the checker.
#guard (match primeCert? 2147483647 (Hex.Rand.ofSeed 0) 8 with
        | .ok (c, _) => checkPrime c.raw && (c.raw.subject == 2147483647)
        | .error _ => false)
#guard (match primeCert? 2147483649 (Hex.Rand.ofSeed 0) 8 with
        | .error f => f.stop == .composite
        | .ok _ => false)

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
