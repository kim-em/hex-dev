/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality

/-!
Core conformance checks for the `hex-primality` decision, certificate, and
segment surfaces.

Oracle: PARI (via cypari2) recomputes `isprime`, `nextprime`, and `segment`
results and an independent Python reimplementation replays `certcheck` cases
(`scripts/oracle/primality_pari.py`); python-flint is the second opinion on
every primality verdict used by the oracle.
Mode: `required`
Covered operations:
- `Hex.Nat.orderOf`
- `Hex.Nat.smoothBound` / `Hex.Nat.smoothBoundCap`
- `Hex.Nat.isPrime` / `Hex.Nat.isPrime?`
- `Hex.Nat.checkPrime` on `PrimeCert` values
- `Hex.Nat.primeCert?` / `Hex.Nat.primeCertWith?`
- `Hex.Nat.pMinusOneStage1` and its counted, resumable form
- `Hex.Nat.rhoFactor?`, its counted internal form, and batched-Brent route
  instrumentation
- trial-division extraction route instrumentation
- sieve decoding through `Hex.Nat.bitsToList`
- `Hex.Nat.millerRabin` / `Hex.Nat.isProbablePrime`
- `Hex.Nat.sieve` and its residue-index mapping
- `Hex.Nat.isTablePrime`
- `Hex.Nat.primesIn`
- `Hex.Nat.nextPrime?`
- `primality` term and tactic forms
Covered properties:
- multiplicative order is positive exactly on the tested nontrivial coprime
  inputs, reaches one, and is minimal
- the total decision agrees with trial division on an initial segment
- a `.composite` certificate-search verdict never contradicts `isPrime`
- rho restart and certificate-witness draws span arbitrary-precision bounds
  through unbiased bounded sampling and retain exact exhaustion states
- custom certificate-factor producers retain default compatibility, bounded
  exhaustion, exact attempt accounting, and advanced random state
- next-prime exhaustion separates rejected candidates from certificate work
  and returns the exact advanced random state
- accepted certificates replay; each rejection reason rejects
- the committed table window and the runtime segment listing agree
- the small sieve agrees with trial division on every represented index
- term and tactic elaboration reach the table and certificate tiers
Covered edge cases:
- `0`, `1`, `2`, and the parity edge `4`
- Carmichael numbers, where a Fermat test would pass and Miller-Rabin
  must not
- base-specific strong pseudoprimes, which catch a truncated base list
- prime squares and semiprimes with a factor just below the square root
- a p−1-friendly certificate route with rho disabled
- the certificate tier at `2^31 - 1` (deterministic: `n - 1` factors over
  the committed table)
-/

open Hex.Nat

-- Multiplicative order: a typical primitive root, both junk-value edges, and
-- a base-2 pseudoprime whose proper order catches a Fermat-only implementation.
#guard orderOf 3 7 == 6
#guard orderOf 2 1 == 0
#guard orderOf 6 9 == 0
#guard orderOf 2 341 == 10
#guard 2 ^ orderOf 2 341 % 341 == 1
#guard (List.range (orderOf 2 341)).all fun k => k == 0 || 2 ^ k % 341 != 1

-- The subject projection covers every public certificate constructor.
#guard (PrimeCert.small 97).subject == 97
#guard (PrimeCert.pock 101 []).subject == 101
#guard (PrimeCert.pock3 103 0 0 0 []).subject == 103

-- The depth and rho policies are executable API, not undocumented constants.
#guard defaultPrimeFuel 0 == 1
#guard defaultPrimeFuel 2 == 2
#guard defaultPrimeFuel (2 ^ 128) == 129
#guard defaultPrimeCertBudget == ⟨8, 1 <<< 22⟩

-- Direct and counted p−1 calls pin all three terminal gcd outcomes. Each
-- counted call costs one attempt and preserves `Rand`.
private def pMinusOneFound :=
  pMinusOneStage1Counted 299 2 5 (Hex.Rand.ofSeed 11)
private def pMinusOneMiss :=
  pMinusOneStage1Counted 25 2 2 (Hex.Rand.ofSeed 12)
private def pMinusOneWhole :=
  pMinusOneStage1Counted 15 4 2 (Hex.Rand.ofSeed 13)

#guard pMinusOneStage1 299 2 5 == .factor 13
#guard pMinusOneStage1 25 2 2 == .noFactor
-- Invalid inputs have the same public result without entering the gcd route.
#guard pMinusOneStage1 3 2 5 == .noFactor
#guard pMinusOneStage1 15 4 2 == .whole
#guard pMinusOneFound.result == .factor 13
#guard pMinusOneFound.attempts == 1
#guard pMinusOneFound.rand == Hex.Rand.ofSeed 11
#guard pMinusOneMiss.result == .noFactor
#guard pMinusOneMiss.attempts == 1
#guard pMinusOneMiss.rand == Hex.Rand.ofSeed 12
#guard pMinusOneWhole.result == .whole
#guard pMinusOneWhole.attempts == 1
#guard pMinusOneWhole.rand == Hex.Rand.ofSeed 13

#guard smoothBoundCap == 9999
#guard smoothBoundCap < primeTableBound
#guard smoothBound (primeTableBound + 1000) == smoothBoundCap

example {n base bound d : Nat} {r : Hex.Rand}
    (h : (pMinusOneStage1Counted n base bound r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n :=
  pMinusOneStage1Counted_spec h

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
#guard isPrime 100003 = true

-- Agreement with trial division on an initial segment.
#guard (List.range 2000).all fun n => isPrime n == isPrimeTrial n

-- Certificate checker: accepted shapes and one rejection per clause.
#guard checkPrime (.pock 7 [(2, 0, .small 3)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)]) = true
#guard checkPrime
    (.pock 4200127 [(2, 0, .pock 100003 [(2, 0, .small 2381)])]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 5), (3, 0, .small 3)]) = false
  -- distinct but noncanonical subjects
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
#guard checkPrime (.pock 7 [(2, 0, .small (2 ^ 4096))]) = false
  -- huge child subject is rejected at the first guarded product step
#guard checkPrime (.pock 31 [(3, 0, .small 5), (3, 0, .small 7)]) = false
  -- each power fits under 30, but the combined product would cross the bound
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

private def emptyFactorSearch : FactorSearch := fun _allocation n r =>
  ⟨⟨[], n⟩, (r.words 2).2, 2⟩

private def squarePrime : Nat := 1208925821721293454442757

private def squareFactor : Nat := 549755814367

private def squareFactorSearch : FactorSearch := fun allocation n r =>
  if n = squarePrime - 1 &&
      allocation.factorFuel = 2 * squarePrime.log2 + 8 then
    ⟨⟨[(2, 2), (squareFactor, 2)], 1⟩, (r.words 3).2, 3⟩
  else defaultFactorSearch allocation n r

#guard (match Internal.primeCertCountedUsing? squareFactorSearch
    defaultPrimeCertBudget squarePrime (Hex.Rand.ofSeed 5)
      (defaultPrimeFuel squarePrime) with
  | .ok success =>
      success.cert.raw.subject == squarePrime &&
        checkPrime success.cert.raw && success.attempts == 17 &&
          success.rand == ((Hex.Rand.ofSeed 5).words 22).2
  | .error _ => false)

-- An exhausted producer's accounting and advanced state are retained even
-- though its empty candidate cannot pass the final certificate checker.
#guard (match primeCertWith? emptyFactorSearch 2147483647
    (Hex.Rand.ofSeed 5) 1 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 2 &&
        failure.rand == ((Hex.Rand.ofSeed 5).words 2).2
  | .ok _ => false)

example {factor : FactorSearch} {n fuel : Nat} {r : Hex.Rand}
    {failure : PrimeCertFailure}
    (h : primeCertWith? factor n r fuel = .error failure)
    (hstop : failure.stop = .composite) : ¬ Prime n :=
  primeCertWith?_composite h hstop

-- The explicit default producer is the compatibility route used by
-- `primeCert?`; successful work and state are unchanged.
#guard (match Internal.primeCertCountedUsing?
    defaultFactorSearch defaultPrimeCertBudget 1000003 (Hex.Rand.ofSeed 3) 2 with
  | .ok success =>
      success.attempts == 8 &&
        success.rand == ((Hex.Rand.ofSeed 3).words 8).2
  | .error _ => false)

-- Table division leaves `100549 · 100049`; base-2 stage 1 at bound 64
-- splits it even with rho disabled. Acceptance still requires replay by the
-- ordinary certificate checker.
#guard (match Internal.primeCertCountedWith? ⟨0, 0⟩ 20119653803
    (Hex.Rand.ofSeed 17) (defaultPrimeFuel 20119653803) with
  | .ok success =>
      success.cert.raw.subject == 20119653803 && checkPrime success.cert.raw
  | .error _ => false)

-- Fixed verdict tiers run before recursive certificate fuel and do not consume
-- attempts or random state. A prime beyond the table still needs construction.
#guard (List.range 2).all fun fuel =>
  match primeCert? 4 (Hex.Rand.ofSeed 0) fuel with
  | .error failure =>
      failure.stop == .composite && failure.attempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 0
  | .ok _ => false
#guard (List.range 2).all fun fuel =>
  match primeCert? 97 (Hex.Rand.ofSeed 0) fuel with
  | .ok (cert, r) =>
      cert.raw.subject == 97 && checkPrime cert.raw && r == Hex.Rand.ofSeed 0
  | .error _ => false
#guard (List.range 2).all fun fuel =>
  match primeCert? 2147483649 (Hex.Rand.ofSeed 0) fuel with
  | .error failure =>
      failure.stop == .composite && failure.attempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 0
  | .ok _ => false
#guard (match primeCert? 2147483647 (Hex.Rand.ofSeed 0) 0 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 0
  | .ok _ => false)
#guard (match Internal.primeCertCounted? 2147483647
    (Hex.Rand.ofSeed 0) 1 with
  | .ok success =>
      success.attempts == 7 &&
        success.rand == ((Hex.Rand.ofSeed 0).words 7).2
  | .error _ => false)

-- Here `n - 1 = 2^20 * 100003 * 1000651`. With rho disabled, trial division
-- supplies `F = 2^20` but leaves the table-coprime composite cofactor
-- untouched. It is below the square-root Pocklington threshold and above the
-- cube-root threshold, so search must construct a `pock3` node and the ordinary
-- checker must replay it.
#guard (match Internal.primeCertCountedWith? ⟨0, 0⟩ 104929010073468929
    (Hex.Rand.ofSeed 23) (defaultPrimeFuel 104929010073468929) with
  | .ok success =>
      match success.cert.raw with
      | .pock3 n r s _ factors =>
          n == 104929010073468929 &&
            certProduct (n - 1) factors == some (2 ^ 20) &&
            2 ^ 20 * 2 ^ 20 < n && r == 397121 && s == 47716 &&
            checkPrime success.cert.raw
      | _ => false
  | .error _ => false)

-- The bounded decision remains fuel-insensitive below the table bound and
-- exposes the reordered verdict/construction boundary above its trial cutoff.
#guard (List.range 2).all fun fuel =>
  match isPrime? 4 (Hex.Rand.ofSeed 0) fuel with
  | .ok (verdict, r) => !verdict && r == Hex.Rand.ofSeed 0
  | .error _ => false
#guard (List.range 2).all fun fuel =>
  match isPrime? 97 (Hex.Rand.ofSeed 0) fuel with
  | .ok (verdict, r) => verdict && r == Hex.Rand.ofSeed 0
  | .error _ => false
-- This prime is above the table and below the trial threshold. The unchanged
-- state distinguishes the exact trial route from certificate construction.
#guard (match isPrime? 100003 (Hex.Rand.ofSeed 0) 0 with
  | .ok (verdict, r) => verdict && r == Hex.Rand.ofSeed 0
  | .error _ => false)
#guard (List.range 2).all fun fuel =>
  match isPrime? 2147483649 (Hex.Rand.ofSeed 0) fuel with
  | .ok (verdict, r) => !verdict && r == Hex.Rand.ofSeed 0
  | .error _ => false
#guard (match isPrime? 2147483647 (Hex.Rand.ofSeed 0) 0 with
  | .error failure =>
      failure.attempts == 0 && failure.rand == Hex.Rand.ofSeed 0
  | .ok _ => false)
#guard (match isPrime? 2147483647 (Hex.Rand.ofSeed 0) 1 with
  | .ok (verdict, r) =>
      verdict && r == ((Hex.Rand.ofSeed 0).words 7).2
  | .error _ => false)

-- Counted compatibility forms retain successful randomized work without
-- changing the ordinary pair-returning entry points.
#guard (match Internal.rhoFactorCounted? 3 (Hex.Rand.ofSeed 2) 8 with
  | .error failure =>
      failure.stop == .invalidInput && failure.attempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 2
  | .ok _ => false)
#guard (match Internal.rhoFactorCounted? 8 (Hex.Rand.ofSeed 2) 8 with
  | .ok success =>
      success.factor == 2 && success.attempts == 0 &&
        success.rand == Hex.Rand.ofSeed 2
  | .error _ => false)
#guard (match Internal.rhoFactorCounted? 9 (Hex.Rand.ofSeed 2) 8 with
  | .ok success =>
      success.factor == 3 && success.attempts == 4 &&
        success.rand == ((Hex.Rand.ofSeed 2).words 12).2
  | .error _ => false)

-- Trial extraction covers a typical mixed cofactor, a non-dividing edge, and
-- a deep adversarial valuation. The source binding keeps the last route linear
-- independently of CSE.
#guard Hex.Nat.Internal.trialExtractTrace 3 (3 ^ 7 * 10) == (7, 10)
#guard Hex.Nat.Internal.trialExtractTrace 0 17 == (0, 17)
set_option maxRecDepth 10000 in
#guard Hex.Nat.Internal.trialExtractTrace 2 (2 ^ 128) == (128, 1)

-- Pin the composition of caller allocation with the input-scaled Brent cap.
#guard Hex.Nat.Internal.rhoRestartFuel 9 (1 <<< 22) == 48
#guard Hex.Nat.Internal.rhoRestartFuel (2 ^ 200) (1 <<< 22) == (1 <<< 22)
#guard Hex.Nat.Internal.rhoRestartFuel 9 4 == 4

#guard (match Internal.primeCertCounted? 1000003
    (Hex.Rand.ofSeed 3) 16 with
  | .ok success =>
      success.attempts == 8 &&
        success.rand == ((Hex.Rand.ofSeed 3).words 8).2
  | .error _ => false)

-- Fuel one resolves table children and finds their witnesses before a later
-- child needs construction. The failure retains that successful work.
#guard (match Internal.primeCertCounted? 1000003
    (Hex.Rand.ofSeed 3) 1 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 2 &&
        failure.rand == ((Hex.Rand.ofSeed 3).words 2).2
  | .ok _ => false)

-- One more level constructs the remaining child and completes the parent.
#guard (match Internal.primeCertCounted? 1000003
    (Hex.Rand.ofSeed 3) 2 with
  | .ok success =>
      success.attempts == 8 &&
        success.rand == ((Hex.Rand.ofSeed 3).words 8).2
  | .error _ => false)

-- At fuel two, a deeper child consumes its randomized subtotal before
-- exhaustion; the parent retains both its earlier witness and that subtotal.
#guard (match Internal.primeCertCounted? 1000000007
    (Hex.Rand.ofSeed 3) 2 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 7 &&
        failure.rand == ((Hex.Rand.ofSeed 3).words 7).2
  | .ok _ => false)

-- Fuel three constructs that child and completes the parent.
#guard (match Internal.primeCertCounted? 1000000007
    (Hex.Rand.ofSeed 3) 3 with
  | .ok success =>
      success.attempts == 16 &&
        success.rand == ((Hex.Rand.ofSeed 3).words 16).2
  | .error _ => false)

-- This strong pseudoprime passes the fixed Miller--Rabin screen, then its
-- first certificate witness search consumes all 32 candidates. The retained
-- total also includes the preceding p−1 call and three rho restarts.
#guard (match Internal.primeCertCounted? 3317044064679887385961981
    (Hex.Rand.ofSeed 0) 2 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 36
  | .ok _ => false)

-- The elaborator's explicit rho allocation reaches a deterministic success
-- on the committed 512-bit boundary prime.
#guard (match Internal.primeCertCountedWith? ⟨2, 1 <<< 15⟩
    9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177
    (Hex.Rand.ofSeed 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177)
    (defaultPrimeFuel 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177) with
  | .ok success => success.attempts == 34
  | .error _ => false)

-- The same allocation fails promptly when both bounded restarts miss.
#guard (match Internal.primeCertCountedWith? ⟨2, 1 <<< 15⟩
    11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123
    (Hex.Rand.ofSeed 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123)
    (defaultPrimeFuel 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123) with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 10
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
#guard (match rhoFactor? 3 (Hex.Rand.ofSeed 1) 8 with
  | .error failure => failure.stop == .invalidInput
  | .ok _ => false)
#guard (match rhoFactor? 101 (Hex.Rand.ofSeed 1) 0 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 1
  | .ok _ => false)

-- Collisions for 11 and 13 share the cycle-boundary batch, so the route
-- returns their proper composite product rather than pretending it is prime.
#guard (Hex.Nat.Internal.rhoTrace 2431 1 1 32).factor == some 143

-- A whole-modulus batch is replayed and recovers the proper factor 3.
private def rhoRecoveryTrace : Hex.Nat.Internal.RhoTrace :=
  Hex.Nat.Internal.rhoTrace 9 1 0 32

#guard rhoRecoveryTrace.factor == some 3
#guard rhoRecoveryTrace.recoveries == 1

-- Seed 213 first draws the fixed pair `(c, x) = (71, 61)` modulo 91; the
-- route rejects it and advances to a non-fixed pair, consuming two words per
-- pair but still belonging to one semantic restart.
#guard (match Hex.Nat.Internal.rhoDrawTrace 91 (Hex.Rand.ofSeed 213) with
  | .ok (c, start, rejections, r) =>
      c == 37 && start == 6 && rejections == 1 &&
        r == ((Hex.Rand.ofSeed 213).words 4).2
  | .error _ => false)
-- Seed 40 first draws the globally degenerate offset `c = n - 2` and then
-- advances to the usable pair `(81, 74)`.
#guard (match Hex.Nat.Internal.rhoDrawTrace 91 (Hex.Rand.ofSeed 40) with
  | .ok (c, start, rejections, r) =>
      c == 81 && start == 74 && rejections == 1 &&
        r == ((Hex.Rand.ofSeed 40).words 4).2
  | .error _ => false)

-- An awkward non-power-of-two modulus above `2^64` draws both coordinates
-- from its full advertised range rather than the first word-sized slice.
private def wideDrawBound : Nat := 2 ^ 80 + 123

#guard (match Hex.Nat.Internal.rhoDrawTrace wideDrawBound (Hex.Rand.ofSeed 0) with
  | .ok (c, start, rejections, r) =>
      decide (2 ^ 64 < c) && decide (c < wideDrawBound) &&
        decide (2 ^ 64 < start) && decide (start < wideDrawBound) &&
        rejections == 0 && r == ((Hex.Rand.ofSeed 0).words 4).2
  | .error _ => false)

#guard (match Hex.Nat.Internal.witnessDrawTrace wideDrawBound
    (Hex.Rand.ofSeed 0) with
  | .ok (candidate, r) =>
      decide (2 ^ 64 < candidate) && decide (candidate < wideDrawBound - 1) &&
        r == ((Hex.Rand.ofSeed 0).words 2).2
  | .error _ => false)

-- The first candidate for the near-half-word bound is in the incomplete top
-- interval. One sampler try therefore exhausts after advancing exactly once.
#guard (match Hex.Nat.Internal.rhoDrawTrace (2 ^ 63 + 2)
    (Hex.Rand.ofSeed 0) (drawFuel := 1) with
  | .error (.sample (.exhausted attempts sampleRand), rejections, r) =>
      attempts == 1 && rejections == 0 &&
        sampleRand == ((Hex.Rand.ofSeed 0).words 1).2 && r == sampleRand
  | .error _ => false
  | .ok _ => false)

#guard (match Hex.Nat.Internal.witnessDrawTrace (2 ^ 63 + 4)
    (Hex.Rand.ofSeed 0) 1 with
  | .error (.exhausted attempts r) =>
      attempts == 1 && r == ((Hex.Rand.ofSeed 0).words 1).2
  | _ => false)

-- Giving the same semantic witness draw one more sampler try accepts the next
-- word; the internal rejection changes only the exact state, not the candidate
-- count owned by the caller.
#guard (match Hex.Nat.Internal.witnessDrawTrace (2 ^ 63 + 4)
    (Hex.Rand.ofSeed 0) 2 with
  | .ok (candidate, r) =>
      decide (2 ≤ candidate) && decide (candidate < 2 ^ 63 + 3) &&
        r == ((Hex.Rand.ofSeed 0).words 2).2
  | .error _ => false)

-- All eight drawn pairs are degenerate for this seed. Exhaustion returns the
-- state after those draws; no fabricated fallback pair enters Brent's loop.
#guard (match Hex.Nat.Internal.rhoDrawTrace 5 (Hex.Rand.ofSeed 72) with
  | .error (.pairs, rejections, r) =>
      rejections == 8 && r == ((Hex.Rand.ofSeed 72).words 16).2
  | .error _ => false
  | .ok _ => false)

-- The failed pair draw costs one restart, and the next allocated restart
-- continues from its exact advanced state instead of forfeiting the search.
#guard (match Internal.rhoFactorCountedWith? 5 (Hex.Rand.ofSeed 72) 2 1 with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 2 &&
        failure.rand == ((Hex.Rand.ofSeed 72).words 18).2
  | .ok _ => false)

-- A sampler stall likewise costs one witness candidate and advances into the
-- next candidate. This exercises the counted search branch, not just its draw.
#guard (match Hex.Nat.Internal.witnessSearchTrace (2 ^ 63 + 4) 2
    (Hex.Rand.ofSeed 0) 2 (drawFuel := 1) with
  | .error failure =>
      failure.stop == .exhausted && failure.attempts == 2 &&
        failure.rand == ((Hex.Rand.ofSeed 0).words 2).2
  | .ok _ => false)
#guard Hex.Nat.Internal.sampleFuel == 64
#guard Hex.Nat.Internal.rhoPairFuel == 8
#guard Hex.Nat.Internal.rhoRestartCap == 8

-- Miller-Rabin filter behaviour on the adversarial families.
#guard millerRabin 0 2 = false
#guard millerRabin 2 2 = true
#guard millerRabin 4 3 = false
#guard millerRabin 7 7 = true
#guard millerRabin 21 3 = false
#guard millerRabin 97 5 = true
#guard isProbablePrime 561 = false
#guard isProbablePrime 1373653 = false
#guard isProbablePrime 97 = true
#guard isProbablePrime 0 = false
#guard isProbablePrime 3215031751 = false
#guard isProbablePrime 2047 [2] = true
#guard isProbablePrime 2047 [2, 3] = false
#guard millerRabin 2047 2 = true
#guard millerRabin 2047 3 = false

-- Table and segments agree across the boundary.
#guard (primesIn 0 100).size = 25
#guard (primesIn 99950 100050).toList =
  [99961, 99971, 99989, 99991, 100003, 100019, 100043, 100049]
#guard (primesIn 99950 100050).toList.all fun p =>
  isTablePrime p == decide (p < 100000)

-- Next-prime success returns the least prime across the table, trial, and
-- certificate tiers.
#guard (match nextPrime? 90 (Hex.Rand.ofSeed 0) 8 with
  | .ok (p, _) =>
      p == 97 && (List.range' 91 6).all fun q => isPrimeTrial q == false
  | .error _ => false)
#guard (match nextPrime? 99991 (Hex.Rand.ofSeed 0) 16 with
  | .ok (p, _) => p == 100003
  | .error _ => false)
#guard (match nextPrime? 10000000 (Hex.Rand.ofSeed 0) 32,
    isPrime? 10000019 (Hex.Rand.ofSeed 0) 32 with
  | .ok (p, r), .ok (true, directRand) => p == 10000019 && r == directRand
  | _, _ => false)

-- Candidate-window exhaustion counts every proved-composite candidate but no
-- certificate attempts, and deterministic decisions leave the seed unchanged.
#guard (match nextPrime? 90 (Hex.Rand.ofSeed 0) 6 with
  | .error failure =>
      failure.rejectedCandidates == 6 && failure.certAttempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 0
  | .ok _ => false)

-- Certificate-tier composite verdicts also consume no randomized work, so
-- exhausting a window of them leaves the seed unchanged.
#guard (match nextPrime? 10000000 (Hex.Rand.ofSeed 0) 4 with
  | .error failure =>
      failure.rejectedCandidates == 4 && failure.certAttempts == 0 &&
        failure.rand == Hex.Rand.ofSeed 0
  | .ok _ => false)

-- The first candidate is undecided after nonzero randomized work. Its
-- certificate attempts and exact advanced state are retained, but it is not
-- counted as conclusively rejected.
#guard (match nextPrime? 1000000006 (Hex.Rand.ofSeed 3) 2,
    isPrime? 1000000007 (Hex.Rand.ofSeed 3) 2 with
  | .error failure, .error decisionFailure =>
      failure.rejectedCandidates == 0 && failure.certAttempts == 7 &&
        failure.certAttempts == decisionFailure.attempts &&
        failure.rand == decisionFailure.rand
  | _, _ => false)

-- A preceding deterministic composite and a later undecided candidate retain
-- both nonzero units without counting the undecided candidate as rejected.
#guard (match nextPrime? 1000000005 (Hex.Rand.ofSeed 3) 2,
    isPrime? 1000000007 (Hex.Rand.ofSeed 3) 2 with
  | .error failure, .error decisionFailure =>
      failure.rejectedCandidates == 1 && 0 < failure.certAttempts &&
        failure.certAttempts == decisionFailure.attempts &&
        failure.rand == decisionFailure.rand
  | _, _ => false)

-- Sieve representation and a complete small-bound comparison with the
-- independent trial-division decision route.
#guard (List.range 8).map numOfIndex = [1, 5, 7, 11, 13, 17, 19, 23]
#guard indexWidth 10000 = 3333
#guard numOfIndex (indexWidth 10000) ≥ 10000
#guard (List.range (indexWidth 100)).all fun t =>
  t == 0 || ((sieve 100 10).testBit t == isPrimeTrial (numOfIndex t))
#guard sieve 0 0 == 0
#guard bitsToList (sieve 25 5) 25 == [5, 7, 11, 13, 17, 19, 23]

-- Table bound edges, the largest entry, an above-bound prime, and empty
-- segment behavior.
#guard primeTable.size = 9592
#guard isTablePrime 2 = true
#guard isTablePrime 3 = true
#guard isTablePrime 4 = false
#guard isTablePrime 99991 = true
#guard isTablePrime 99999 = false
#guard isTablePrime 100003 = false
#guard (primesIn 90 100).toList = [97]
#guard primesIn 10 10 = #[]

-- The bounded certificate arm exposes exhaustion, while the total convenience
-- API takes its documented exact-trial fallback on the same input.
#guard (match isPrime? 10000019 (Hex.Rand.ofSeed 10000019) 0 with
  | .error _ => true
  | .ok _ => false)
#guard isPrime 10000019

-- Every Mathlib-free elaborator syntax form, across the table and certificate
-- tiers.
example : Hex.Nat.Prime 97 := primality 97
example : Hex.Nat.Prime 9973 := primality 9973
example : Hex.Nat.Prime 10007 := primality 10007
example : Hex.Nat.Prime 2147483647 := primality 2147483647
example : Hex.Nat.Prime 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177 :=
  primality 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177
example : Hex.Nat.Prime 101 := by primality
example : Hex.Nat.Prime 2147483647 := by primality
example : True := by
  primality 65537
  primality fermat : 257
  exact trivial

/-- error: primality: 561 is not prime (Miller-Rabin witness 2) -/
#guard_msgs in
example : Hex.Nat.Prime 561 := primality 561

/--
error: primality: certificate search for 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 exhausted after 10 attempts (seed 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123, recursive fuel 512, root factor fuel 1030; policy maximum 512 fuel at 512 bits, 2 rho restarts with 32768 steps each); no total primality decision was attempted
-/
#guard_msgs in
example : Hex.Nat.Prime 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 :=
  primality 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123

/--
error: primality: input has 513 bits; the enforced policy supports at most 512 bits; raising the ceiling requires new end-to-end benchmark evidence
-/
#guard_msgs in
example : Hex.Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 :=
  primality 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096

/--
error: primality: the goal
  Prime (2 + 2)
is not about a natural-number numeral
-/
#guard_msgs in
example : Hex.Nat.Prime (2 + 2) := by primality

/-- error: primality: expected a natural-number term after the colon -/
#guard_msgs in
example : True := by primality h :

/-! The generator emits a complete, batch-count-independent one-batch replay
block. The committed four-batch path is regenerated separately because its
literal is intentionally large. -/

/--
info: @[expose]
def primeTableBound : Nat := 25

@[expose]
def primeTable : Array Nat :=
  #[2, 3, 5, 7, 11, 13, 17, 19, 23]

-- #rebuild_primeTable 25 5 1

private def sieveState1 : Nat :=
  254

private abbrev sieveStateFinal : Nat := sieveState1

private theorem sieveChunk1 :
    sieveGoRange 8 1 1 (sieveInit 8) = sieveState1 := by
  decide +kernel

private theorem sieve_eq_final : sieve 25 5 = sieveStateFinal := by
  show sieveGoRange 8 1 1 (sieveInit 8) = _
  exact sieveChunk1

private theorem primeTable_eq_bits :
    primeTable = (2 :: 3 :: bitsToList sieveStateFinal 25).toArray := by
  decide +kernel
-/
#guard_msgs in
#rebuild_primeTable 25 5 1
