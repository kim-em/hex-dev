/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor

/-! Route-level and checker regression tests for integer factorization. -/

open Hex Hex.Nat

set_option maxRecDepth 20000

private def raw12 : Factorization :=
  ⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩

private def checked12 : CheckedFactorization 12 :=
  ⟨raw12, rfl, by decide⟩

private def checked1 : CheckedFactorization 1 :=
  ⟨⟨1, []⟩, rfl, by decide⟩

private def checked64 : CheckedFactorization 64 :=
  ⟨⟨64, [⟨6, .small 2⟩]⟩, rfl, by decide⟩

private def checked10800 : CheckedFactorization 10800 :=
  ⟨⟨10800, [⟨4, .small 2⟩, ⟨3, .small 3⟩, ⟨2, .small 5⟩]⟩, rfl, by decide⟩

private def checkedPow64 : CheckedFactorization (2 ^ 64) :=
  ⟨⟨2 ^ 64, [⟨64, .small 2⟩]⟩, rfl, by decide⟩

private def checkedHugeTau :
    CheckedFactorization ((2 * 3 * 5 * 7 * 11 * 13) ^ 100) :=
  ⟨⟨(2 * 3 * 5 * 7 * 11 * 13) ^ 100,
    [⟨100, .small 2⟩, ⟨100, .small 3⟩, ⟨100, .small 5⟩,
      ⟨100, .small 7⟩, ⟨100, .small 11⟩, ⟨100, .small 13⟩]⟩,
    rfl, by decide⟩

#guard checkFactorization raw12
#guard !checkFactorization ⟨12, [⟨1, .small 4⟩, ⟨1, .small 3⟩]⟩
#guard !checkFactorization ⟨12, [⟨1, .small 2⟩, ⟨1, .small 3⟩]⟩
#guard !checkFactorization ⟨12, [⟨1, .small 2⟩, ⟨1, .small 2⟩, ⟨1, .small 3⟩]⟩
#guard !checkFactorization ⟨12, [⟨0, .small 2⟩, ⟨1, .small 3⟩]⟩
#guard !checkFactorization ⟨12, [⟨1, .small 3⟩, ⟨2, .small 2⟩]⟩

#guard divisors checked1 == #[1]
#guard numDivisors checked1 == 1
#guard divisors checked12 == #[1, 2, 3, 4, 6, 12]
#guard numDivisors checked12 == 6
#guard divisors checked64 == #[1, 2, 4, 8, 16, 32, 64]
#guard numDivisors checked64 == 7
#guard (divisors checked10800).size == 60
#guard numDivisors checked10800 == 60
-- This subject is far beyond any feasible scan through `List.range n`.
#guard numDivisors checkedPow64 == 65
-- `101 ^ 6` divisors rules out computing the count by enumeration.
#guard numDivisors checkedHugeTau == 101 ^ 6
example : numDivisors checkedHugeTau = 101 ^ 6 := by decide +kernel
-- `sigmaEntry` remains total even for uncertified `PrimePower` values.
#guard sigmaEntry ⟨3, .small 0⟩ 1 == 1
#guard sigmaEntry ⟨3, .small 1⟩ 1 == 4
#guard sigma checked1 0 == 1
#guard sigma checked12 0 == 6
#guard sigma checked12 1 == 28
#guard sigma checked12 2 == 210
#guard sigma checked64 1 == 127
#guard sigma checked64 2 == 5461
#guard sigma checked10800 1 == 38440
#guard sigma checkedPow64 1 == 2 ^ 65 - 1
-- The trillion-divisor input demonstrates that `sigma` never enumerates them;
-- the independent modular value also rejects a constant nonzero result.
#guard sigma checkedHugeTau 1 % 1000000007 == 898750509
example : sigma checkedHugeTau 0 = 101 ^ 6 := by decide +kernel
example : sigma checkedPow64 1 = 2 ^ 65 - 1 := by decide +kernel
#guard totient checked12 == 4
#guard radical checked12 == 6
#guard squarefreePart checked12 == 3
#guard squareDivisor checked12 == 2
#guard !isSquarefree checked12

#guard (smallCandidate (2 ^ 20)).route == .perfectPower
#guard (smallCandidate (3 ^ 13)).route == .perfectPower
#guard (smallCandidate (1000003 ^ 2)).route == .perfectPower
#guard (smallCandidate ((6 ^ 5) ^ 3)).route == .perfectPower

#guard pMinusOneStage1 15 2 2 == .factor 3
#guard pMinusOneStage1 25 2 2 == .noFactor
#guard pMinusOneStage1 15 4 2 == .whole

-- ECM's three stage-boundary gcd outcomes are observably distinct.
#guard ecmStage1 191 6 2 == .noFactor
#guard ecmStage1 6 7 2 == .factor 2
#guard ecmStage1 4 6 2 == .whole

#guard (match rhoSplit? 91 (Rand.ofSeed 1) 16 with
  | .ok (d, _) => decide (1 < d) && decide (d < 91) && 91 % d == 0
  | .error _ => false)

#guard checkOrder ⟨2, 7, 3, ⟨3, [⟨1, .small 3⟩]⟩⟩

#guard (match cyclotomicSplit? 2 6 .minus with
  | some parts => parts.map (·.value) == [1, 3, 7, 3]
  | none => false)
#guard (match cyclotomicSplit? 2 6 .plus with
  | some parts => parts.map (·.value) == [5, 13]
  | none => false)

#guard (match factorPowerWithRoute? 2 6 .minus (Rand.ofSeed 1) with
  | .ok (_, _, route) => route == .cyclotomic
  | .error _ => false)

#guard (match factor? 4826808 (Rand.ofSeed 7) with
  | .ok (F, _) =>
      F.raw.factors.map (fun e => (e.prime, e.exponent)) ==
        [(2, 3), (3, 2), (7, 1), (61, 1), (157, 1)]
  | .error _ => false)

#guard (match factor? 0 (Rand.ofSeed 0) with
  | .error f => f.stop == .zero
  | .ok _ => false)
