/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor

/-!
Kernel-replay probes for `hex-int-factor` checkers and factor-list consumers.

Every theorem is discharged by kernel reduction alone (`decide +kernel`). The
cases are deliberately bounded: they exercise reducer exposure and the
canonical certified-factor routes without pricing search or divisor sorting.
This module is build-only and is compiled by the main CI job.
-/

namespace HexBench.IntFactorKernel

open Hex.Nat

private def raw360 : Factorization :=
  ⟨360, [⟨3, .small 2⟩, ⟨2, .small 3⟩, ⟨1, .small 5⟩]⟩

private def corruptProduct : Factorization :=
  ⟨361, [⟨3, .small 2⟩, ⟨2, .small 3⟩, ⟨1, .small 5⟩]⟩

private def checked360 : CheckedFactorization 360 :=
  ⟨raw360, rfl, by decide +kernel⟩

private def raw30 : Factorization :=
  ⟨30, [⟨1, .small 2⟩, ⟨1, .small 3⟩, ⟨1, .small 5⟩]⟩

private def checked30 : CheckedFactorization 30 :=
  ⟨raw30, rfl, by decide +kernel⟩

private def checkedPow64 : CheckedFactorization (2 ^ 64) :=
  ⟨⟨2 ^ 64, [⟨64, .small 2⟩]⟩, rfl, by decide +kernel⟩

private def checkedHugeTau :
    CheckedFactorization ((2 * 3 * 5 * 7 * 11 * 13) ^ 100) :=
  ⟨⟨(2 * 3 * 5 * 7 * 11 * 13) ^ 100,
    [⟨100, .small 2⟩, ⟨100, .small 3⟩, ⟨100, .small 5⟩,
      ⟨100, .small 7⟩, ⟨100, .small 11⟩, ⟨100, .small 13⟩]⟩,
    rfl, by decide +kernel⟩

private def rawPock7 : Factorization :=
  ⟨7, [⟨1, .pock 7 [(2, 0, .small 3)]⟩]⟩

private def orderTwoModSeven : OrderCert :=
  ⟨2, 7, 3, ⟨3, [⟨1, .small 3⟩]⟩⟩

private def corruptOrder : OrderCert :=
  ⟨2, 7, 2, ⟨2, [⟨1, .small 2⟩]⟩⟩

/- The final entry is a 61-bit prime, so this 1-through-10 ladder exercises
both table leaves and an above-table Pocklington certificate while keeping the
factor subjects in canonical ascending order. -/
private def cert61 : PrimeCert :=
  .pock 1945555039024054273
    [(891154892214722695, 55, .small 2),
     (110189291828549774, 2, .small 3)]

private def replayCerts : List PrimeCert :=
  [.small 2, .small 3, .small 5, .small 7, .small 11,
   .small 13, .small 17, .small 19, .small 23, cert61]

private def replayFactors (count : Nat) : List PrimePower :=
  (replayCerts.take count).map fun cert => ⟨1, cert⟩

private def replayCase (count : Nat) : Factorization :=
  let factors := replayFactors count
  ⟨(factors.map (·.prime)).prod, factors⟩

theorem factorizationValid : checkFactorization raw360 = true := by
  decide +kernel

theorem factorizationCorrupt : checkFactorization corruptProduct = false := by
  decide +kernel

theorem factorizationPocklington : checkFactorization rawPock7 = true := by
  decide +kernel

theorem replay1 : checkFactorization (replayCase 1) = true := by
  decide +kernel

theorem replay2 : checkFactorization (replayCase 2) = true := by
  decide +kernel

theorem replay3 : checkFactorization (replayCase 3) = true := by
  decide +kernel

theorem replay4 : checkFactorization (replayCase 4) = true := by
  decide +kernel

theorem replay5 : checkFactorization (replayCase 5) = true := by
  decide +kernel

theorem replay6 : checkFactorization (replayCase 6) = true := by
  decide +kernel

theorem replay7 : checkFactorization (replayCase 7) = true := by
  decide +kernel

theorem replay8 : checkFactorization (replayCase 8) = true := by
  decide +kernel

theorem replay9 : checkFactorization (replayCase 9) = true := by
  decide +kernel

theorem replay10 : checkFactorization (replayCase 10) = true := by
  decide +kernel

theorem orderValid : checkOrder orderTwoModSeven = true := by
  decide +kernel

theorem orderCorrupt : checkOrder corruptOrder = false := by
  decide +kernel

theorem orderNotMinimal :
    checkOrder ⟨2, 7, 6, ⟨6, [⟨1, .small 2⟩, ⟨1, .small 3⟩]⟩⟩ = false := by
  decide +kernel

theorem entrySum : sigmaEntry ⟨2, .small 3⟩ 1 = 13 := by
  decide +kernel

theorem divisorCount : numDivisors checkedHugeTau = 101 ^ 6 := by
  decide +kernel

theorem divisorCountThroughSigma : sigma checkedHugeTau 0 = 101 ^ 6 := by
  decide +kernel

theorem divisorSum : sigma checkedPow64 1 = 2 ^ 65 - 1 := by
  decide +kernel

theorem totientValue : totient checkedPow64 = 2 ^ 63 := by
  decide +kernel

theorem radicalValue : radical checked360 = 30 := by
  decide +kernel

theorem squarefreePartValue : squarefreePart checkedHugeTau = 1 := by
  decide +kernel

theorem squareDivisorValue : squareDivisor checkedPow64 = 2 ^ 32 := by
  decide +kernel

theorem squarefreeFalse : isSquarefree checked360 = false := by
  decide +kernel

theorem squarefreeTrue : isSquarefree checked30 = true := by
  decide +kernel

theorem carmichaelTwoPower : carmichaelPrimePower ⟨3, .small 2⟩ = 2 := by
  decide +kernel

theorem carmichaelValue : carmichael checked360 = 12 := by
  decide +kernel

end HexBench.IntFactorKernel
