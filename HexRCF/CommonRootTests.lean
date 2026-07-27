/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Carrier
public import HexRCF.CommonRoot
import all HexRCF.CommonRoot

public section

/-! Regression tests for cached common-root certificates. -/

namespace Hex.RCF.CommonRootTests

open HexRealRootsMathlib

private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]
private def minusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int)]
private def minusTwo : ZPoly := DensePoly.ofCoeffs #[(-2 : Int)]
private def twiceX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 2]
private def xMinusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 1]
private def xPlusOne : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 1]

private def quadReplay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def minusReplay : SturmReplay where
  chain := #[xMinusOne, one]
  derivScale := 1
  steps := #[]

private def sentence : Sentence := .forallReal (.atom ⟨quad, .ge⟩)

private def carrier : CarrierCert where
  carrier := quad
  repeated := one
  derivPart := twiceX
  factorScale := 1
  derivScale := 1
  replay := quadReplay

private def negHalf : Dyadic := Dyadic.ofInt (-1) >>> (1 : Int)
private def half : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)

private def isolations : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) negHalf (by decide),
  DyadicInterval.mk half (Dyadic.ofInt 2) (by decide)]⟩

private theorem carrier_ok : carrier.check sentence = true := by decide
private theorem strict_ok : isolations.checkStrict carrier.replay = true := by decide

/-! The shared-factor case has the right carrier root and not the left one. -/

private def shared : CommonRootCert where
  gcd := xMinusOne
  atomFactor := one
  carrierFactor := xPlusOne
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some minusReplay

private theorem shared_ok : shared.check xMinusOne quad = true := by decide

example : shared.hasRoot isolations.intervals[0] = false := by decide
example : shared.hasRoot isolations.intervals[1] = true := by decide

example (i : Fin isolations.intervals.size) :
    shared.hasRoot isolations.intervals[i] = true ↔
      (toPolyℝ xMinusOne).IsRoot
        ((isolations.rootModel (CarrierCert.replay_of_check carrier_ok) strict_ok).root i) :=
  shared.hasRoot_model_iff
    (CarrierCert.replay_of_check carrier_ok) strict_ok shared_ok i

/-! A constant gcd certifies a coprime atom/carrier pair without a replay. -/

private def coprime : CommonRootCert where
  gcd := one
  atomFactor := x
  carrierFactor := quad
  atomCoeff := x
  carrierCoeff := minusOne
  scale := 1
  replay := none

private theorem coprime_ok : coprime.check x quad = true := by decide

example : coprime.hasRoot isolations.intervals[0] = false := by decide
example : coprime.hasRoot isolations.intervals[1] = false := by decide

example (i : Fin isolations.intervals.size) :
    coprime.hasRoot isolations.intervals[i] = true ↔
      (toPolyℝ x).IsRoot
        ((isolations.rootModel (CarrierCert.replay_of_check carrier_ok) strict_ok).root i) :=
  coprime.hasRoot_model_iff
    (CarrierCert.replay_of_check carrier_ok) strict_ok coprime_ok i

/-! Equal atom and carrier polynomials share every carrier root. -/

private def equal : CommonRootCert where
  gcd := quad
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some quadReplay

private theorem equal_ok : equal.check quad quad = true := by decide

example : equal.hasRoot isolations.intervals[0] = true := by decide
example : equal.hasRoot isolations.intervals[1] = true := by decide

example (z : ℝ) :
    (toPolyℝ equal.gcd).IsRoot z ↔
      (toPolyℝ quad).IsRoot z ∧ (toPolyℝ quad).IsRoot z :=
  equal.isRoot_iff equal_ok z

/-! Every independently checked identity and replay branch rejects tampering. -/

private def badAtomFactor : CommonRootCert :=
  { shared with atomFactor := x }

private def badCarrierFactor : CommonRootCert :=
  { shared with carrierFactor := one }

private def badBezout : CommonRootCert :=
  { shared with atomCoeff := 0 }

private def badScale : CommonRootCert :=
  { shared with scale := 0 }

private def missingReplay : CommonRootCert :=
  { shared with replay := none }

private def extraReplay : CommonRootCert :=
  { coprime with replay := some quadReplay }

private def malformedReplay : CommonRootCert :=
  { shared with replay := some { minusReplay with derivScale := 2 } }

private def wrongReplayHead : CommonRootCert :=
  { shared with replay := some quadReplay }

private def zeroGcd : CommonRootCert :=
  { coprime with gcd := 0 }

/-- Both factor identities accept this proper divisor of the actual gcd; only
the scaled Bezout identity rules it out. -/
private def shrunkGcd : CommonRootCert where
  gcd := xMinusOne
  atomFactor := xPlusOne
  carrierFactor := xPlusOne
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some minusReplay

/-- A genuine denominator-clearing scale exercises a nonunit Bezout scale in
the constant-gcd branch. -/
private def scaled : CommonRootCert where
  gcd := one
  atomFactor := twiceX
  carrierFactor := quad
  atomCoeff := x
  carrierCoeff := minusTwo
  scale := 2
  replay := none

example : badAtomFactor.check xMinusOne quad = false := by decide
example : badCarrierFactor.check xMinusOne quad = false := by decide
example : badBezout.check xMinusOne quad = false := by decide
example : badScale.check xMinusOne quad = false := by decide
example : missingReplay.check xMinusOne quad = false := by decide
example : extraReplay.check x quad = false := by decide
example : malformedReplay.check xMinusOne quad = false := by decide
example : wrongReplayHead.check xMinusOne quad = false := by decide
example : zeroGcd.check x quad = false := by decide
example : shrunkGcd.check quad quad = false := by decide
example : shrunkGcd.checkReplay = true := by decide
example : DensePoly.beqCoeffs quad (shrunkGcd.gcd * shrunkGcd.atomFactor) = true := by
  decide
example : DensePoly.beqCoeffs quad (shrunkGcd.gcd * shrunkGcd.carrierFactor) = true := by
  decide
example : scaled.check twiceX quad = true := by decide
example : ({ scaled with scale := 3 }).check twiceX quad = false := by decide

end Hex.RCF.CommonRootTests
