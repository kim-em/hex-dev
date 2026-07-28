/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SignMatrix

public section

/-! Regression tests for exact signs, package alignment, and cell formulas. -/

namespace Hex.RCF.SignMatrixTests

open HexRealRootsMathlib

private def zero : ZPoly := 0
private def minusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int)]
private def minusTwo : ZPoly := DensePoly.ofCoeffs #[(-2 : Int)]
private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def twiceX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 2]
private def fourX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 4]
private def xMinusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 1]
private def xPlusOne : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 1]
private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def posQuad : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 0, 1]
private def threeXPlusOne : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 3]

/-! Three-way exact evaluation and all eighteen comparison outcomes. -/

example : evalSign x (Dyadic.ofInt (-1)) = .neg := by decide
example : evalSign x 0 = .zero := by decide
example : evalSign x (Dyadic.ofInt 1) = .pos := by decide

example : Cmp.lt.evalSign .neg = true := by decide
example : Cmp.le.evalSign .neg = true := by decide
example : Cmp.eq.evalSign .neg = false := by decide
example : Cmp.ge.evalSign .neg = false := by decide
example : Cmp.gt.evalSign .neg = false := by decide
example : Cmp.ne.evalSign .neg = true := by decide
example : Cmp.lt.evalSign .zero = false := by decide
example : Cmp.le.evalSign .zero = true := by decide
example : Cmp.eq.evalSign .zero = true := by decide
example : Cmp.ge.evalSign .zero = true := by decide
example : Cmp.gt.evalSign .zero = false := by decide
example : Cmp.ne.evalSign .zero = false := by decide
example : Cmp.lt.evalSign .pos = false := by decide
example : Cmp.le.evalSign .pos = false := by decide
example : Cmp.eq.evalSign .pos = false := by decide
example : Cmp.ge.evalSign .pos = true := by decide
example : Cmp.gt.evalSign .pos = true := by decide
example : Cmp.ne.evalSign .pos = true := by decide

/-! Every Boolean connective is executable in both truth states. -/

example : Formula.evalSigns (fun _ => none) (.not .tt) = some false := by decide
example : Formula.evalSigns (fun _ => none) (.not .ff) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.and .ff .ff) = some false := by decide
example : Formula.evalSigns (fun _ => none) (.and .ff .tt) = some false := by decide
example : Formula.evalSigns (fun _ => none) (.and .tt .ff) = some false := by decide
example : Formula.evalSigns (fun _ => none) (.and .tt .tt) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.or .ff .ff) = some false := by decide
example : Formula.evalSigns (fun _ => none) (.or .ff .tt) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.or .tt .ff) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.or .tt .tt) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.imp .ff .ff) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.imp .ff .tt) = some true := by decide
example : Formula.evalSigns (fun _ => none) (.imp .tt .ff) = some false := by decide
example : Formula.evalSigns (fun _ => none) (.imp .tt .tt) = some true := by decide

private def missing : Formula := .atom ⟨x, .eq⟩
example : Formula.evalSigns (fun _ => none) (.and .ff missing) = none := by decide
example : Formula.evalSigns (fun _ => none) (.or .tt missing) = none := by decide
example : Formula.evalSigns (fun _ => none) (.imp .ff missing) = none := by decide
example : Formula.evalSigns (fun _ => none) (.not missing) = none := by decide
example : Formula.evalSigns (fun _ => none) (.and missing .ff) = none := by decide

/-! A two-root carrier exercises shared roots and nonzero root transfer. -/

private def quadReplay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def minusReplay : SturmReplay where
  chain := #[xMinusOne, one]
  derivScale := 1
  steps := #[]

private def sharedFormula : Formula :=
  .and (.atom ⟨quad, .eq⟩) (.atom ⟨xMinusOne, .ne⟩)

private def sharedSentence : Sentence := .forallReal sharedFormula

/-- The atom product is `(x - 1)^2 * (x + 1)`, so the repeated factor is
`x - 1` and its derivative quotient is `3*x + 1`. -/
private def sharedCarrier : CarrierCert where
  carrier := quad
  repeated := xMinusOne
  derivPart := threeXPlusOne
  factorScale := 1
  derivScale := 1
  replay := quadReplay

private def negHalf : Dyadic := Dyadic.ofInt (-1) >>> (1 : Int)
private def half : Dyadic := Dyadic.ofInt 1 >>> (1 : Int)

private def twoRoots : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-2)) negHalf (by decide),
  DyadicInterval.mk half (Dyadic.ofInt 2) (by decide)]⟩

private def equalQuad : CommonRootCert where
  gcd := quad
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some quadReplay

private def sharedMinus : CommonRootCert where
  gcd := xMinusOne
  atomFactor := one
  carrierFactor := xPlusOne
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some minusReplay

private def sharedMatrix : SignMatrixCert :=
  ⟨[equalQuad, sharedMinus]⟩

private theorem sharedCarrier_ok : sharedCarrier.check sharedSentence = true := by decide
private theorem twoRoots_ok : twoRoots.checkStrict sharedCarrier.replay = true := by decide
private theorem sharedMatrix_ok : sharedMatrix.check sharedSentence sharedCarrier = true := by
  decide

example : dedupPolys sharedSentence.polys = [quad, xMinusOne] := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.open ⟨0, by decide⟩)
    quad = some .pos := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.root ⟨0, by decide⟩)
    quad = some .zero := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.open ⟨1, by decide⟩)
    quad = some .neg := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.root ⟨1, by decide⟩)
    quad = some .zero := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.open ⟨2, by decide⟩)
    quad = some .pos := by decide

/-- `x - 1` does not vanish at the left carrier root, so its negative sign is
transferred from the left open sample; it vanishes at the right root. -/
example : sharedMatrix.sign? sharedSentence twoRoots (.root ⟨0, by decide⟩)
    xMinusOne = some .neg := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.open ⟨0, by decide⟩)
    xMinusOne = some .neg := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.open ⟨1, by decide⟩)
    xMinusOne = some .neg := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.root ⟨1, by decide⟩)
    xMinusOne = some .zero := by decide
example : sharedMatrix.evalCell? sharedSentence twoRoots
    (.root ⟨0, by decide⟩) = some true := by decide
example : sharedMatrix.evalCell? sharedSentence twoRoots
    (.root ⟨1, by decide⟩) = some false := by decide
example : sharedMatrix.evalCell? sharedSentence twoRoots
    (.open ⟨0, by decide⟩) = some false := by decide
example : (⟨[]⟩ : SignMatrixCert).evalCell? sharedSentence twoRoots
    (.root ⟨0, by decide⟩) = none := by decide

example (c : Cell twoRoots.intervals.size) :
    ∃ value, sharedMatrix.evalCell? sharedSentence twoRoots c = some value ∧
      ∀ z, Cell.Sem
        (twoRoots.rootModel (CarrierCert.replay_of_check sharedCarrier_ok)
          twoRoots_ok) c z → (value = true ↔ sharedFormula.toProp z) :=
  sharedMatrix.evalCell_spec sharedCarrier_ok twoRoots_ok sharedMatrix_ok c

/-! Alignment is exact: missing, extra, swapped, and malformed packages fail. -/

example : (⟨[equalQuad]⟩ : SignMatrixCert).check
    sharedSentence sharedCarrier = false := by decide
example : (⟨[equalQuad, sharedMinus, sharedMinus]⟩ : SignMatrixCert).check
    sharedSentence sharedCarrier = false := by decide
example : (⟨[sharedMinus, equalQuad]⟩ : SignMatrixCert).check
    sharedSentence sharedCarrier = false := by decide
example : (⟨[equalQuad, { sharedMinus with scale := 0 }]⟩ : SignMatrixCert).check
    sharedSentence sharedCarrier = false := by decide

private def repeatedSentence : Sentence :=
  .forallReal (.and (.atom ⟨quad, .le⟩) (.atom ⟨quad, .ge⟩))
private def repeatedCarrier : CarrierCert :=
  { sharedCarrier with repeated := quad, derivPart := fourX }
private def repeatedMatrix : SignMatrixCert := ⟨[equalQuad]⟩

example : dedupPolys repeatedSentence.polys = [quad] := by decide
example : dedupPolys [quad, xMinusOne, quad] = [quad, xMinusOne] := by decide
example : repeatedCarrier.check repeatedSentence = true := by decide
example : repeatedMatrix.check repeatedSentence repeatedCarrier = true := by decide

/-! Constants in mixed formulas bypass common-root packages on every cell. -/

private def mixedFormula : Formula :=
  .and (.atom ⟨quad, .ge⟩)
    (.and (.atom ⟨minusTwo, .lt⟩)
      (.and (.atom ⟨zero, .eq⟩) (.atom ⟨one, .gt⟩)))
private def mixedSentence : Sentence := .forallReal mixedFormula
private def mixedCarrier : CarrierCert :=
  { sharedCarrier with repeated := one, derivPart := twiceX }
private def mixedMatrix : SignMatrixCert := ⟨[equalQuad]⟩

example : mixedCarrier.check mixedSentence = true := by decide
example : mixedMatrix.check mixedSentence mixedCarrier = true := by decide
example : mixedMatrix.sign? mixedSentence twoRoots (.root ⟨0, by decide⟩)
    minusTwo = some .neg := by decide
example : mixedMatrix.sign? mixedSentence twoRoots (.root ⟨1, by decide⟩)
    zero = some .zero := by decide
example : mixedMatrix.sign? mixedSentence twoRoots (.open ⟨2, by decide⟩)
    one = some .pos := by decide

private def constantFormula : Formula :=
  .and (.atom ⟨minusTwo, .lt⟩)
    (.and (.atom ⟨zero, .eq⟩) (.atom ⟨one, .gt⟩))

example : constantFormula.evalConstants? = some true := by decide

private def falseConstantFormula : Formula := .atom ⟨one, .lt⟩
example : falseConstantFormula.evalConstants? = some false := by decide

/-! Zero-root and singleton carriers cover the remaining cell shapes. -/

private def posReplay : SturmReplay where
  chain := #[posQuad, x, minusOne]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def posSentence : Sentence := .forallReal (.atom ⟨posQuad, .gt⟩)
private def posCarrier : CarrierCert where
  carrier := posQuad
  repeated := one
  derivPart := twiceX
  factorScale := 1
  derivScale := 1
  replay := posReplay
private def posCommon : CommonRootCert where
  gcd := posQuad
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some posReplay
private def noRoots : IsolationCert := ⟨#[]⟩
private def posMatrix : SignMatrixCert := ⟨[posCommon]⟩

example : posCarrier.check posSentence = true := by decide
example : noRoots.checkStrict posReplay = true := by decide
example : posMatrix.check posSentence posCarrier = true := by decide
example : posMatrix.sign? posSentence noRoots (.open ⟨0, by decide⟩)
    posQuad = some .pos := by decide
/-- Defensive failure for an atom inconsistent with the claimed root-free
carrier cell. -/
example : openSign? x noRoots ⟨0, by decide⟩ = none := by decide

/-- A nonzero constant gcd takes the nonvanishing root-sign transfer branch. -/
private def coprimePos : CommonRootCert where
  gcd := one
  atomFactor := posQuad
  carrierFactor := quad
  atomCoeff := one
  carrierCoeff := minusOne
  scale := 2
  replay := none

example : coprimePos.check posQuad quad = true := by decide
example : rootSign? posQuad coprimePos twoRoots ⟨0, by decide⟩ = some .pos := by decide
example : rootSign? posQuad coprimePos twoRoots ⟨1, by decide⟩ = some .pos := by decide
example : sharedMatrix.sign? sharedSentence twoRoots (.root ⟨0, by decide⟩)
    posQuad = none := by decide

private def linearReplay : SturmReplay where
  chain := #[x, one]
  derivScale := 1
  steps := #[]
private def linearSentence : Sentence := .forallReal (.atom ⟨x, .eq⟩)
private def linearCarrier : CarrierCert where
  carrier := x
  repeated := one
  derivPart := one
  factorScale := 1
  derivScale := 1
  replay := linearReplay
private def linearCommon : CommonRootCert where
  gcd := x
  atomFactor := one
  carrierFactor := one
  atomCoeff := one
  carrierCoeff := 0
  scale := 1
  replay := some linearReplay
private def singleton : IsolationCert := ⟨#[
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 1) (by decide)]⟩
private def linearMatrix : SignMatrixCert := ⟨[linearCommon]⟩

example : linearCarrier.check linearSentence = true := by decide
example : singleton.checkStrict linearReplay = true := by decide
example : linearMatrix.check linearSentence linearCarrier = true := by decide
example : linearMatrix.sign? linearSentence singleton (.open ⟨0, by decide⟩)
    x = some .neg := by decide
example : linearMatrix.sign? linearSentence singleton (.root ⟨0, by decide⟩)
    x = some .zero := by decide
example : linearMatrix.sign? linearSentence singleton (.open ⟨1, by decide⟩)
    x = some .pos := by decide

end Hex.RCF.SignMatrixTests
