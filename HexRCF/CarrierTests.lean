/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Carrier
import all HexRCF.Carrier

public section

/-! Regression tests for atom collection and square-free carrier checking. -/

namespace Hex.RCF.CarrierTests

private def quad : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
private def x : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 1]
private def one : ZPoly := DensePoly.ofCoeffs #[(1 : Int)]
private def twiceX : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 2]

private def replay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

private def formula : Formula :=
  .and (.atom ⟨0, .eq⟩) (.or (.atom ⟨quad, .ge⟩) (.atom ⟨one, .ne⟩))

private def sentence : Sentence := .forallReal formula

private def cert : CarrierCert where
  carrier := quad
  repeated := one
  derivPart := twiceX
  factorScale := 1
  derivScale := 1
  replay := replay

/-- Constant atoms are retained in the formula but omitted from the carrier. -/
example : sentence.polys.length = 1 := by decide
example : cert.check sentence = true := by decide

example (r : ℝ) :
    (HexRealRootsMathlib.toPolyℝ cert.carrier).IsRoot r ↔
      ∃ p ∈ sentence.polys, (HexRealRootsMathlib.toPolyℝ p).IsRoot r :=
  cert.isRoot_iff_atom (by decide) r

private def extraSentence : Sentence :=
  .forallReal (.and formula (.atom ⟨x, .eq⟩))

private def badRepeated : CarrierCert := { cert with repeated := 0 }
private def badFactorScale : CarrierCert := { cert with factorScale := 0 }
private def badDerivScale : CarrierCert := { cert with derivScale := 0 }
private def badFactor : CarrierCert := { cert with repeated := x }
private def badDerivative : CarrierCert := { cert with derivPart := x }
private def badReplay : CarrierCert :=
  { cert with replay := { replay with derivScale := 3 } }

/-- Changing the reflected sentence changes the recomputed product. -/
example : cert.check extraSentence = false := by decide
example : badRepeated.check sentence = false := by decide
example : badFactorScale.check sentence = false := by decide
example : badDerivScale.check sentence = false := by decide
example : badFactor.check sentence = false := by decide
example : badDerivative.check sentence = false := by decide
example : badReplay.check sentence = false := by decide

/-- A genuine repeated-factor carrier: `Q = x²`, `P = x`, `R = x`, and
`Q' = x * 2`. -/
private def repeatedSentence : Sentence :=
  .forallReal (.and (.atom ⟨x, .ge⟩) (.atom ⟨x, .le⟩))

private def linearReplay : SturmReplay where
  chain := #[x, one]
  derivScale := 1
  steps := #[]

private def repeatedCert : CarrierCert where
  carrier := x
  repeated := x
  derivPart := DensePoly.ofCoeffs #[(2 : Int)]
  factorScale := 1
  derivScale := 1
  replay := linearReplay

example : linearReplay.check x = true := by decide
example : repeatedCert.check repeatedSentence = true := by decide

/-- The factor identity alone cannot justify dropping a root: for
`Q = (x-1)(x+1)`, the derivative identity rejects `P = x-1`. -/
private def xMinusOne : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 1]
private def xPlusOne : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 1]

private def minusReplay : SturmReplay where
  chain := #[xMinusOne, one]
  derivScale := 1
  steps := #[]

private def droppedRoot : CarrierCert where
  carrier := xMinusOne
  repeated := xPlusOne
  derivPart := DensePoly.ofCoeffs #[(2 : Int)]
  factorScale := 1
  derivScale := 1
  replay := minusReplay

example : minusReplay.check xMinusOne = true := by decide
example : DensePoly.beqCoeffs sentence.product
    (DensePoly.scale droppedRoot.factorScale
      (droppedRoot.carrier * droppedRoot.repeated)) = true := by decide
example : DensePoly.beqCoeffs
    (DensePoly.scale droppedRoot.derivScale (DensePoly.derivative sentence.product))
    (droppedRoot.repeated * droppedRoot.derivPart) = false := by decide
example : droppedRoot.check sentence = false := by decide

/-- The no-carrier branch is mandatory for constant-only formulas. -/
private def constantSentence : Sentence := .existsReal (.atom ⟨one, .gt⟩)
example : constantSentence.polys.isEmpty = true := by decide
example : cert.check constantSentence = false := by decide

/-- Collection covers implication/negation and bounded sentence constructors. -/
private def bounded : Sentence :=
  .forallIoc (Dyadic.ofInt (-2)) (Dyadic.ofInt 2)
    (.imp (.not (.atom ⟨0, .eq⟩)) (.atom ⟨quad, .gt⟩))

private def boundedExists : Sentence :=
  .existsIoc (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (.atom ⟨quad, .eq⟩)

example : bounded.polys.length = 1 := by decide
example : boundedExists.polys.length = 1 := by decide

end Hex.RCF.CarrierTests
