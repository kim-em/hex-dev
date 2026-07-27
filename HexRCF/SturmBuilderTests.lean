/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SturmBuilder
import all HexRCF.SturmBuilder

public section

/-! Regression tests for multiplication-only Sturm replay and its builder. -/

namespace Hex.RCF.SturmBuilderTests

private def quad : ZPoly :=
  DensePoly.ofCoeffs #[(-1 : Int), 0, 1]

private def x : ZPoly :=
  DensePoly.ofCoeffs #[(0 : Int), 1]

private def one : ZPoly :=
  DensePoly.ofCoeffs #[(1 : Int)]

private def quadReplay : SturmReplay where
  chain := #[quad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 }]

example : quadReplay.check quad = true := by decide

example : Squarefree (HexRealRootsMathlib.toPolyℝ quad) :=
  SturmReplay.squarefree_of_check (cert := quadReplay) (by decide)

private def badScale : SturmReplay :=
  { quadReplay with
    steps := #[{ leftScale := 0, quotient := x, rightScale := 1 }] }

private def badQuotient : SturmReplay :=
  { quadReplay with
    steps := #[{ leftScale := 1, quotient := 0, rightScale := 1 }] }

private def badRightScale : SturmReplay :=
  { quadReplay with
    steps := #[{ leftScale := 1, quotient := x, rightScale := 0 }] }

private def badLength : SturmReplay :=
  { quadReplay with steps := #[] }

private def badDerivative : SturmReplay :=
  { quadReplay with derivScale := 3 }

private def badDerivativeSign : SturmReplay :=
  { quadReplay with derivScale := 0 }

private def twiceQuad : ZPoly :=
  DensePoly.ofCoeffs #[(-2 : Int), 0, 2]

private def twiceX : ZPoly :=
  DensePoly.ofCoeffs #[(0 : Int), 2]

private def badHead : SturmReplay where
  chain := #[twiceQuad, x, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := twiceX, rightScale := 2 }]

private def xPlusOne : ZPoly :=
  DensePoly.ofCoeffs #[(1 : Int), 1]

private def badDegree : SturmReplay where
  chain := #[quad, x, one, one]
  derivScale := 2
  steps := #[{ leftScale := 1, quotient := x, rightScale := 1 },
    { leftScale := 1, quotient := xPlusOne, rightScale := 1 }]

private def badTerminal : SturmReplay where
  chain := #[quad, x]
  derivScale := 2
  steps := #[]

example : badScale.check quad = false := by decide
example : badQuotient.check quad = false := by decide
example : badRightScale.check quad = false := by decide
example : badLength.check quad = false := by decide
example : badDerivative.check quad = false := by decide
example : badDerivativeSign.check quad = false := by decide
example : badHead.check quad = false := by decide
example : badDegree.check quad = false := by decide
example : badTerminal.check quad = false := by decide

private def wide : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt 2) (by decide)

private def rightRoot : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 1) (by decide)

private def excludedLeftRoot : DyadicInterval :=
  DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 0) (by decide)

example : quadReplay.count wide = 2 := by decide
example : quadReplay.count rightRoot = 1 := by decide
example : quadReplay.count excludedLeftRoot = 0 := by decide
example : quadReplay.total = 2 := by decide

example : (HexRealRootsMathlib.Literal.rootsIn
    (HexRealRootsMathlib.toPolyℝ quad) wide).card = 2 := by
  have h := SturmReplay.count_eq_card_roots
    (f := quad) (cert := quadReplay) (by decide) wide
  have hcount : quadReplay.count wide = 2 := by decide
  exact_mod_cast (hcount ▸ h).symm

/-- The compiled builder emits and rechecks the expected squarefree cases. -/
example : (buildSturmReplay? quad).map (fun cert => cert.check quad) = some true := by
  decide

private def linear : ZPoly :=
  DensePoly.ofCoeffs #[(3 : Int), 2]

example : (buildSturmReplay? linear).map
    (fun cert => decide (cert.steps.size = 0) && cert.check linear) = some true := by
  decide

private def cubic : ZPoly :=
  DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]

example : (buildSturmReplay? cubic).map (fun cert => cert.check cubic) = some true := by
  decide

/-- This chain reaches a negative-leading-coefficient divisor, exercising the
sign correction in the accumulated quotient. -/
private def cubicPlus : ZPoly :=
  DensePoly.ofCoeffs #[(0 : Int), 1, 0, 1]

example : (buildSturmReplay? cubicPlus).map
    (fun cert => cert.check cubicPlus) = some true := by
  decide

/-- The first division takes two pseudo-remainder reductions, pinning both the
accumulated left scale and the scaled previous quotient. -/
private def accumulated : ZPoly :=
  DensePoly.ofCoeffs #[(-1 : Int), 0, 1, 1]

private def accumulatedQuotient : ZPoly :=
  DensePoly.ofCoeffs #[(1 : Int), 3]

example : (buildSturmReplay? accumulated).map (fun cert =>
    match cert.steps.toList.head? with
    | some step => decide (step.leftScale = 9) &&
        DensePoly.beqCoeffs step.quotient accumulatedQuotient
    | none => false) = some true := by
  decide

example : (buildSturmReplay? accumulated).map
    (fun cert => cert.check accumulated) = some true := by
  decide

/-- The literal head is retained for a nonprimitive polynomial. -/
private def nonprimitive : ZPoly :=
  DensePoly.ofCoeffs #[(-6 : Int), 0, 6]

example : (buildSturmReplay? nonprimitive).map
    (fun cert => match cert.chain.toList.head? with
      | some head => DensePoly.beqCoeffs head nonprimitive
      | none => false) = some true := by
  decide

example : (buildSturmReplay? nonprimitive).map
    (fun cert => cert.check nonprimitive) = some true := by
  decide

example : (buildSturmReplay? nonprimitive).map
    (fun cert => decide (cert.derivScale = 12)) = some true := by
  decide

private def repeated : ZPoly :=
  DensePoly.ofCoeffs #[(1 : Int), -2, 1]

example : (buildSturmReplay? repeated).isNone = true := by decide
example : (buildSturmReplay? one).isNone = true := by decide
example : (buildSturmReplay? (0 : ZPoly)).isNone = true := by decide

end Hex.RCF.SturmBuilderTests
