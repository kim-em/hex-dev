/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Laws

public section

/-! Check the data reached through Mathlib's structures and bridges. -/

namespace Hex.RealAlgebraicNumber

example : Field.toGrindField (K := RealAlgebraicNumber) = instFieldOfLaws := rfl
example : instLinearOrder.toOrd = instOrd := rfl

section OperationRegression

attribute [-instance] instZero instOne instNatCast instIntCast instAdd instSub
  instMul instNeg instInv instDiv instPowNat instPowInt instSMulRat instSMulNat instSMulInt
  instLT instLE instOrd instMin instMax instDecidableLT instDecidableLE
  instDecidableEqOfLaws instFieldOfLaws instOrderedRing instIsLinearOrderOfLaws
  instLawfulOrderLTOfLaws instLawfulOrderBEqOfLaws instLawfulOrderOrdOfLaws
  instLawfulOrderLeftLeaningMin instLawfulOrderLeftLeaningMax

variable (a b : RealAlgebraicNumber) (n : Nat) (z : Int) (q : Rat) (u : ℚ≥0)

example : (0 : RealAlgebraicNumber) = zero := rfl
example : (1 : RealAlgebraicNumber) = ofRat 1 := rfl
example : a + b = add a b := rfl
example : a - b = sub a b := rfl
example : a * b = mul a b := rfl
example : -a = neg a := rfl
example : a⁻¹ = inv a := rfl
example : a / b = div a b := rfl
example : a ^ n = natPow a n := rfl
example : a ^ z = intPow a z := rfl
example : n • a = smul (n : Rat) a := rfl
example : z • a = smul (z : Rat) a := rfl
example : q • a = smul q a := rfl
example : u • a = smul (u : Rat) a := rfl
example : (n : RealAlgebraicNumber) = ofRat (n : Rat) := rfl
example : (z : RealAlgebraicNumber) = ofRat (z : Rat) := rfl
example : (q : RealAlgebraicNumber) = ofRat q := rfl
example : (u : RealAlgebraicNumber) = ofRat (u : Rat) := rfl
example : Ord.compare a b = compare a b := rfl
example : Min.min a b = min a b := rfl
example : Max.max a b = max a b := rfl
example : (a < b) = (compare a b = .lt) := rfl
example : (a ≤ b) = (compare a b ≠ .gt) := rfl
example : instLinearOrder.toDecidableLT a b = instDecidableLT a b := rfl
example : (inferInstance : Decidable (a ≤ b)) = instDecidableLE a b := rfl
example : (inferInstance : Decidable (a = b)) = instDecidableEqOfLaws a b := rfl
example : (inferInstance : Ord RealAlgebraicNumber) = instOrd := rfl
example : (inferInstance : Lean.Grind.Field RealAlgebraicNumber) = instFieldOfLaws := rfl

-- OrderedRing depends on the selected semiring and preorder dictionaries.
-- Pin those parents before comparing the packages at one explicit type.
local instance : Lean.Grind.Semiring RealAlgebraicNumber :=
  (Field.toGrindField (K := RealAlgebraicNumber)).toCommRing.toRing.toSemiring
local instance : Std.IsPreorder RealAlgebraicNumber :=
  instIsLinearOrderOfLaws.toIsPartialOrder.toIsPreorder

example : (inferInstance : Lean.Grind.OrderedRing RealAlgebraicNumber) = instOrderedRing := rfl

-- Compilation must retain these executable operations through the Field and
-- LinearOrder dictionaries, even with the primitive instances disabled.
private def orderedCube (a : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if a ≤ 0 then -(a ^ (3 : Nat)) else a ^ (3 : Nat)

end OperationRegression

end Hex.RealAlgebraicNumber
