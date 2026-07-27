/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public import Init.Grind.Ring.Field

public section

/-!
Exact scalar division for the Brown subresultant recurrence.

The executable operations reuse the coefficient type's existing `/` and make
division by zero deterministic. Algebraic correctness is isolated in
`ExactDivLaws`; computational consumers need only the operations, while proof
consumers opt into the law package.
-/
namespace Hex

universe u

/-- A quotient operation is exact when multiplication by every nonzero right
factor can be undone by division by that factor. -/
class ExactDivLaws (R : Type u) [Zero R] [Mul R] [Div R] : Prop where
  /-- Right multiplication followed by division by a nonzero factor cancels. -/
  mul_div_cancel_right : ∀ a b : R, b ≠ 0 → (a * b) / b = a

namespace ExactDivLaws

variable {R : Type u}

/-- Exact division implies right cancellation by a nonzero factor. -/
theorem mul_right_cancel [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]
    {a b c : R} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hdiv := congrArg (fun x : R => x / c) h
  rw [ExactDivLaws.mul_div_cancel_right a c hc,
    ExactDivLaws.mul_div_cancel_right b c hc] at hdiv
  exact hdiv

/-- Exact division and commutative-ring laws rule out nonzero products
vanishing. -/
theorem mul_ne_zero [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hzero
  have hdiv := congrArg (fun x : R => x / b) hzero
  have hzdiv : (0 : R) / b = 0 := by
    simpa [Lean.Grind.Semiring.zero_mul] using
      (ExactDivLaws.mul_div_cancel_right (0 : R) b hb)
  rw [ExactDivLaws.mul_div_cancel_right a b hb, hzdiv] at hdiv
  exact ha hdiv

end ExactDivLaws

variable {R : Type u}

/-- Total exact quotient wrapper. The zero denominator is a documented junk
input and returns zero. -/
@[expose]
def exactDiv [Zero R] [DecidableEq R] [Div R] (a b : R) : R :=
  if b = 0 then 0 else a / b

/-- Exact division by zero takes the stable junk branch. -/
@[simp, grind =]
theorem exactDiv_zero_right [Zero R] [DecidableEq R] [Div R] (a : R) :
    exactDiv a 0 = 0 := by
  simp [exactDiv]

/-- A nonzero exact quotient is the underlying quotient operation. -/
theorem exactDiv_eq_div_of_ne [Zero R] [DecidableEq R] [Div R]
    (a : R) {b : R} (hb : b ≠ 0) : exactDiv a b = a / b := by
  simp [exactDiv, hb]

/-- The wrapper cancels a nonzero exact right factor under `ExactDivLaws`. -/
@[simp]
theorem exactDiv_mul_right [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] (a : R) {b : R} (hb : b ≠ 0) :
    exactDiv (a * b) b = a := by
  rw [exactDiv_eq_div_of_ne _ hb]
  exact ExactDivLaws.mul_div_cancel_right a b hb

/-- Natural powers by binary exponentiation, using only the executable `One`
and `Mul` operations. The association order is part of this law-free
computational definition; correctness consumers assume associative ring
multiplication. -/
@[expose]
def powNat [One R] [Mul R] (x : R) (n : Nat) : R :=
  if n = 0 then
    1
  else
    let y := powNat (x * x) (n / 2)
    if n % 2 = 0 then y else y * x
termination_by n
decreasing_by omega

/-- Brown's scalar update `x^n / y^(n-1)`, with the same total zero behavior
as `exactDiv`. -/
@[expose]
def divExp [Zero R] [DecidableEq R] [One R] [Mul R] [Div R]
    (x y : R) (n : Nat) : R :=
  exactDiv (powNat x n) (powNat y (n - 1))

namespace DensePoly

/-- Divide every coefficient by the same scalar.

Kernel-facing specification: one map over the coefficient list. Compiled code
runs the `Array.map` pass `divScalarImpl` via `divScalar_eq_impl`. -/
@[expose]
noncomputable def divScalar [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : DensePoly R :=
  if b = 0 then 0 else
    ofCoeffs (p.toList.map (fun a => a / b)).toArray

/-- Runtime array implementation of coefficientwise exact scalar division. -/
@[expose]
def divScalarImpl [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : DensePoly R :=
  if b = 0 then 0 else
    ofCoeffs (p.toArray.map (fun a => a / b))

/-- The list specification and array implementation of scalar division agree. -/
theorem divScalar_eq_divScalarImpl [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : divScalar p b = divScalarImpl p b := by
  unfold divScalar divScalarImpl
  by_cases hb : b = 0
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]
    congr 1
    show ((p.toArray.toList).map (fun a => a / b)).toArray = _
    rw [← Array.toList_map, Array.toArray_toList]

/-- Register the array pass as the compiled scalar-division implementation. -/
@[csimp]
theorem divScalar_eq_impl : @divScalar = @divScalarImpl := by
  funext R _ _ _ p b
  exact divScalar_eq_divScalarImpl p b

/-- Mapping division over a coefficient list commutes with default-indexed
reads when zero divides to zero. -/
private theorem list_getD_map_div_zero [Zero R] [Div R]
    (b : R) (coeffs : List R) (n : Nat)
    (hzero : (Zero.zero : R) / b = (Zero.zero : R)) :
    (coeffs.map fun a => a / b).getD n (Zero.zero : R) =
      coeffs.getD n (Zero.zero : R) / b := by
  induction coeffs generalizing n with
  | nil => simp [hzero]
  | cons a as ih =>
      cases n with
      | zero => simp
      | succ n => simpa using ih n

/-- Coefficient law for exact scalar division by a nonzero factor. -/
theorem coeff_divScalar [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] (p : DensePoly R) {b : R} (hb : b ≠ 0) (n : Nat) :
    (divScalar p b).coeff n = p.coeff n / b := by
  unfold divScalar
  rw [if_neg hb, coeff_ofCoeffs_list]
  have hzero : (0 : R) / b = 0 := by
    simpa [Lean.Grind.Semiring.zero_mul] using
      (ExactDivLaws.mul_div_cancel_right (0 : R) b hb)
  rw [list_getD_map_div_zero b p.toList n hzero, toList_getD_eq_coeff]

/-- Exact scalar division undoes scalar multiplication by a nonzero factor. -/
@[simp]
theorem divScalar_scale [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] (p : DensePoly R) {b : R} (hb : b ≠ 0) :
    divScalar (scale b p) b = p := by
  apply ext_coeff
  intro n
  rw [coeff_divScalar _ hb, coeff_scale_semiring,
    Lean.Grind.CommSemiring.mul_comm]
  exact ExactDivLaws.mul_div_cancel_right (p.coeff n) b hb

end DensePoly

/-- Integer Euclidean division is exact on nonzero right multiples. -/
instance instExactDivLawsInt : ExactDivLaws Int where
  mul_div_cancel_right := Int.mul_ediv_cancel

/-- Every `Lean.Grind.Field` supplies the exact-division law. -/
instance instExactDivLawsField {K : Type u} [Lean.Grind.Field K] :
    ExactDivLaws K where
  mul_div_cancel_right a b hb := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hb, Lean.Grind.Semiring.mul_one]

/-- Exact coefficient division lifts recursively to exact dense-polynomial
division, including nonunit constants and nonmonic polynomial factors. -/
instance instExactDivLawsDensePoly [Lean.Grind.CommRing R] [DecidableEq R]
    [Div R] [ExactDivLaws R] : ExactDivLaws (DensePoly R) where
  mul_div_cancel_right a b hb := by
    have hb_pos : 0 < b.size := by
      by_cases hpos : 0 < b.size
      · exact hpos
      · exfalso
        apply hb
        apply DensePoly.ext_coeff
        intro i
        rw [DensePoly.coeff_zero]
        exact DensePoly.coeff_eq_zero_of_size_le b (by omega)
    have hlc : b.leadingCoeff ≠ (0 : R) :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size b hb_pos
    have hpair : DensePoly.divMod (a * b) b = (a, 0) :=
      DensePoly.divMod_eq_of_polynomial_mul (a * b) b a hb
        (fun x => ExactDivLaws.mul_div_cancel_right x b.leadingCoeff hlc)
        (fun _ hx => ExactDivLaws.mul_ne_zero hx hlc)
        rfl
    change (DensePoly.divMod (a * b) b).1 = a
    exact congrArg Prod.fst hpair

/-! Instance-contract checks for the two coefficient towers exercised by the
Brown regressions. -/

example : ExactDivLaws Int := inferInstance

example : ExactDivLaws (DensePoly Int) := inferInstance

end Hex
