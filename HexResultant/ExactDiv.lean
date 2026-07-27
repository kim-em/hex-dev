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

/-- Raising a power to another power multiplies the two exponents. -/
private theorem pow_mul {S : Type u} [Lean.Grind.Semiring S]
    (x : S) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n := by
  symm
  induction n with
  | zero => simp [Lean.Grind.Semiring.pow_zero]
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, ih,
        ← Lean.Grind.Semiring.pow_add]
      congr 1

/-- The executable binary power agrees with the lightweight semiring power. -/
theorem powNat_eq_pow {S : Type u} [Lean.Grind.Semiring S]
    (x : S) (n : Nat) : powNat x n = x ^ n := by
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
      rw [powNat]
      by_cases hn : n = 0
      · subst n
        simp [Lean.Grind.Semiring.pow_zero]
      · rw [if_neg hn]
        have hlt : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2)
        rw [ih (n / 2) hlt (x * x)]
        have hdiv := Nat.mod_add_div n 2
        by_cases heven : n % 2 = 0
        · rw [if_pos heven, ← Lean.Grind.Semiring.pow_two, ← pow_mul]
          congr 1
          omega
        · rw [if_neg heven, ← Lean.Grind.Semiring.pow_two, ← pow_mul,
            ← Lean.Grind.Semiring.pow_succ]
          congr 1
          have hmod := Nat.mod_lt n (by decide : 0 < 2)
          omega

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

/-! The Mathlib-free dense-polynomial ring instance.

`HexPoly` proves its ring laws as standalone lemmas so its computational core
does not impose an algebra hierarchy.  Resultant correctness must recurse to
polynomial coefficient rings, however, so this layer packages those existing
lemmas as the lightweight `Lean.Grind` hierarchy.
-/

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

theorem DensePoly.neg_neg_poly [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) : -(-p) = p := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_neg_ring, DensePoly.coeff_neg_ring]
  grind

private theorem coeffZero_eq [Lean.Grind.CommRing R] :
    (Zero.zero : R) = 0 := rfl

namespace DensePoly

/-- Natural powers used by the lightweight dense-polynomial ring instance. -/
@[expose]
def natPow [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) : Nat → DensePoly R
  | 0 => 1
  | n + 1 => natPow p n * p

instance instNatCast [Lean.Grind.CommRing R] [DecidableEq R] :
    NatCast (DensePoly R) :=
  ⟨fun n =>
    match n with
    | 0 => Zero.zero
    | 1 => One.one
    | n + 2 => C (Nat.cast (n + 2))⟩

instance instOfNat [Lean.Grind.CommRing R] [DecidableEq R] (n : Nat) :
    OfNat (DensePoly R) n :=
  ⟨match n with
    | 0 => Zero.zero
    | 1 => One.one
    | n + 2 => C (OfNat.ofNat (n + 2))⟩

instance instNSMul [Lean.Grind.CommRing R] [DecidableEq R] :
    SMul Nat (DensePoly R) :=
  ⟨fun n p => (Nat.cast n : DensePoly R) * p⟩

instance instNPow [Lean.Grind.CommRing R] [DecidableEq R] :
    HPow (DensePoly R) Nat (DensePoly R) :=
  ⟨natPow⟩

instance instIntCast [Lean.Grind.CommRing R] [DecidableEq R] :
    IntCast (DensePoly R) :=
  ⟨fun i =>
    match i with
    | .ofNat n => (Nat.cast n : DensePoly R)
    | .negSucc n => -(Nat.cast (n + 1) : DensePoly R)⟩

instance instZSMul [Lean.Grind.CommRing R] [DecidableEq R] :
    SMul Int (DensePoly R) :=
  ⟨fun i p =>
    match i with
    | .ofNat n => n • p
    | .negSucc n => -((n + 1) • p)⟩

@[simp]
theorem coeff_ofNat [Lean.Grind.CommRing R] [DecidableEq R]
    (n i : Nat) :
    (OfNat.ofNat (α := DensePoly R) n).coeff i =
      if i = 0 then OfNat.ofNat (α := R) n else 0 := by
  cases n with
  | zero =>
      change (0 : DensePoly R).coeff i = if i = 0 then (0 : R) else 0
      rw [DensePoly.coeff_zero]
      by_cases hi : i = 0 <;> simp only [hi, if_true, if_false]
  | succ n =>
      cases n with
      | zero =>
          change (DensePoly.C (1 : R)).coeff i =
            if i = 0 then (1 : R) else 0
          rw [DensePoly.coeff_C]
          by_cases hi : i = 0
          · simp only [hi, if_true]
          · simpa only [hi, if_false] using (coeffZero_eq (R := R))
      | succ n =>
          change (DensePoly.C (OfNat.ofNat (α := R) (n + 2))).coeff i =
            if i = 0 then OfNat.ofNat (α := R) (n + 2) else 0
          rw [DensePoly.coeff_C]
          by_cases hi : i = 0
          · simp only [hi, if_true]
          · simpa only [hi, if_false] using (coeffZero_eq (R := R))

@[simp]
theorem coeff_natCast [Lean.Grind.CommRing R] [DecidableEq R]
    (n i : Nat) :
    (Nat.cast n : DensePoly R).coeff i =
      if i = 0 then (Nat.cast n : R) else 0 := by
  cases n with
  | zero =>
      change (0 : DensePoly R).coeff i =
        if i = 0 then (Nat.cast 0 : R) else 0
      rw [DensePoly.coeff_zero, Lean.Grind.Semiring.natCast_zero]
      by_cases hi : i = 0 <;> simp only [hi, if_true, if_false]
  | succ n =>
      cases n with
      | zero =>
          change (DensePoly.C (1 : R)).coeff i =
            if i = 0 then (Nat.cast 1 : R) else 0
          rw [DensePoly.coeff_C, Lean.Grind.Semiring.natCast_one]
          by_cases hi : i = 0
          · simp only [hi, if_true]
          · simpa only [hi, if_false] using (coeffZero_eq (R := R))
      | succ n =>
          change (DensePoly.C (Nat.cast (n + 2))).coeff i =
            if i = 0 then (Nat.cast (n + 2) : R) else 0
          rw [DensePoly.coeff_C]
          by_cases hi : i = 0
          · simp only [hi, if_true]
          · simpa only [hi, if_false] using (coeffZero_eq (R := R))

end DensePoly

/-- Dense polynomials over a lightweight commutative ring again form a
lightweight semiring. -/
instance instGrindSemiringDensePoly [Lean.Grind.CommRing R] [DecidableEq R] :
    Lean.Grind.Semiring (DensePoly R) := by
  refine Lean.Grind.Semiring.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact DensePoly.add_zero_poly
  · exact DensePoly.add_comm_poly
  · exact DensePoly.add_assoc_poly
  · exact DensePoly.mul_assoc_poly
  · exact DensePoly.mul_one_right_poly
  · intro p
    exact (DensePoly.mul_comm_poly 1 p).trans (DensePoly.mul_one_right_poly p)
  · exact DensePoly.mul_add_right_poly
  · exact DensePoly.mul_add_left_poly
  · exact DensePoly.zero_mul
  · intro p
    exact (DensePoly.mul_comm_poly p 0).trans (DensePoly.zero_mul p)
  · intro p
    rfl
  · intro p n
    rfl
  · intro n
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_add_semiring, DensePoly.coeff_ofNat,
      DensePoly.coeff_ofNat, DensePoly.coeff_ofNat]
    by_cases hi : i = 0
    · simpa [hi] using (Lean.Grind.Semiring.ofNat_succ (α := R) n)
    · simp only [hi, if_false]
      grind
  · intro n
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_ofNat, DensePoly.coeff_natCast]
    by_cases hi : i = 0
    · simpa [hi] using
        (Lean.Grind.Semiring.ofNat_eq_natCast (α := R) n)
    · simp [hi]
  · intro n p
    rfl

/-- Dense polynomials over a lightweight commutative ring again form a
lightweight ring. -/
instance instGrindRingDensePoly [Lean.Grind.CommRing R] [DecidableEq R] :
    Lean.Grind.Ring (DensePoly R) := by
  refine Lean.Grind.Ring.mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_add_semiring, DensePoly.coeff_neg_ring,
      DensePoly.coeff_zero]
    change -p.coeff n + p.coeff n = (0 : R)
    grind
  · exact DensePoly.sub_eq_add_neg_poly
  · intro i p
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            change (0 : Nat) • p = -((0 : Nat) • p)
            change (0 : DensePoly R) * p = -((0 : DensePoly R) * p)
            rw [DensePoly.zero_mul, DensePoly.neg_zero_ring]
        | succ n => rfl
    | negSucc n =>
        change (n + 1) • p = -(-((n + 1) • p))
        exact (DensePoly.neg_neg_poly _).symm
  · intro _ _
    rfl
  · intro n
    exact (Lean.Grind.Semiring.ofNat_eq_natCast (α := DensePoly R) n).symm
  · intro i
    cases i with
    | ofNat n =>
        cases n with
        | zero =>
            change (Nat.cast 0 : DensePoly R) = -(Nat.cast 0 : DensePoly R)
            rw [Lean.Grind.Semiring.natCast_zero, DensePoly.neg_zero_ring]
        | succ n => rfl
    | negSucc n =>
        change (Nat.cast (n + 1) : DensePoly R) =
          -(-(Nat.cast (n + 1) : DensePoly R))
        exact (DensePoly.neg_neg_poly _).symm

/-- Dense polynomial multiplication is commutative when coefficient
multiplication is. -/
instance instGrindCommRingDensePoly [Lean.Grind.CommRing R] [DecidableEq R] :
    Lean.Grind.CommRing (DensePoly R) := by
  refine Lean.Grind.CommRing.mk ?_
  exact DensePoly.mul_comm_poly

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

example : Lean.Grind.CommRing (DensePoly Int) := inferInstance

/-! Value-level pins for the total quotient and binary-power helpers. -/

#guard powNat (3 : Int) 5 = 243

#guard exactDiv (7 : Int) 0 = 0

#guard divExp (4 : Int) 2 3 = 16

end Hex
