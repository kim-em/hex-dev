/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ExactDiv
public import HexPoly

public section

/-!
Exact scalar division for the Brown subresultant recurrence.

The coefficient-independent contract lives in `HexBasic.ExactDiv`: the total
`exactDiv` wrapper, the `ExactDivLaws` package, and the cancellation lemmas
that hold over every carrier. This module, which re-exports that contract
through a public import, adds the two layers above it.

First the binary-power helpers `powNat` and `divExp` with the lightweight
semiring power lemmas they need. These stay here rather than in `HexBasic`
because `mul_pow`, `pow_mul`, and `pow_ne_zero` shadow Mathlib root names, and
a shadow introduced at the bottom of the graph turns a bare use anywhere in the
scope of an `open Hex` into an ambiguous term; nothing below `hex-resultant`
needs them.

Then the polynomial-specific layer: coefficientwise scalar division on
`DensePoly`, the lightweight ring tower that lets resultant correctness recurse
into polynomial coefficient rings, and the recursive
`ExactDivLaws (DensePoly R)` instance.
-/
namespace Hex

universe u

variable {R : Type u}

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

/-- Powers distribute over multiplication in a lightweight commutative ring. -/
theorem mul_pow {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by
      rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero,
        Lean.Grind.Semiring.pow_zero]
      exact (Lean.Grind.Semiring.mul_one 1).symm
  | n + 1 => by
      rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ,
        Lean.Grind.Semiring.pow_succ, mul_pow a b n]
      grind

/-- Raising a power to another power multiplies the two exponents. -/
theorem pow_mul {S : Type u} [Lean.Grind.Semiring S]
    (x : S) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n := by
  symm
  induction n with
  | zero => simp [Lean.Grind.Semiring.pow_zero]
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, ih,
        ← Lean.Grind.Semiring.pow_add]
      congr 1

/-- Natural powers of a nonzero element stay nonzero in every nontrivial
exact-division ring. -/
theorem pow_ne_zero {S : Type u} [Lean.Grind.CommRing S] [Div S]
    [ExactDivLaws S] (h1 : (1 : S) ≠ 0) {a : S} (ha : a ≠ 0) :
    ∀ n : Nat, a ^ n ≠ 0
  | 0 => by
      simpa only [Lean.Grind.Semiring.pow_zero] using h1
  | n + 1 => by
      rw [Lean.Grind.Semiring.pow_succ]
      exact ExactDivLaws.mul_ne_zero (pow_ne_zero h1 ha n) ha

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

/-- The executable natural power of a nonzero element stays nonzero. -/
theorem powNat_ne_zero {S : Type u} [Lean.Grind.CommRing S] [Div S]
    [ExactDivLaws S] (h1 : (1 : S) ≠ 0) {a : S} (ha : a ≠ 0) (n : Nat) :
    powNat a n ≠ 0 := by
  rw [powNat_eq_pow]
  exact pow_ne_zero h1 ha n

/-- Brown's scalar update `x^n / y^(n-1)`, with the same total zero behavior
as `exactDiv`. -/
@[expose]
def divExp [Zero R] [DecidableEq R] [One R] [Mul R] [Div R]
    (x y : R) (n : Nat) : R :=
  exactDiv (powNat x n) (powNat y (n - 1))

namespace DensePoly

/-- A nonzero scalar does not change the normalized dense size. -/
theorem size_scale [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] {a : R} (ha : a ≠ 0) (p : DensePoly R) :
    (scale a p).size = p.size := by
  have hle : (scale a p).size ≤ p.size := by
    rw [scale_eq_scaleImpl]
    exact size_scaleImpl_le a p
  by_cases hp : p.size = 0
  · omega
  have hp_pos : 0 < p.size := Nat.pos_of_ne_zero hp
  have hcoeff : (scale a p).coeff (p.size - 1) ≠ (0 : R) := by
    rw [coeff_scale_semiring]
    exact ExactDivLaws.mul_ne_zero ha
      (coeff_last_ne_zero_of_pos_size p hp_pos)
  apply Nat.le_antisymm hle
  apply Nat.le_of_not_gt
  intro hlt
  exact hcoeff (coeff_eq_zero_of_size_le (scale a p) (by omega))

/-- Scaling a nonzero polynomial by a nonzero coefficient remains nonzero. -/
theorem scale_ne_zero [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] {a : R} (ha : a ≠ 0) {p : DensePoly R} (hp : p ≠ 0) :
    scale a p ≠ 0 := by
  intro hzero
  have hsize := congrArg DensePoly.size hzero
  rw [size_scale ha, size_zero] at hsize
  exact hp ((size_eq_zero_iff p).mp hsize)

/-- The leading coefficient scales with a nonzero coefficient scalar. -/
theorem leadingCoeff_scale [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] {a : R} (ha : a ≠ 0) (p : DensePoly R) :
    (scale a p).leadingCoeff = a * p.leadingCoeff := by
  by_cases hp : p.size = 0
  · have hp0 : p = 0 := (size_eq_zero_iff p).mp hp
    subst p
    simp [Lean.Grind.Semiring.mul_zero]
  have hp_pos : 0 < p.size := Nat.pos_of_ne_zero hp
  have hsize := size_scale ha p
  rw [leadingCoeff_eq_coeff_last _ (hsize ▸ hp_pos), hsize,
    coeff_scale_semiring, leadingCoeff_eq_coeff_last p hp_pos]

/-- Divide every coefficient by the same scalar.

Kernel-facing specification: one map over the coefficient list. Compiled code
runs the `Array.map` pass `divScalarImpl` via `divScalar_eq_impl`. -/
@[expose]
noncomputable def divScalar [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : DensePoly R :=
  if b = 0 then 0 else
    ofList (p.toList.map (fun a => a / b))

/-- Runtime array implementation of coefficientwise exact scalar division. -/
@[expose]
def divScalarImpl [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : DensePoly R :=
  if b = 0 then 0 else
    ofCoeffs (p.toArray.map (fun a => a / b))

/-- The list specification and array implementation of scalar division agree. -/
theorem divScalar_eq_divScalarImpl [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : divScalar p b = divScalarImpl p b := by
  unfold divScalar divScalarImpl ofList
  by_cases hb : b = 0
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]
    congr 1
    show ((p.toArray.toList).map (fun a => a / b)).toArray = _
    rw [← Array.toList_map, Array.toArray_toList]

/-- Coefficientwise scalar division cannot increase the stored polynomial size. -/
theorem size_divScalarImpl_le [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : (divScalarImpl p b).size ≤ p.size := by
  unfold divScalarImpl
  by_cases hb : b = 0
  · simp [hb]
  · rw [if_neg hb]
    exact Nat.le_trans (size_ofCoeffs_le _) (by simp)

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
  rw [if_neg hb, coeff_ofList]
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

/-- Scaling by a nonzero coefficient is cancellable. -/
theorem scale_cancel [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] {b : R} (hb : b ≠ 0) {p q : DensePoly R}
    (h : scale b p = scale b q) : p = q := by
  have hdiv := congrArg (fun r : DensePoly R => divScalar r b) h
  simpa only [divScalar_scale _ hb] using hdiv

end DensePoly

/-! The Mathlib-free dense-polynomial ring instance.

`HexPoly` proves its ring laws as standalone lemmas so its computational core
does not impose an algebra hierarchy.  Resultant correctness must recurse to
polynomial coefficient rings, however, so this layer packages those existing
lemmas as the lightweight `Lean.Grind` hierarchy.
-/

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Dense-polynomial negation is involutive. -/
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

/-- Natural-number casts are constant polynomials, reusing the canonical zero
and one. -/
instance instNatCast [Lean.Grind.CommRing R] [DecidableEq R] :
    NatCast (DensePoly R) :=
  ⟨fun n =>
    match n with
    | 0 => Zero.zero
    | 1 => One.one
    | n + 2 => C (Nat.cast (n + 2))⟩

/-- Numerals are constant polynomials, reusing the canonical zero and one. -/
instance instOfNat [Lean.Grind.CommRing R] [DecidableEq R] (n : Nat) :
    OfNat (DensePoly R) n :=
  ⟨match n with
    | 0 => Zero.zero
    | 1 => One.one
    | n + 2 => C (OfNat.ofNat (n + 2))⟩

/-- Natural scalar multiplication is multiplication by the cast constant. -/
instance instNSMul [Lean.Grind.CommRing R] [DecidableEq R] :
    SMul Nat (DensePoly R) :=
  ⟨fun n p => (Nat.cast n : DensePoly R) * p⟩

/-- Natural powers of dense polynomials via `natPow`. -/
instance instNPow [Lean.Grind.CommRing R] [DecidableEq R] :
    HPow (DensePoly R) Nat (DensePoly R) :=
  ⟨natPow⟩

/-- Integer casts are signed constant polynomials through the natural cast. -/
instance instIntCast [Lean.Grind.CommRing R] [DecidableEq R] :
    IntCast (DensePoly R) :=
  ⟨fun i =>
    match i with
    | .ofNat n => (Nat.cast n : DensePoly R)
    | .negSucc n => -(Nat.cast (n + 1) : DensePoly R)⟩

/-- Integer scalar multiplication is signed natural scalar multiplication. -/
instance instZSMul [Lean.Grind.CommRing R] [DecidableEq R] :
    SMul Int (DensePoly R) :=
  ⟨fun i p =>
    match i with
    | .ofNat n => n • p
    | .negSucc n => -((n + 1) • p)⟩

/-- A numeral polynomial stores its value in coefficient zero only. -/
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

/-- A cast-natural polynomial stores its value in coefficient zero only. -/
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

/-! Instance-contract checks for the dense-polynomial coefficient tower
exercised by the Brown regressions. -/

example : ExactDivLaws (DensePoly Int) := inferInstance

example : Lean.Grind.CommRing (DensePoly Int) := inferInstance

/-! Value-level pins for the binary-power helpers. -/

#guard powNat (3 : Int) 5 = 243

#guard divExp (4 : Int) 2 3 = 16

end Hex
