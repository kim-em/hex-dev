/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexPoly.Euclid.Reconstruction

public section

/-!
The Mathlib-free lightweight algebra hierarchy for dense polynomials.

`HexPoly` proves the polynomial laws directly.  This module packages them as
the `Lean.Grind` instances needed by generic matrix algebra, without adding a
Mathlib dependency.
-/

namespace Hex

universe u

variable {R : Type u}

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

/-- Linear reference power used to prove the binary implementation lawful. -/
private def linearPow [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) : Nat → DensePoly R
  | 0 => 1
  | n + 1 => linearPow p n * p

private theorem linearPow_square [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) (n : Nat) :
    linearPow (p * p) n = linearPow p (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [linearPow, ih]
      change linearPow p (2 * n) * (p * p) =
        (linearPow p (2 * n) * p) * p
      rw [DensePoly.mul_assoc_poly]

/-- Natural powers by binary exponentiation. -/
@[expose]
def natPow [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) (n : Nat) : DensePoly R :=
  if n = 0 then 1
  else
    let square := natPow (p * p) (n / 2)
    if n % 2 = 0 then square else square * p
termination_by n
decreasing_by omega

private theorem natPow_eq_linearPow [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) (n : Nat) : natPow p n = linearPow p n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
      rw [natPow]
      by_cases hn : n = 0
      · subst n
        rfl
      · rw [ite_eq_right hn, ih (n / 2)
          (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2))]
        rw [linearPow_square]
        have hmod := Nat.mod_add_div n 2
        have hlt := Nat.mod_lt n (by decide : 0 < 2)
        by_cases heven : n % 2 = 0
        · rw [ite_eq_left heven]
          congr 1
          omega
        · rw [ite_eq_right heven]
          have hnForm : n = 2 * (n / 2) + 1 := by omega
          calc
            linearPow p (2 * (n / 2)) * p =
                linearPow p (2 * (n / 2) + 1) := rfl
            _ = linearPow p n := congrArg (linearPow p) hnForm.symm

@[simp] theorem natPow_zero [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) : natPow p 0 = 1 := by
  rw [natPow_eq_linearPow]
  rfl

theorem natPow_succ [Lean.Grind.CommRing R] [DecidableEq R]
    (p : DensePoly R) (n : Nat) : natPow p (n + 1) = natPow p n * p := by
  rw [natPow_eq_linearPow, natPow_eq_linearPow]
  rfl

/-- Natural-number casts are constant polynomials, reusing zero and one. -/
instance instNatCast [Lean.Grind.CommRing R] [DecidableEq R] :
    NatCast (DensePoly R) :=
  ⟨fun n =>
    match n with
    | 0 => Zero.zero
    | 1 => One.one
    | n + 2 => C (Nat.cast (n + 2))⟩

/-- Numerals are constant polynomials, reusing zero and one. -/
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

/-- Natural powers of dense polynomials. -/
instance instNPow [Lean.Grind.CommRing R] [DecidableEq R] :
    HPow (DensePoly R) Nat (DensePoly R) :=
  ⟨natPow⟩

/-- Integer casts are signed constant polynomials. -/
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
      by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false]
  | succ n =>
      cases n with
      | zero =>
          change (DensePoly.C (1 : R)).coeff i =
            if i = 0 then (1 : R) else 0
          rw [DensePoly.coeff_C]
          by_cases hi : i = 0
          · simp only [hi, ite_true]
          · simpa only [hi, ite_false] using (coeffZero_eq (R := R))
      | succ n =>
          change (DensePoly.C (OfNat.ofNat (α := R) (n + 2))).coeff i =
            if i = 0 then OfNat.ofNat (α := R) (n + 2) else 0
          rw [DensePoly.coeff_C]
          by_cases hi : i = 0
          · simp only [hi, ite_true]
          · simpa only [hi, ite_false] using (coeffZero_eq (R := R))

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
      by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false]
  | succ n =>
      cases n with
      | zero =>
          change (DensePoly.C (1 : R)).coeff i =
            if i = 0 then (Nat.cast 1 : R) else 0
          rw [DensePoly.coeff_C, Lean.Grind.Semiring.natCast_one]
          by_cases hi : i = 0
          · simp only [hi, ite_true]
          · simpa only [hi, ite_false] using (coeffZero_eq (R := R))
      | succ n =>
          change (DensePoly.C (Nat.cast (n + 2))).coeff i =
            if i = 0 then (Nat.cast (n + 2) : R) else 0
          rw [DensePoly.coeff_C]
          by_cases hi : i = 0
          · simp only [hi, ite_true]
          · simpa only [hi, ite_false] using (coeffZero_eq (R := R))

end DensePoly

/-- Dense polynomials over a lightweight commutative ring form a lightweight
semiring. -/
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
    exact DensePoly.natPow_zero p
  · intro p n
    exact DensePoly.natPow_succ p n
  · intro n
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_add_semiring, DensePoly.coeff_ofNat,
      DensePoly.coeff_ofNat, DensePoly.coeff_ofNat]
    by_cases hi : i = 0
    · simpa [hi] using (Lean.Grind.Semiring.ofNat_succ (α := R) n)
    · simp only [hi, ite_false]
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

/-- Dense polynomials over a lightweight commutative ring form a lightweight
ring. -/
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
        | succ _ => rfl
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
        | succ _ => rfl
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

end Hex
