/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKronecker
public import HexMvPolyMathlib.Kernel
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Tactic

public section

namespace Hex.Kronecker

theorem powAux_eq (a : Int) (fuel n : Nat) (hn : n ≤ fuel) :
    powAux fuel a n = a ^ n := by
  induction fuel generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst n
      simp [powAux]
  | succ fuel ih =>
      by_cases hz : n = 0
      · subst n; simp [powAux]
      have hd : n / 2 ≤ fuel := by
        have := Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 2)
        omega
      have hm := Nat.mod_add_div n 2
      have hr := Nat.mod_lt n (by decide : 0 < 2)
      by_cases he : n % 2 = 0
      · simp only [powAux, beq_iff_eq, hz, ↓reduceIte, ih _ hd, he]
        rw [← pow_add]
        congr 1
        omega
      · have ho : n % 2 = 1 := by omega
        simp only [powAux, beq_iff_eq, hz, ↓reduceIte, ih _ hd, he]
        rw [← pow_add, ← pow_succ]
        congr 1
        omega

@[simp] theorem power_eq (a : Int) (n : Nat) : power a n = a ^ n :=
  powAux_eq a n n le_rfl

namespace Expr

/-- Interpret the fixed language in any commutative ring. -/
@[expose] def denote {R : Type u} [CommRing R] (v : Nat → R) : Expr → R
  | .int z => z
  | .atom i => v i
  | .add a b => denote v a + denote v b
  | .sub a b => denote v a - denote v b
  | .neg a => -denote v a
  | .mul a b => denote v a * denote v b
  | .pow a n => denote v a ^ n

/-- Interpret a validated expression using a finite atom assignment. -/
@[expose] def denoteFin {R : Type u} [CommRing R] {k : Nat} :
    (e : Expr) → e.WellFormed k → (Fin k → R) → R
  | .int z, _, _ => z
  | .atom i, h, v => v ⟨i, of_decide_eq_true h⟩
  | .add a b, h, v =>
      denoteFin a (Bool.and_eq_true_iff.mp h).1 v + denoteFin b (Bool.and_eq_true_iff.mp h).2 v
  | .sub a b, h, v =>
      denoteFin a (Bool.and_eq_true_iff.mp h).1 v - denoteFin b (Bool.and_eq_true_iff.mp h).2 v
  | .neg a, h, v => -denoteFin a h v
  | .mul a b, h, v =>
      denoteFin a (Bool.and_eq_true_iff.mp h).1 v * denoteFin b (Bool.and_eq_true_iff.mp h).2 v
  | .pow a n, h, v => denoteFin a h v ^ n

/-- The proof-only multivariate polynomial model. Invalid indices cannot be supplied. -/
@[expose] noncomputable def toMvPolynomial {k : Nat} (e : Expr) (h : e.WellFormed k) :
    MvPolynomial (Fin k) Int := e.denoteFin h MvPolynomial.X

theorem denoteFin_eq {R : Type u} [CommRing R] {k : Nat} (e : Expr)
    (h : e.WellFormed k) (v : Nat → R) :
    e.denoteFin h (fun i => v i.val) = e.denote v := by
  induction e with
  | int | atom => rfl
  | add a b ha hb => rw [denoteFin, denote, ha, hb]
  | sub a b ha hb => rw [denoteFin, denote, ha, hb]
  | mul a b ha hb => rw [denoteFin, denote, ha, hb]
  | neg a ha => rw [denoteFin, denote, ha]
  | pow a n ha => rw [denoteFin, denote, ha]

theorem map_denoteFin {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {k : Nat} (f : R →+* S) (e : Expr) (h : e.WellFormed k) (v : Fin k → R) :
    f (e.denoteFin h v) = e.denoteFin h (fun i => f (v i)) := by
  induction e with
  | int => simp [denoteFin]
  | atom => rfl
  | add a b ha hb => simp only [denoteFin, map_add, ha, hb]
  | sub a b ha hb => simp only [denoteFin, map_sub, ha, hb]
  | mul a b ha hb => simp only [denoteFin, map_mul, ha, hb]
  | neg a ha => simp only [denoteFin, map_neg, ha]
  | pow a n ha => simp only [denoteFin, map_pow, ha]

end Expr

theorem denote_eq_eval₂ {R : Type u} [CommRing R] {k : Nat} (e : Expr)
    (h : e.WellFormed k) (v : Fin k → R) :
    e.denoteFin h v = MvPolynomial.eval₂Hom (Int.castRingHom R) v (e.toMvPolynomial h) := by
  rw [Expr.toMvPolynomial, Expr.map_denoteFin]
  simp

theorem evalKron_eq_denote (base : Nat) (strides : List Nat) (e : Expr) :
    evalKron base strides e = e.denote (fun i => (base : Int) ^ strides.getD i 0) := by
  induction e <;> simp_all [evalKron, Expr.denote]

theorem evalKron_eq_eval₂ {k : Nat} (base : Nat) (strides : List Nat) (e : Expr)
    (h : e.WellFormed k) :
    evalKron base strides e = MvPolynomial.eval₂Hom (RingHom.id Int)
      (fun i : Fin k => (base : Int) ^ strides.getD i.val 0) (e.toMvPolynomial h) := by
  rw [evalKron_eq_denote, ← Expr.denoteFin_eq e h, denote_eq_eval₂]
  rfl

end Hex.Kronecker
