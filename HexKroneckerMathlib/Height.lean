/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Denote

public section

namespace Hex.Kronecker

open scoped BigOperators

noncomputable section

/-- The coefficient ℓ¹ norm in the integer polynomial model. -/
@[expose] def norm₁ {σ : Type*} (p : MvPolynomial σ Int) : Nat :=
  p.support.sum (fun d => (p.coeff d).natAbs)

@[simp] theorem norm₁_zero {σ : Type*} : norm₁ (0 : MvPolynomial σ Int) = 0 := by
  simp [norm₁]

theorem norm₁_eq_sum {σ : Type*} (p : MvPolynomial σ Int) (s : Finset (σ →₀ Nat))
    (hs : p.support ⊆ s) : norm₁ p = ∑ d ∈ s, (p.coeff d).natAbs := by
  classical
  apply Finset.sum_subset hs
  intro d _ hd
  simp [MvPolynomial.notMem_support_iff.mp hd]

@[simp] theorem norm₁_monomial {σ : Type*} (d : σ →₀ Nat) (c : Int) :
    norm₁ (MvPolynomial.monomial d c) = c.natAbs := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · simp [norm₁, MvPolynomial.support_monomial, hc]

@[simp] theorem norm₁_one {σ : Type*} : norm₁ (1 : MvPolynomial σ Int) = 1 := by
  simpa only [MvPolynomial.one_def, Int.natAbs_one] using
    norm₁_monomial (σ := σ) 0 1

theorem norm₁_add {σ : Type*} (p q : MvPolynomial σ Int) :
    norm₁ (p + q) ≤ norm₁ p + norm₁ q := by
  classical
  rw [norm₁_eq_sum (p + q) (p.support ∪ q.support) MvPolynomial.support_add,
    norm₁_eq_sum p (p.support ∪ q.support) Finset.subset_union_left,
    norm₁_eq_sum q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun d _ => by
    simpa only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      Int.natAbs_add_le (p.coeff d) (q.coeff d)

@[simp] theorem norm₁_neg {σ : Type*} (p : MvPolynomial σ Int) : norm₁ (-p) = norm₁ p := by
  simp [norm₁]

theorem norm₁_sub {σ : Type*} (p q : MvPolynomial σ Int) :
    norm₁ (p - q) ≤ norm₁ p + norm₁ q := by
  simpa [sub_eq_add_neg] using norm₁_add p (-q)

theorem norm₁_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ Int) :
    norm₁ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, norm₁ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (norm₁_add _ _).trans (Nat.add_le_add_left ih _)

theorem norm₁_mul {σ : Type*} (p q : MvPolynomial σ Int) :
    norm₁ (p * q) ≤ norm₁ p * norm₁ q := by
  classical
  rw [MvPolynomial.mul_def]
  change norm₁ (∑ d ∈ p.support, ∑ e ∈ q.support,
    MvPolynomial.monomial (d + e) (p.coeff d * q.coeff e)) ≤ _
  apply (norm₁_sum _ _).trans
  apply (Finset.sum_le_sum (fun d _ => norm₁_sum q.support _)).trans
  simp only [norm₁_monomial, Int.natAbs_mul]
  simp only [norm₁, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem norm₁_pow {σ : Type*} (p : MvPolynomial σ Int) (n : Nat) :
    norm₁ (p ^ n) ≤ norm₁ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (norm₁_mul _ _).trans (Nat.mul_le_mul_right _ ih)

theorem coeff_le_norm₁ {σ : Type*} (p : MvPolynomial σ Int) (d : σ →₀ Nat) :
    (p.coeff d).natAbs ≤ norm₁ p := by
  classical
  by_cases hd : d ∈ p.support
  · exact Finset.single_le_sum (f := fun d => (p.coeff d).natAbs)
      (fun _ _ => Nat.zero_le _) hd
  · simp [MvPolynomial.notMem_support_iff.mp hd]

theorem Expr.norm₁_le {k : Nat} (e : Expr) (h : e.WellFormed k) :
    norm₁ (e.toMvPolynomial h) ≤ e.height := by
  induction e with
  | int z =>
      change norm₁ (MvPolynomial.C z) ≤ z.natAbs
      exact le_of_eq (norm₁_monomial 0 z)
  | atom i =>
      change norm₁ (MvPolynomial.X (⟨i, Nat.le_of_ble_eq_true h⟩ : Fin k)) ≤ 1
      simp [MvPolynomial.X]
  | add a b ha hb =>
      exact (norm₁_add _ _).trans (Nat.add_le_add (ha _) (hb _))
  | sub a b ha hb =>
      exact (norm₁_sub _ _).trans (Nat.add_le_add (ha _) (hb _))
  | neg a ha =>
      change norm₁ (-a.toMvPolynomial h) ≤ a.height
      rw [norm₁_neg]
      exact ha h
  | mul a b ha hb =>
      exact (norm₁_mul _ _).trans (Nat.mul_le_mul (ha _) (hb _))
  | pow a n ha =>
      exact (norm₁_pow _ n).trans (Nat.pow_le_pow_left (ha _) n)

end

end Hex.Kronecker
