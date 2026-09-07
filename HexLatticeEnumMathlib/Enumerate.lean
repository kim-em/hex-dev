/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Enumerate
public import HexLatticeEnumMathlib.Distance
public import HexLatticeEnumMathlib.Order
import Mathlib.Tactic

public section

namespace HexLatticeEnumMathlib

open Hex.LatticeEnum

variable {n m : Nat}

/-- Exact squared cost of the chosen suffix, excluding the orthogonal residual. -/
noncomputable def suffix (p : Data n m) (z : Vector Int n) (k : Nat) : Rat :=
  ∑ i : Fin n, if k ≤ i.val then p.norms[i] * ((z[i] : Rat) - p.centre z i) ^ 2 else 0

/-- Every valid suffix cost is nonnegative. -/
theorem suffix_nonneg (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) (z : Vector Int n) (k : Nat) : 0 ≤ suffix p z k := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (le_of_lt (hp.1 i).1) (sq_nonneg _)
  · exact le_rfl

/-- Before any coefficient is chosen, the suffix cost is zero. -/
theorem suffix_rank (p : Data n m) (z : Vector Int n) : suffix p z n = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp [not_le.mpr i.isLt]

/-- The full suffix plus residual is exactly the direct squared distance. -/
theorem suffix_zero (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) (z : Vector Int n) :
    p.residual.normSq + suffix p z 0 = distance (Hex.Matrix.vecMul z rows) t := by
  rw [distance_decomposition p rows t hp z]
  simp [suffix]

/-- Modifying a coefficient leaves every strictly later centre unchanged. -/
theorem centre_set (p : Data n m) (z : Vector Int n) (k : Nat) (hk : k < n)
    (a : Int) (i : Fin n) (hi : k ≤ i.val) :
    p.centre (z.set k a hk) i = p.centre z i := by
  apply centre_congr
  intro j hj
  simp only [Fin.getElem_fin]
  exact Vector.getElem_set_ne hk j.isLt (by omega)

/-- Chosen suffix costs depend only on the selected coefficients. -/
theorem suffix_congr (p : Data n m) (z w : Vector Int n) (k : Nat)
    (h : ∀ i : Fin n, k ≤ i.val → z[i] = w[i]) : suffix p z k = suffix p w k := by
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [h i hi, centre_congr p z w i (fun j hj => h j (by omega))]
  · rfl

/-- Updating the next coefficient adds precisely the cost used by the executable traversal. -/
theorem suffix_step (p : Data n m) (z : Vector Int n) (k : Nat) (hk : k < n) (a : Int) :
    suffix p (z.set k a hk) k = suffix p z (k + 1) +
      p.norms[k] * ((a : Rat) - p.centre z ⟨k, hk⟩) * ((a : Rat) - p.centre z ⟨k, hk⟩) := by
  let i : Fin n := ⟨k, hk⟩
  have he : ∀ j : Fin n,
      (if k ≤ j.val then p.norms[j] * ((z.set k a hk)[j] - p.centre (z.set k a hk) j) ^ 2 else 0) =
      (if k + 1 ≤ j.val then p.norms[j] * ((z[j] : Rat) - p.centre z j) ^ 2 else 0) +
        (if j = i then p.norms[k] * ((a : Rat) - p.centre z i) ^ 2 else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [i, centre_set p z k hk a i (by rfl)]
    · have hne : k ≠ j.val := by intro h; apply hji; apply Fin.ext; exact h.symm
      by_cases hj : k ≤ j.val
      · rw [centre_set p z k hk a j hj]
        simp only [Fin.getElem_fin, Vector.getElem_set_ne hk j.isLt hne]
        simp [hji, hj, show k + 1 ≤ j.val by omega]
      · simp [hji, hj, show ¬k + 1 ≤ j.val by omega]
  unfold suffix
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  ring

/-- Dropping nonnegative terms can only decrease the suffix cost. -/
theorem suffix_le (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) (z : Vector Int n) {k l : Nat} (hkl : k ≤ l) :
    suffix p z l ≤ suffix p z k := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> try omega
  · exact le_rfl
  · exact mul_nonneg (le_of_lt (hp.1 i).1) (sq_nonneg _)
  · exact le_rfl

/-- The residual and selected suffix are a lower bound for every full distance. -/
theorem suffix_bound (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) (z : Vector Int n) (k : Nat) :
    p.residual.normSq + suffix p z k ≤ distance (Hex.Matrix.vecMul z rows) t := by
  rw [← suffix_zero p rows t hp z]
  have := suffix_le p rows t hp z (Nat.zero_le k)
  linarith

/-- Every feasible completion must choose its next coefficient inside the computed interval. -/
theorem completion_bound (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) (z w : Vector Int n) (k : Nat) (hk : k < n) (r : Rat)
    (hs : ∀ j : Fin n, k < j.val → w[j] = z[j])
    (hr : distance (Hex.Matrix.vecMul w rows) t ≤ r) :
    let interval := bounds (p.centre z ⟨k, hk⟩) p.norms[k]
      (r - p.residual.normSq - suffix p z (k + 1))
    interval.lo ≤ w[k] ∧ w[k] ≤ interval.hi := by
  dsimp only
  have hd : 0 < p.norms[k] := by simpa using (hp.1 ⟨k, hk⟩).1
  rw [bounds_iff _ _ _ _ hd]
  have hstep := suffix_step p w k hk w[k]
  have hset : w.set k w[k] hk = w := by simp
  rw [hset, suffix_congr p w z (k + 1) (fun i hi => hs i (by omega)),
    centre_congr p w z ⟨k, hk⟩ hs] at hstep
  have hbound := suffix_bound p rows t hp w k
  nlinarith

/-- A suffix with an excessive lower bound has no feasible completion. -/
theorem prune_suffix (p : Data n m) (rows : Hex.Matrix Int n m) (t : Vector Rat m)
    (hp : p.Valid rows t) (z w : Vector Int n) (k : Nat) (r : Rat)
    (hs : ∀ j : Fin n, k ≤ j.val → w[j] = z[j])
    (hr : r < p.residual.normSq + suffix p z k) :
    r < distance (Hex.Matrix.vecMul w rows) t := by
  have h := suffix_bound p rows t hp w k
  rw [suffix_congr p w z k hs] at h
  exact lt_of_lt_of_le hr h


end HexLatticeEnumMathlib
