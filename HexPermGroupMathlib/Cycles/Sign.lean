/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroupMathlib.Cycles.Factors

public section

namespace Hex.Perm.Cycle

theorem sign_formPerm (xs : List (Fin n)) (h : xs.Nodup) :
    (Equiv.Perm.sign xs.formPerm : Int) = (-1 : Int) ^ (xs.length - 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hxy : x ≠ y := fun he => h.notMem (by simp [he])
      have ht := ih h.of_cons
      rw [List.formPerm_cons_cons, map_mul, Units.val_mul, Equiv.Perm.sign_swap hxy, ht]
      simp [_root_.pow_succ, mul_comm]

theorem sign_prod (cs : List (Array (Fin n))) (hd : ∀ c ∈ cs, c.toList.Nodup) :
    (Equiv.Perm.sign (cs.map (fun c => c.toList.formPerm)).prod : Int) =
      (-1 : Int) ^ (cs.map (fun c => c.size - 1)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have ht := ih (fun d hd' => hd d (by simp [hd']))
    simp only [List.map_cons, List.prod_cons, map_mul, Units.val_mul, sign_formPerm c.toList
      (hd c (by simp)), Array.length_toList, ht, List.sum_cons, _root_.pow_add]

theorem sum_defect (cs : List (Array (Fin n))) (hc : ∀ c ∈ cs, 0 < c.size) :
    (cs.map (fun c => c.size - 1)).sum + cs.length = (cs.map Array.size).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have ht := ih (fun d hd => hc d (by simp [hd]))
    have hp := hc c (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

end Hex.Perm.Cycle

namespace Hex.Perm

theorem sign_pow (p : Perm n) : p.sign = (-1 : Int) ^ (n - p.allCycles.size) := by
  simp only [sign, neg_one_pow_eq_ite, Nat.even_iff]

/-- The executable cycle-count formula agrees with Mathlib's sign homomorphism. -/
theorem sign_eq_mathlib (p : Perm n) : p.sign = (Equiv.Perm.sign p.toEquiv : Int) := by
  rw [sign_pow, ← p.allCycles_prod, Cycle.sign_prod _
    (fun c hc => (p.allCycles_valid c (by simpa using hc)).1)]
  congr 1
  have h := Cycle.sum_defect p.allCycles.toList
    (fun c hc => (p.allCycles_valid c (by simpa using hc)).nonempty)
  rw [p.allCycles_length] at h
  simp only [Array.length_toList] at h
  omega

theorem sign_comp (p q : Perm n) : (p.comp q).sign = p.sign * q.sign := by
  simp only [sign_eq_mathlib, toEquiv_comp, map_mul, Units.val_mul]

@[simp] theorem sign_id : (Perm.id n).sign = 1 := by simp [sign_eq_mathlib]

@[simp] theorem sign_inv (p : Perm n) : p.inv.sign = p.sign := by
  simp [sign_eq_mathlib]

/-- Every decomposition into transpositions gives the same parity as the
executable cycle-count formula. -/
theorem sign_transpositions (p : Perm n) (xs : List (Perm n))
    (hs : ∀ q ∈ xs, Equiv.Perm.IsSwap q.toEquiv)
    (hp : (xs.map toEquiv).prod = p.toEquiv) : p.sign = (-1 : Int) ^ xs.length := by
  rw [p.sign_eq_mathlib, ← hp, Equiv.Perm.sign_prod_list_swap]
  · simp
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact hs r hr

end Hex.Perm
