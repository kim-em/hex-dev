/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Gram matrices and standard-basis dot products.
-/

universe u v

namespace Vector

/-- A foldl whose every step adds `0` reduces to the initial accumulator. -/
private theorem foldl_add_eq_acc {R : Type u} [Lean.Grind.CommRing R]
    {α : Type v} (xs : List α) (f : α → R) (acc : R)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hac : acc + (0 : R) = acc := by grind
      rw [hac]
      exact ih acc hxs

/-- A foldl summing an indicator function picks out the unique matching index. -/
private theorem foldl_indicator_unique {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0)) acc = acc + 1 := by
  induction xs generalizing acc with
  | nil => exact absurd hi (List.not_mem_nil)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · have hx_eq : (if i = x then (1 : R) else 0) = 1 := by
          rw [hieq]; simp
        rw [hx_eq]
        have hxs_zero : ∀ y ∈ xs, (if i = y then (1 : R) else 0) = 0 := by
          intro y hy
          have hyx : y ≠ x := fun heq => by
            rw [heq] at hy
            exact (List.nodup_cons.mp hnodup).1 hy
          have hiy : i ≠ y := by
            rw [hieq]; exact fun h => hyx h.symm
          simp [hiy]
        rw [foldl_add_eq_acc xs _ _ hxs_zero]
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        have hx_eq : (if i = x then (1 : R) else 0) = 0 := by simp [hxi]
        rw [hx_eq]
        have hac : acc + (0 : R) = acc := by grind
        rw [hac]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

/-- Squaring an indicator gives the same indicator. -/
private theorem foldl_indicator_square_eq {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (acc : R) :
    xs.foldl (fun acc l =>
        acc + (if i = l then (1 : R) else 0) * (if i = l then (1 : R) else 0)) acc =
      xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hsq :
          (if i = x then (1 : R) else 0) * (if i = x then (1 : R) else 0) =
            if i = x then (1 : R) else 0 := by
        by_cases h : i = x
        · rw [if_pos h]; grind
        · rw [if_neg h]; grind
      rw [hsq]
      exact ih _

/-- Strip standard-basis lookups inside a dotProduct-style foldl body. -/
private theorem foldl_dotProduct_unit_body {R : Type u} [Lean.Grind.CommRing R]
    {n : Nat} (xs : List (Fin n)) (i j : Fin n) (acc : R) :
    xs.foldl
        (fun acc l =>
          acc + (unit (R := R) i)[l] * (unit (R := R) j)[l]) acc =
      xs.foldl
        (fun acc l =>
          acc + (if i = l then (1 : R) else 0) * (if j = l then (1 : R) else 0)) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [getElem_unit, getElem_unit]
      exact ih (acc + (if i = x then 1 else 0) * (if j = x then 1 else 0))

/-- Dot product of standard basis vectors. -/
@[simp] theorem dotProduct_unit_unit {R : Type u} [Lean.Grind.CommRing R] {n : Nat}
    (i j : Fin n) :
    dotProduct (unit (R := R) i) (unit (R := R) j) = if i = j then 1 else 0 := by
  unfold dotProduct
  rw [foldl_dotProduct_unit_body]
  by_cases hij : i = j
  · subst hij
    rw [foldl_indicator_square_eq]
    rw [foldl_indicator_unique (List.finRange n) i (List.mem_finRange i)
      (List.nodup_finRange n) (0 : R)]
    rw [if_pos rfl]; grind
  · have hzero : ∀ l ∈ List.finRange n,
        (if i = l then (1 : R) else 0) * (if j = l then (1 : R) else 0) = 0 := by
      intro l _
      by_cases hil : i = l
      · have hjl : j ≠ l := fun heq => hij (hil.trans heq.symm)
        rw [if_pos hil, if_neg hjl]; grind
      · rw [if_neg hil]; grind
    rw [foldl_add_eq_acc (List.finRange n) _ _ hzero, if_neg hij]

end Vector

namespace Hex

namespace Matrix

/-- Gram matrix of the rows of a dense matrix. -/
@[expose]
def gramMatrix [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) : Matrix R n n :=
  ofFn fun i j => (row M i).dotProduct (row M j)

/-- Entry characterization for the Gram matrix of the rows of a dense matrix. -/
@[grind =] theorem getElem_gramMatrix [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (i j : Fin n) :
    (gramMatrix M)[i][j] = (row M i).dotProduct (row M j) := by
  rw [gramMatrix, getElem_ofFn]

/-- The Gram matrix of the identity is the identity. -/
@[simp, grind =] theorem gramMatrix_one {R : Type u} [Lean.Grind.CommRing R] {n : Nat} :
    gramMatrix (1 : Matrix R n n) = (1 : Matrix R n n) := by
  ext i hi j hj
  have hrow_i : (1 : Matrix R n n).row ⟨i, hi⟩ =
      Vector.unit (R := R) ⟨i, hi⟩ := by
    ext a ha
    show ((1 : Matrix R n n).row ⟨i, hi⟩)[(⟨a, ha⟩ : Fin n)] =
      (Vector.unit (R := R) ⟨i, hi⟩)[(⟨a, ha⟩ : Fin n)]
    rw [Matrix.row, Hex.Matrix.getElem_one (i := (⟨i, hi⟩ : Fin n)) (j := (⟨a, ha⟩ : Fin n)),
      Vector.getElem_unit (i := (⟨i, hi⟩ : Fin n)) (j := (⟨a, ha⟩ : Fin n))]
    rfl
  have hrow_j : (1 : Matrix R n n).row ⟨j, hj⟩ =
      Vector.unit (R := R) ⟨j, hj⟩ := by
    ext a ha
    show ((1 : Matrix R n n).row ⟨j, hj⟩)[(⟨a, ha⟩ : Fin n)] =
      (Vector.unit (R := R) ⟨j, hj⟩)[(⟨a, ha⟩ : Fin n)]
    rw [Matrix.row, Hex.Matrix.getElem_one (i := (⟨j, hj⟩ : Fin n)) (j := (⟨a, ha⟩ : Fin n)),
      Vector.getElem_unit (i := (⟨j, hj⟩ : Fin n)) (j := (⟨a, ha⟩ : Fin n))]
    rfl
  show (gramMatrix (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
    (1 : Matrix R n n)[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)]
  have hgram :
      (gramMatrix (1 : Matrix R n n))[(⟨i, hi⟩ : Fin n)][(⟨j, hj⟩ : Fin n)] =
        ((1 : Matrix R n n).row ⟨i, hi⟩).dotProduct
          ((1 : Matrix R n n).row ⟨j, hj⟩) := by
    unfold gramMatrix ofFn
    simp
  rw [hgram, hrow_i, hrow_j, Vector.dotProduct_unit_unit, getElem_one]

end Matrix

end Hex
