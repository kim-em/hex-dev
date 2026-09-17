/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Bound

public section

namespace Hex.Matrix
namespace Dixon

/-- Ceiling Euclidean norm of an integer vector. -/
def norm (b : Vector Int n) : Nat :=
  HexArith.Nat.ceilSqrt (DetBound.sum fun i : Fin n => b[i].natAbs ^ 2)

def normFast (b : Vector Int n) : Nat :=
  HexArith.Nat.ceilSqrt (DetBound.sum fun i : Fin n => let a := b[i].natAbs; a * a)

@[csimp] theorem norm_eq_fast : @norm = @normFast := by
  funext n b
  simp only [norm, normFast, Nat.pow_two]

/-- Product and largest product with one factor omitted. A single pass avoids
division by zero and also handles matrices with a zero column. -/
def products (xs : List α) (f : α → Nat) : Nat × Nat :=
  match xs with
  | [] => (1, 0)
  | i :: xs =>
    let (p, q) := products xs f
    let a := f i
    (a * p, max p (a * q))

theorem products_fst (xs : List α) (f : α → Nat) :
    (products xs f).1 = (xs.map f).prod := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [products, ih]

theorem products_bound [DecidableEq α] (xs : List α) (f : α → Nat)
    (hn : xs.Nodup) (j : α) (hj : j ∈ xs) (b : Nat) :
    (xs.map fun i => if i = j then b else f i).prod ≤ b * (products xs f).2 := by
  induction xs with
  | nil => simp at hj
  | cons i xs ih =>
    simp only [List.nodup_cons] at hn
    by_cases hij : i = j
    · subst i
      have heq : (xs.map fun i => if i = j then b else f i) = xs.map f := by
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ j := by intro h; subst i; exact hn.1 hi
        simp [hne]
      simp only [List.map_cons, List.prod_cons, ↓reduceIte, heq, products]
      rw [← products_fst xs f]
      exact Nat.mul_le_mul_left b (Nat.le_max_left _ _)
    · have hj' : j ∈ xs := (List.mem_cons.mp hj).resolve_left (Ne.symm hij)
      have h := Nat.mul_le_mul_left (f i) (ih hn.2 hj')
      simp only [List.map_cons, List.prod_cons, hij, ↓reduceIte, products]
      calc
        f i * (xs.map fun i => if i = j then b else f i).prod
            ≤ f i * (b * (products xs f).2) := h
        _ = b * (f i * (products xs f).2) := by ac_rfl
        _ ≤ b * max (products xs f).1 (f i * (products xs f).2) :=
          Nat.mul_le_mul_left b (Nat.le_max_right _ _)

/-- Replace one column by an integer right-hand side. -/
@[expose] def replaceCol (A : Matrix Int n n) (b : Vector Int n) (j : Fin n) : Matrix Int n n :=
  Matrix.ofFn fun i k => if k = j then b[i] else A[(i, k)]

end Dixon

/-- Column Hadamard product with the smallest column factor replaced by the
right-hand-side norm. This bounds every Cramer numerator in O(n²) work. -/
def numeratorBound (A : Matrix Int n n) (b : Vector Int n) : Nat :=
  Dixon.norm b * (Dixon.products (List.finRange n) (fun j => Dixon.norm (A.col j))).2

theorem numeratorBound_spec [LawfulDetBound] (A : Matrix Int n n)
    (b : Vector Int n) (j : Fin n) :
    (det (Dixon.replaceCol A b j)).natAbs ≤ numeratorBound A b := by
  apply Nat.le_trans (LawfulDetBound.natAbs_det_le _)
  apply Nat.le_trans (Nat.min_le_left _ _)
  have hc (k : Fin n) :
      HexArith.Nat.ceilSqrt (DetBound.sum fun i : Fin n =>
        (Dixon.replaceCol A b j)[(i, k)].natAbs ^ 2) =
      if k = j then Dixon.norm b else Dixon.norm (A.col k) := by
    by_cases h : k = j
    · subst k
      simp only [Dixon.replaceCol, getElem_pair_eq_nested, getElem_ofFn, ↓reduceIte,
        Dixon.norm]
    · simp only [Dixon.replaceCol, getElem_pair_eq_nested, getElem_ofFn, h, ↓reduceIte,
        Dixon.norm, getElem_col]
  change DetBound.prod (fun k : Fin n => _) ≤ _
  simp only [hc, DetBound.prod, Fin.foldl_eq_finRange_foldl]
  rw [← List.foldl_map, ← List.prod_eq_foldl]
  exact Dixon.products_bound _ _ (List.nodup_finRange n) j (List.mem_finRange j) _

end Hex.Matrix
