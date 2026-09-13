/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Lists
public import HexMatrixMathlib.Literal
public import HexMatrixMathlib.Algebra

public section

/-! Transport of structural integer list products to Mathlib matrices. -/

namespace HexMatrixMathlib

open Hex.Matrix.Lists

theorem shape_iff (n m : Nat) (rows : List (List Int)) :
    shape n m rows = true ↔ rows.length = n ∧ ∀ row ∈ rows, row.length = m := by
  simp [shape, List.all_eq_true]

theorem row_length {n m : Nat} {rows : List (List Int)}
    (h : shape n m rows = true) (i : Fin n) :
    (entry [] rows i).length = m := by
  obtain ⟨hn, hm⟩ := (shape_iff n m rows).mp h
  rw [entry_eq_getD, getD_eq_getElem' _ _ _ (by omega)]
  exact hm _ (List.getElem_mem (by omega))

theorem dot_eq_sum (a b : List Int) :
    dot a b = ∑ i : Fin a.length, a.getD i 0 * b.getD i 0 := by
  induction a generalizing b with
  | nil => simp [dot]
  | cons x xs ih =>
    cases b with
    | nil => simp [dot]
    | cons y ys => simp [dot, Fin.sum_univ_succ, ih]

theorem ListProducts.column_getD (j : Nat) (rows : List (List Int)) (i : Nat) :
    (column j rows).getD i 0 = (rows.getD i []).getD j 0 := by
  induction rows generalizing i with
  | nil => simp [column]
  | cons row rows ih =>
    cases i with
    | zero => simp only [column, List.getD_cons_zero, entry_eq_getD]
    | succ i => simpa only [column, List.getD_cons_succ] using ih i

/-- Accepted list products give mathematical matrix products; decoding is
used only by this theorem, outside the Boolean reduction path. -/
theorem mul_of_product {n k m : Nat} {a b : List (List Int)}
    {c : Nat → Nat → Int} (ha : shape n k a = true)
    (hc : product n m a b c = true) :
    ofLists n k a * ofLists k m b = fun (i : Fin n) (j : Fin m) => c i j := by
  have hc := (all_iff _ n).mp hc
  ext i j
  have hij := of_decide_eq_true ((all_iff _ m).mp (hc i i.isLt) j j.isLt)
  have hd := dot_eq_sum (entry [] a i) (column j b)
  rw [row_length ha i] at hd
  calc
    (ofLists n k a * ofLists k m b) i j =
        ∑ x : Fin k, (a.getD i []).getD x 0 * (b.getD x []).getD j 0 := by
      simp only [Matrix.mul_apply, ofLists_apply]
    _ = dot (entry [] a i) (column j b) := by
      simpa only [entry_eq_getD, ListProducts.column_getD] using hd.symm
    _ = c i j := hij

/-- Decode lists to the executable matrix representation for reference
certificate soundness. This definition is never reduced by a checker. -/
def matrixOfLists (n m : Nat) (rows : List (List Int)) : Hex.Matrix Int n m :=
  matrixEquiv.symm (ofLists n m rows)

@[simp] theorem matrixEquiv_matrixOfLists (n m : Nat) (rows : List (List Int)) :
    matrixEquiv (matrixOfLists n m rows) = ofLists n m rows :=
  matrixEquiv.apply_symm_apply _

theorem matrixOfLists_get (n m : Nat) (rows : List (List Int)) (i : Fin n) (j : Fin m) :
    (matrixOfLists n m rows)[i][j] = get rows i j := by
  change (matrixEquiv.symm (ofLists n m rows))[i.val][j.val] = _
  rw [matrixEquiv_symm_apply, ofLists_apply]
  simp only [Hex.Matrix.Lists.get, entry_eq_getD]

theorem matrix_mul_of_product {n k m : Nat} {a b d : List (List Int)}
    (ha : shape n k a = true) (h : product n m a b (get d) = true) :
    matrixOfLists n k a * matrixOfLists k m b = matrixOfLists n m d := by
  apply matrixEquiv.injective
  rw [matrixEquiv_mul, matrixEquiv_matrixOfLists, matrixEquiv_matrixOfLists,
    matrixEquiv_matrixOfLists, mul_of_product ha h]
  ext i j
  simp [Hex.Matrix.Lists.get, entry_eq_getD, ofLists_apply]

theorem matrix_inverse_of_product {n : Nat} {a b : List (List Int)}
    (ha : shape n n a = true) (h : product n n a b identity = true) :
    matrixOfLists n n a * matrixOfLists n n b = Hex.Matrix.identity n := by
  apply matrixEquiv.injective
  rw [matrixEquiv_mul, matrixEquiv_matrixOfLists, matrixEquiv_matrixOfLists,
    mul_of_product ha h]
  change (fun (i j : Fin n) => identity i j) = matrixEquiv (1 : Hex.Matrix Int n n)
  rw [matrixEquiv_one]
  ext i j
  simp [identity, Matrix.one_apply, Fin.ext_iff]

end HexMatrixMathlib
