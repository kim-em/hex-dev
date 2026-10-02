/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.MatrixModel
public import Mathlib.Data.List.Forall2

public section

namespace Hex.Kronecker

@[expose] def columnsWith (d : α) : Nat → List (List α) → List (List α)
  | 0, _ => []
  | m+1, rows => rows.map (List.headD · d) :: columnsWith d m (rows.map List.tail)

theorem boundColumns_eq (k m : Nat) (rows : List (List Bounds)) :
    boundColumns k m rows = columnsWith (Bounds.zero k) m rows := by
  induction m generalizing rows <;> simp [boundColumns, columnsWith, *]

theorem columnsWith_length (d : α) (m : Nat) (rows : List (List α)) :
    (columnsWith d m rows).length = m := by
  induction m generalizing rows <;> simp [columnsWith, *]

theorem columnsWith_getD (d : α) (m : Nat) (rows : List (List α)) (j : Nat) (hj : j < m) :
    (columnsWith d m rows).getD j [] = rows.map (fun row => row.getD j d) := by
  induction m generalizing rows j with
  | zero => omega
  | succ m ih =>
      cases j with
      | zero =>
          simp only [columnsWith, List.getD_cons_zero]
          congr 1
          funext row
          cases row <;> rfl
      | succ j =>
          rw [columnsWith, List.getD_cons_succ, ih _ j (by omega), List.map_map]
          congr 1
          funext row
          cases row <;> rfl

theorem rel_getD {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) (dx : α) (dy : β) (hd : r dx dy) (i : Nat) :
    r (xs.getD i dx) (ys.getD i dy) := by
  induction h generalizing i with
  | nil => exact hd
  | cons h ht ih => cases i with
    | zero => exact h
    | succ i => exact ih i

theorem columnsWith_rel {r : α → β → Prop} (dx : α) (dy : β) (hd : r dx dy)
    (m : Nat) {xs : List (List α)} {ys : List (List β)} (h : List.Forall₂ (List.Forall₂ r) xs ys) :
    List.Forall₂ (List.Forall₂ r) (columnsWith dx m xs) (columnsWith dy m ys) := by
  induction m generalizing xs ys with
  | zero => exact .nil
  | succ m ih =>
      apply List.Forall₂.cons
      · apply List.rel_map _ h
        intro a b hab
        simpa only [List.headD_eq_getD] using rel_getD hab dx dy hd 0
      · apply ih
        apply List.rel_map _ h
        intro a b hab
        cases hab with
        | nil => exact .nil
        | cons _ ht => exact ht

theorem map_bounded (cap k : Nat) (ts : List (Hex.MvPoly.Kernel.PolyList Int))
    (h : ∀ t ∈ ts, termShape k t = true) :
    List.Forall₂ (Bounded cap) (ts.map (termBounds cap k)) (ts.map (termsPolynomial k)) := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih =>
      exact .cons (terms_bounded cap k t (h t (by simp)))
        (ih fun t ht => h t (by simp [ht]))

@[expose] noncomputable def matrixPolynomial (k : Nat) (a : TermMatrix) :
    List (List (MvPolynomial (Fin k) Int)) := a.map (List.map (termsPolynomial k))

theorem matrix_bounded (cap k n m : Nat) (a : TermMatrix) (h : matrixShape k n m a = true) :
    List.Forall₂ (List.Forall₂ (Bounded cap)) (matrixBounds cap k a) (matrixPolynomial k a) := by
  have hrows := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2
  clear h
  unfold matrixBounds matrixPolynomial
  induction a with
  | nil => exact .nil
  | cons row rows ih =>
      apply List.Forall₂.cons
      · apply map_bounded
        exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hrows row (by simp))).2
      · exact ih (fun row hr => hrows row (by simp [hr]))

@[expose] noncomputable def polyProduct {k : Nat} (cols rows : List (List (MvPolynomial (Fin k) Int))) :
    List (List (MvPolynomial (Fin k) Int)) := rows.map (fun row => cols.map (polyDot row))

theorem product_bounded {cap k : Nat} {cols rows : List (List Bounds)}
    {pc pr : List (List (MvPolynomial (Fin k) Int))}
    (hc : List.Forall₂ (List.Forall₂ (Bounded cap)) cols pc)
    (hr : List.Forall₂ (List.Forall₂ (Bounded cap)) rows pr) :
    List.Forall₂ (List.Forall₂ (Bounded cap)) (productBounds cap k cols rows) (polyProduct pc pr) := by
  induction hr with
  | nil => exact .nil
  | cons h ht ih =>
      apply List.Forall₂.cons _ ih
      clear ht ih
      induction hc with
      | nil => exact .nil
      | cons g gt ih => exact .cons (polyDot_bounded h g) ih

theorem polyColumns_bounded (cap k n m : Nat) (a : TermMatrix) (h : matrixShape k n m a = true) :
    List.Forall₂ (List.Forall₂ (Bounded cap)) (boundColumns k m (matrixBounds cap k a))
      (columnsWith 0 m (matrixPolynomial k a)) := by
  rw [boundColumns_eq]
  exact columnsWith_rel _ _ (Bounded.zero cap k) m (matrix_bounded cap k n m a h)

end Hex.Kronecker
