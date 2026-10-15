/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDef.Certificate
public import HexMatrixTheory.Literal

public section

/-! Structural traversal and indexed descriptions of certificate checks. -/

namespace Hex.PosDefTheory.Lists

open Hex.PosDef
open Hex.Matrix.Lists (entry all all_iff)

variable {S : Type} {a : PosDef.Lists.Arithmetic S}

theorem shape_iff (n m : Nat) (rows : List (List S)) :
    PosDef.Lists.shape n m rows = true ↔
      rows.length = n ∧ ∀ row ∈ rows, row.length = m := by
  simp [PosDef.Lists.shape, List.all_eq_true]

theorem row_length {n m : Nat} {rows : List (List S)}
    (h : PosDef.Lists.shape n m rows = true) (i : Fin n) :
    (entry [] rows i).length = m := by
  obtain ⟨hn, hm⟩ := (shape_iff n m rows).mp h
  rw [Hex.Matrix.Lists.entry_eq_getD, HexMatrixTheory.getD_eq_getElem' _ _ _ (by omega)]
  exact hm _ (List.getElem_mem (by omega))

theorem column_entry (rows : List (List S)) (i j : Nat) :
    entry a.zero (PosDef.Lists.column a j rows) i = PosDef.Lists.get a rows i j := by
  induction rows generalizing i with
  | nil => cases i <;> rfl
  | cons row rows ih => cases i <;> simp [PosDef.Lists.column, PosDef.Lists.get, entry, ih]

theorem columns_length (n : Nat) (rows : List (List S)) :
    (PosDef.Lists.columns a n rows).length = n := by
  induction n generalizing rows <;> simp [PosDef.Lists.columns, *]

theorem column_map (j : Nat) (rows : List (List S)) :
    PosDef.Lists.column a j rows = rows.map (fun r => entry a.zero r j) := by
  induction rows <;> simp [PosDef.Lists.column, *]

theorem columns_entry (n : Nat) (rows : List (List S)) (j : Nat) (hj : j < n) :
    entry [] (PosDef.Lists.columns a n rows) j = PosDef.Lists.column a j rows := by
  induction n generalizing rows j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero =>
      simp only [PosDef.Lists.columns, entry, column_map]
      congr 1
      funext row
      cases row <;> rfl
    | succ j =>
      rw [PosDef.Lists.columns, entry, ih _ j (by omega), column_map, column_map, List.map_map]
      congr 1
      funext row
      cases row <;> rfl

theorem indexedAll_iff (p : Nat → S → Bool) (xs : List S) (d : S) :
    PosDef.Lists.indexedAll p xs = true ↔ ∀ i, i < xs.length → p i (entry d xs i) = true := by
  simp only [PosDef.Lists.indexedAll, List.all_eq_true]
  constructor
  · intro h i hi
    have hm : (entry d xs i, i) ∈ xs.zipIdx := by
      simp [List.mk_mem_zipIdx_iff_getElem?, Hex.Matrix.Lists.entry_eq_getD,
        List.getD_eq_getElem?_getD, hi]
    exact h _ hm
  · intro h pair hm
    obtain ⟨x,i⟩ := pair
    have he := List.mk_mem_zipIdx_iff_getElem?.mp hm
    obtain ⟨hi,hx⟩ := List.getElem?_eq_some_iff.mp he
    have : entry d xs i = x := by simp [Hex.Matrix.Lists.entry_eq_getD, hi, hx]
    simpa only [this] using h i hi

theorem paired_iff (p : S → S → Bool) (xs ys : List S) (d : S)
    (hlen : xs.length = ys.length) :
    PosDef.Lists.paired p xs ys = true ↔
      ∀ i, i < xs.length → p (entry d xs i) (entry d ys i) = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [PosDef.Lists.paired]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [PosDef.Lists.paired, Bool.and_eq_true_iff, ih ys hlen]
      constructor
      · rintro ⟨h,ht⟩ i hi
        cases i with
        | zero => exact h
        | succ i => exact ht i (by simpa using hi)
      · intro h
        exact ⟨h 0 (by simp), fun i hi => h (i+1) (by simpa using hi)⟩

theorem zipAll_iff {T : Type} (p : S → T → Bool) (xs : List S) (ys : List T)
    (dx : S) (dy : T) (hlen : xs.length = ys.length) :
    (xs.zip ys).all (fun (x,y) => p x y) = true ↔
      ∀ i, i < xs.length → p (entry dx xs i) (entry dy ys i) = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true_iff]
      rw [ih ys hlen]
      constructor
      · rintro ⟨h,ht⟩ i hi
        cases i with
        | zero => exact h
        | succ i => exact ht i (by simpa using hi)
      · intro h
        exact ⟨h 0 (by simp), fun i hi => h (i+1) (by simpa using hi)⟩

theorem all_congr (p q : Nat → Bool) (n : Nat)
    (h : ∀ i, i < n → p i = q i) : all p n = all q n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [all, all, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- A quadratic structural symmetry pass has the usual indexed meaning. -/
theorem hermitian_spec (a : PosDef.Lists.Arithmetic S) (n : Nat) (rows : List (List S))
    (hs : PosDef.Lists.shape n n rows = true) :
    PosDef.Lists.hermitian a n rows =
      all (fun i => all (fun j => a.eq (PosDef.Lists.get a rows i j)
        (a.conj (PosDef.Lists.get a rows j i))) n) n := by
  have hlen := (shape_iff n n rows).mp hs |>.1
  apply Bool.eq_iff_iff.mpr
  rw [PosDef.Lists.hermitian, PosDef.Lists.conjugateEq, zipAll_iff _ _ _ [] [] (by rw [columns_length, hlen]),
    hlen, all_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [columns_entry n rows i hi,
    paired_iff _ _ _ a.zero (by rw [row_length hs ⟨i,hi⟩, column_map, List.length_map, hlen]),
    row_length hs ⟨i,hi⟩, all_iff]
  simp only [column_entry, PosDef.Lists.get]

/-- Structural off-diagonal comparisons visit each matrix entry once. -/
theorem offDiagonal_spec (n : Nat) (rows : List (List Int))
    (hs : PosDef.Lists.shape n n rows = true) :
    PosDef.Lists.indexedAll (fun i row => PosDef.Lists.indexedAll
      (fun j x => Nat.beq i j || decide (x ≤ 0)) row) rows =
    all (fun i => all (fun j => Nat.beq i j ||
      decide (PosDef.Lists.get PosDef.Lists.intArithmetic rows i j ≤ 0)) n) n := by
  apply Bool.eq_iff_iff.mpr
  rw [indexedAll_iff _ _ [], (shape_iff n n rows).mp hs |>.1, all_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [indexedAll_iff _ _ 0, row_length hs ⟨i,hi⟩, all_iff]
  rfl

/-- Transposition is shared across all triangular dot products. -/
theorem triangular_spec (a : PosDef.Lists.Arithmetic S) (n : Nat)
    (rows transform : List (List S)) :
    PosDef.Lists.triangular a n rows transform =
      (Nat.beq transform.length n && PosDef.Lists.triangularShape 0 transform &&
      PosDef.Lists.hermitian a n rows && all (fun i =>
        let t := entry [] transform i
        all (fun j => a.eq (PosDef.Lists.dot a t (PosDef.Lists.column a j rows)) a.zero) i &&
        a.positive (a.mul (PosDef.Lists.dot a t (PosDef.Lists.column a i rows))
          (a.conj (entry a.zero t i)))) n) := by
  unfold PosDef.Lists.triangular
  apply congrArg (fun b => _ && b)
  apply all_congr
  intro i hi
  dsimp only
  rw [columns_entry n rows i hi]
  congr 1
  apply all_congr
  intro j hj
  rw [columns_entry n rows j (by omega)]

end Hex.PosDefTheory.Lists
