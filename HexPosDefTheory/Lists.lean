/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Structural
public import HexMatrixTheory.Literal
public import HexPosDefTheory.Congruence
public import Mathlib.LinearAlgebra.Matrix.Block

public section

/-! Interpretation of structural certificate arithmetic as finite matrix products. -/

open Matrix

namespace Hex.PosDefTheory

open Hex.PosDef
open Hex.Matrix.Lists (entry all_iff)

namespace Lists

variable {S : Type} {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]

/-- An injective scalar interpretation, including the Boolean comparisons. -/
structure Model (a : PosDef.Lists.Arithmetic S) where
  map : S → R
  injective : Function.Injective map
  zero : map a.zero = 0
  add : ∀ x y, map (a.add x y) = map x + map y
  mul : ∀ x y, map (a.mul x y) = map x * map y
  conj : ∀ x, map (a.conj x) = star (map x)
  eq : ∀ x y, a.eq x y = true ↔ x = y
  positive : ∀ x, a.positive x = true → 0 < map x
  nonpositive : ∀ x, a.nonpositive x = true → map x ≤ 0

variable {a : PosDef.Lists.Arithmetic S} (f : Model (R := R) a)

/-- Decode square row lists, padding only in the mathematical interpretation. -/
@[expose] def matrix (n : Nat) (rows : List (List S)) : _root_.Matrix (Fin n) (Fin n) R :=
  fun i j => f.map (PosDef.Lists.get a rows i j)

@[expose] def vector (n : Nat) (v : List S) : Fin n → R := fun i => f.map (entry a.zero v i)

theorem dot_eq_sum (n : Nat) (xs ys : List S) (hx : xs.length ≤ n) :
    f.map (PosDef.Lists.dot a xs ys) =
      ∑ i : Fin n, f.map (entry a.zero xs i) * f.map (entry a.zero ys i) := by
  induction n generalizing xs ys with
  | zero =>
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [this, PosDef.Lists.dot, f.zero]
  | succ n ih =>
    cases xs with
    | nil => simp [PosDef.Lists.dot, entry, f.zero]
    | cons x xs =>
      cases ys with
      | nil => simp [PosDef.Lists.dot, entry, f.zero]
      | cons y ys =>
        simpa [PosDef.Lists.dot, f.add, f.mul, Fin.sum_univ_succ, entry] using
          congrArg (fun z => f.map x * f.map y + z) (ih xs ys (by simpa using hx))

theorem hermitian {n : Nat} {rows : List (List S)}
    (hs : PosDef.Lists.shape n n rows = true)
    (h : PosDef.Lists.hermitian a n rows = true) : (matrix f n rows).IsHermitian := by
  rw [hermitian_spec a n rows hs] at h
  ext i j
  have hij := (all_iff _ n).mp ((all_iff _ n).mp h i i.isLt) j j.isLt
  have hij := congrArg f.map ((f.eq _ _).mp hij)
  simpa [matrix, Matrix.conjTranspose_apply, f.conj] using hij.symm

theorem dot_column {n : Nat} (rows : List (List S)) (xs : List S)
    (hx : xs.length ≤ n) (j : Fin n) :
    f.map (PosDef.Lists.dot a xs (PosDef.Lists.column a j rows)) =
      ∑ i : Fin n, f.map (entry a.zero xs i) * matrix f n rows i j := by
  rw [dot_eq_sum f n xs _ hx]
  simp only [column_entry, matrix]

theorem mul_apply {n : Nat} (rows ts : List (List S)) (i j : Fin n)
    (ht : (entry [] ts i).length ≤ n) :
    (matrix f n ts * matrix f n rows) i j =
      f.map (PosDef.Lists.dot a (entry [] ts i) (PosDef.Lists.column a j rows)) := by
  simpa only [Matrix.mul_apply, matrix, PosDef.Lists.get] using
    (dot_column f rows (entry [] ts i) ht j).symm

theorem triangularShape_row (k : Nat) (rows : List (List S))
    (h : PosDef.Lists.triangularShape k rows = true) (i : Nat) (hi : i < rows.length) :
    (entry [] rows i).length = k + i + 1 := by
  induction rows generalizing k i with
  | nil => simp at hi
  | cons row rows ih =>
    simp only [PosDef.Lists.triangularShape, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => simpa [entry] using h.1
    | succ i =>
      simpa [entry, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (k + 1) h.2 i (by simpa using hi)

/-- The triangular checker establishes exactly the congruence it advertises. -/
theorem triangular_congruence [NoZeroDivisors R] [Nontrivial R] {n : Nat}
    {rows ts : List (List S)} (hs : PosDef.Lists.shape n n rows = true)
    (h : PosDef.Lists.triangular a n rows ts = true) :
    (matrix f n rows).IsHermitian ∧ (matrix f n ts).det ≠ 0 ∧
      ∃ d : Fin n → R, (∀ i, 0 < d i) ∧
        matrix f n ts * matrix f n rows * (matrix f n ts)ᴴ = Matrix.diagonal d := by
  simp only [triangular_spec, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hlen, hshape⟩, hherm⟩, hrows⟩ := h
  have hlen' (i : Fin n) : (entry [] ts i).length = i.val + 1 := by
    simpa using triangularShape_row 0 ts hshape i (by omega)
  let T := matrix f n ts
  let B := matrix f n rows
  have hB : B.IsHermitian := hermitian f hs hherm
  have hlower : T.IsLowerTriangular := by
    intro i j hij
    change f.map (entry a.zero (entry [] ts i) j) = 0
    rw [Hex.Matrix.Lists.entry_eq_getD,
      HexMatrixTheory.getD_eq_default' _ _ _ (by simpa [hlen' i] using hij)]
    exact f.zero
  have hr (i : Fin n) := (all_iff _ n).mp hrows i i.isLt
  have hupper : (T * B).IsUpperTriangular := by
    intro i j hij
    rw [mul_apply f rows ts i j (by rw [hlen' i]; omega)]
    have hz := (all_iff _ i.val).mp (Bool.and_eq_true_iff.mp (hr i)).1 j hij
    rw [(f.eq _ _).mp hz, f.zero]
  have hd (i : Fin n) : 0 < (T * B) i i * star (T i i) := by
    rw [mul_apply f rows ts i i (by rw [hlen' i]; omega)]
    simpa only [T, matrix, PosDef.Lists.get, f.mul, f.conj] using
      f.positive _ (Bool.and_eq_true_iff.mp (hr i)).2
  have hdet : T.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular T hlower]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hi
    have := hd i
    simp [hi] at this
  let C := T * B * Tᴴ
  have hC : C.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose T hB
  have hcu : C.IsUpperTriangular := by
    intro i j hij
    change ∑ k, (T * B) i k * Tᴴ k j = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k < i
    · simp [hupper hk]
    · have hjk : j < k := lt_of_lt_of_le hij (le_of_not_gt hk)
      simp [Matrix.conjTranspose_apply, hlower hjk]
  have hdiag (i : Fin n) : C i i = (T * B) i i * star (T i i) := by
    change ∑ k, (T * B) i k * Tᴴ k i = _
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hj | hj
      · simp [hupper hj]
      · simp [Matrix.conjTranspose_apply, hlower hj]
    · simp
  refine ⟨hB, hdet, fun i => (T * B) i i * star (T i i), hd, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j; simpa using hdiag i
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_or_gt_of_ne hij with hij | hij
    · have he := congrFun (congrFun hC i) j
      simpa only [Matrix.conjTranspose_apply, hcu hij, star_zero] using he.symm
    · exact hcu hij

theorem triangular_sound [NoZeroDivisors R] [Nontrivial R] [StarOrderedRing R]
    {n : Nat} {rows ts : List (List S)}
    (hs : PosDef.Lists.shape n n rows = true)
    (h : PosDef.Lists.triangular a n rows ts = true)
    (reflect : ∀ (c q : R), c ≠ 0 → 0 < star c * q * c → 0 < q) :
    (matrix f n rows).PosDef := by
  obtain ⟨hB, hdet, d, hd, he⟩ := triangular_congruence f hs h
  apply posDef_of_congruence hB hdet (T := matrix f n ts) _ reflect
  rw [he]
  exact Matrix.PosDef.diagonal hd

include f in
theorem conj_zero : a.conj a.zero = a.zero := by
  apply f.injective
  simp [f.conj, f.zero]

theorem entry_map (g : S → S) (hg : g a.zero = a.zero) (v : List S) (i : Nat) :
    entry a.zero (v.map g) i = g (entry a.zero v i) := by
  induction v generalizing i with
  | nil => simp [entry, hg]
  | cons x xs ih => cases i <;> simp [entry, ih]

theorem mulVec_entry {n : Nat} {rows : List (List S)} (v : List S)
    (h : PosDef.Lists.shape n n rows = true) (i : Fin n) :
    f.map (entry a.zero (PosDef.Lists.mulVec a rows v) i) =
      (matrix f n rows *ᵥ vector f n v) i := by
  have hr := (shape_iff n n rows).mp h
  simp only [PosDef.Lists.mulVec, Hex.Matrix.Lists.entry_eq_getD]
  rw [HexMatrixTheory.getD_eq_getElem' _ _ _ (by simp [hr.1]),
    List.getElem_map]
  have hd := dot_eq_sum f n (entry [] rows i) v (le_of_eq (row_length h i))
  rw [Hex.Matrix.Lists.entry_eq_getD,
    HexMatrixTheory.getD_eq_getElem' _ _ _ (by omega)] at hd
  simpa only [matrix, vector, PosDef.Lists.get, Hex.Matrix.Lists.entry_eq_getD,
    _root_.Matrix.mulVec, dotProduct,
    HexMatrixTheory.getD_eq_getElem' rows i [] (by omega)] using hd

theorem quadratic_eq {n : Nat} {rows : List (List S)} {v : List S}
    (h : PosDef.Lists.shape n n rows = true) (hv : v.length = n) :
    f.map (PosDef.Lists.dot a (v.map a.conj) (PosDef.Lists.mulVec a rows v)) =
      star (vector f n v) ⬝ᵥ (matrix f n rows *ᵥ vector f n v) := by
  rw [dot_eq_sum f n _ _ (by simp [hv])]
  apply Finset.sum_congr rfl
  intro i _
  rw [entry_map a.conj (conj_zero f), f.conj, mulVec_entry f v h i]
  rfl

/-- Negative certificate soundness does not assume that the producer supplied the witness. -/
theorem negative_sound {n : Nat} {rows : List (List S)} {c : NegativeCert S}
    (hshape : PosDef.Lists.shape n n rows = true)
    (h : PosDef.Lists.negative a n rows c = true) : ¬ (matrix f n rows).PosDef := by
  intro hB
  cases c with
  | notHermitian i j =>
    simp only [PosDef.Lists.negative, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hi, hj⟩, hne⟩ := h
    have he := congrFun (congrFun hB.isHermitian ⟨i, hi⟩) ⟨j, hj⟩
    have hs : PosDef.Lists.get a rows i j = a.conj (PosDef.Lists.get a rows j i) := by
      apply f.injective
      simpa only [matrix, Matrix.conjTranspose_apply, f.conj] using he.symm
    have ht := (f.eq _ _).mpr hs
    simp [ht] at hne
  | nonpositive v =>
    simp only [PosDef.Lists.negative, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨hv, hn⟩, hq⟩ := h
    obtain ⟨x, hx, hxn⟩ := List.any_eq_true.mp hn
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hxn : v[i] ≠ a.zero := by
      intro he
      have ht := (f.eq _ _).mpr he
      simp [ht] at hxn
    have hne : vector f n v ≠ 0 := by
      intro hz
      have he := congrFun hz (⟨i, by omega⟩ : Fin n)
      have hm : f.map v[i] = f.map a.zero := by
        simpa only [vector, Hex.Matrix.Lists.entry_eq_getD,
          HexMatrixTheory.getD_eq_getElem' _ _ _ hi, Pi.zero_apply, f.zero] using he
      exact hxn (f.injective hm)
    have hq := f.nonpositive _ hq
    rw [quadratic_eq f hshape hv] at hq
    exact (not_lt_of_ge hq) (hB.dotProduct_mulVec_pos hne)

end Lists

end Hex.PosDefTheory
