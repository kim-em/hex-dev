/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.MulSound

public section

namespace Hex.Kronecker

theorem map_getD_of_lt (f : α → β) (xs : List α) (dx : α) (dy : β) (i : Nat) (hi : i < xs.length) :
    (xs.map f).getD i dy = f (xs.getD i dx) := by
  rw [List.getD_eq_getElem (xs.map f) dy (by simpa only [List.length_map] using hi),
    List.getD_eq_getElem xs dx hi, List.getElem_map]

theorem matrixShape_rows {k n m : Nat} {a : TermMatrix} (h : matrixShape k n m a = true) : a.length = n :=
  eq_of_beq (Bool.and_eq_true_iff.mp h).1

theorem matrixShape_row {k n m : Nat} {a : TermMatrix} (h : matrixShape k n m a = true)
    (i : Nat) (hi : i < n) : (a.getD i []).length = m := by
  have hi' : i < a.length := by rwa [matrixShape_rows h]
  have hm : a.getD i [] ∈ a := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  exact eq_of_beq (Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 _ hm)).1

theorem matrixPolynomial_getD (k : Nat) (a : TermMatrix) (i j : Nat) :
    ((matrixPolynomial k a).getD i []).getD j 0 = termsPolynomial k ((a.getD i []).getD j []) := by
  unfold matrixPolynomial
  rw [show ([] : List (MvPolynomial (Fin k) Int)) = List.map (termsPolynomial k) [] from rfl,
    List.getD_map]
  rw [← termsPolynomial_nil k, List.getD_map]

theorem polyDot_sum {k : Nat} (r : Nat) (a b : List (MvPolynomial (Fin k) Int))
    (ha : a.length = r) (hb : b.length = r) :
    polyDot a b = ∑ i : Fin r, a.getD i.val 0 * b.getD i.val 0 := by
  induction r generalizing a b with
  | zero =>
      have := List.length_eq_zero_iff.mp ha
      subst a
      simp [polyDot]
  | succ r ih =>
      cases a with
      | nil => simp at ha
      | cons a as =>
          cases b with
          | nil => simp at hb
          | cons b bs =>
              rw [polyDot, Fin.sum_univ_succ, ih as bs (by simpa using ha) (by simpa using hb)]
              rfl

theorem product_entry {k n r m : Nat} {a b : TermMatrix}
    (ha : matrixShape k n r a = true) (hb : matrixShape k r m b = true)
    (i : Fin n) (j : Fin m) :
    ((polyProduct (columnsWith 0 m (matrixPolynomial k b)) (matrixPolynomial k a)).getD i.val []).getD j.val 0 =
      ∑ t : Fin r, termsPolynomial k ((a.getD i.val []).getD t.val []) *
        termsPolynomial k ((b.getD t.val []).getD j.val []) := by
  have hia : i.val < (matrixPolynomial k a).length := by
    simpa only [matrixPolynomial, List.length_map, matrixShape_rows ha] using i.isLt
  have hjb : j.val < (columnsWith (0 : MvPolynomial (Fin k) Int) m (matrixPolynomial k b)).length := by
    simpa only [columnsWith_length] using j.isLt
  rw [polyProduct, map_getD_of_lt _ _ [] [] i.val hia,
    map_getD_of_lt _ _ [] 0 j.val hjb, columnsWith_getD _ _ _ _ j.isLt]
  have hal : ((matrixPolynomial k a).getD i.val []).length = r := by
    rw [matrixPolynomial, map_getD_of_lt _ _ [] [] i.val (by simpa only [matrixShape_rows ha] using i.isLt)]
    simp only [List.length_map, matrixShape_row ha i.val i.isLt]
  have hbl : ((matrixPolynomial k b).map (fun row => row.getD j.val 0)).length = r := by
    simp only [List.length_map, matrixPolynomial, matrixShape_rows hb]
  rw [polyDot_sum r _ _ hal hbl]
  apply Finset.sum_congr rfl
  intro t _
  rw [matrixPolynomial_getD, map_getD_of_lt _ _ [] 0 t.val
    (by simpa only [matrixPolynomial, List.length_map, matrixShape_rows hb] using t.isLt), matrixPolynomial_getD]

/-- Interpret each supplied entry through the established term-list equivalence. -/
@[expose] noncomputable def denoteEntry {R : Type u} [CommRing R] {k : Nat}
    (v : Fin k → R) (a : TermMatrix) (i j : Nat) : R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) v (termsPolynomial k ((a.getD i []).getD j []))

/-- Total finite matrix denotation. Successful shape checks ensure that no
padding entry is used by either soundness theorem. -/
@[expose] noncomputable def denoteMatrix (n m : Nat) (R : Type u) [CommRing R] {k : Nat}
    (v : Fin k → R) (a : TermMatrix) : _root_.Matrix (Fin n) (Fin m) R :=
  fun i j => denoteEntry v a i.val j.val

/-- Entrywise soundness of both the plain and the signed-packed product checks. -/
theorem checkMulTerms_entry {budget : Budget} {mode : MulMode} {k n r m : Nat}
    {a b c : TermMatrix} (h : checkMulTerms budget mode k n r m a b c = true) :
    ∀ {R : Type u} [CommRing R] (v : Fin k → R) (i : Fin n) (j : Fin m),
      (∑ t : Fin r, denoteEntry v a i.val t.val * denoteEntry v b t.val j.val) =
        denoteEntry v c i.val j.val := by
  intro R _ v i j
  have hw : (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c) = true := by
    by_contra hw
    have hf : (matrixShape k n r a && matrixShape k r m b && matrixShape k n m c) = false :=
      Bool.eq_false_iff.mpr hw
    simp only [checkMulTerms, sizeMulTerms, hf, Bool.not_false, ↓reduceIte, Bool.false_eq_true] at h
  have ha := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
  have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2
  have he := congrArg (fun rows => (rows.getD i.val []).getD j.val 0) (checkMulTerms_polynomial h)
  rw [product_entry ha hb, matrixPolynomial_getD] at he
  have he := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom R) v) he
  simpa only [map_sum, map_mul, denoteEntry] using he

/-- Both multiplication modes certify equality of the finite matrix product. -/
theorem checkMulTerms_sound {budget : Budget} {mode : MulMode} {k n r m : Nat}
    {a b c : TermMatrix} (h : checkMulTerms budget mode k n r m a b c = true) :
    ∀ {R : Type u} [CommRing R] (v : Fin k → R),
      denoteMatrix n r R v a * denoteMatrix r m R v b = denoteMatrix n m R v c := by
  intro R _ v
  funext i j
  simpa only [_root_.Matrix.mul_apply, denoteMatrix] using checkMulTerms_entry h v i j

end Hex.Kronecker
