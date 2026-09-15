/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.CommonBounds

public section

namespace Hex.Kronecker

theorem columnsWith_map (f : α → β) (d : α) (m : Nat) (rows : List (List α)) :
    columnsWith (f d) m (rows.map (List.map f)) = (columnsWith d m rows).map (List.map f) := by
  induction m generalizing rows with
  | zero => rfl
  | succ m ih =>
      simp only [columnsWith, List.map_cons, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro row _
        cases row <;> rfl
      · have h : rows.map (List.tail ∘ List.map f) = (rows.map List.tail).map (List.map f) := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro row _
          cases row <;> rfl
        rw [h, ih]

theorem columnsWith_int (m : Nat) (rows : List (List Int)) :
    columnsWith 0 m rows = Hex.Matrix.Packed.columns m rows := by
  apply List.ext_getElem
  · rw [columnsWith_length, HexMatrixMathlib.columns_length]
  · intro i hi hj
    have him : i < m := by simpa only [columnsWith_length] using hi
    have h := columnsWith_getD 0 m rows i him
    have hc : Hex.Matrix.Packed.column i rows = rows.map (fun row => row.getD i 0) := by
      clear h hi hj
      induction rows with
      | nil => rfl
      | cons row rows ih => simp only [Hex.Matrix.Packed.column, List.map_cons, ih]
    rw [← hc] at h
    rw [← HexMatrixMathlib.columns_getD m rows i him] at h
    simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using h

theorem packMatrix_eval {k n m : Nat} (s : SizeBound) (hs : s.strides.length = k)
    (a : TermMatrix) (h : matrixShape k n m a = true) :
    packMatrix s a = (matrixPolynomial k a).map (List.map
      (MvPolynomial.eval₂Hom (RingHom.id Int) (fun i => ((2^s.digitBits : Nat):Int)^s.strides.getD i.val 0))) := by
  unfold packMatrix matrixPolynomial
  simp only [List.map_map]
  apply List.map_congr_left
  intro row hr
  have hrow := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 row hr
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro t ht
  exact packTerms_eq_eval₂ _ _ hs t (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hrow).2 t ht)

theorem checkRow_polynomial {k : Nat} (mode : MulMode) (s : SizeBound) (r : Nat)
    (v : Fin k → Int) (row : List (MvPolynomial (Fin k) Int))
    (cols : List (List (MvPolynomial (Fin k) Int))) (cs : List (MvPolynomial (Fin k) Int))
    (h : checkRow mode s r (row.map (MvPolynomial.eval₂Hom (RingHom.id Int) v))
      (cols.map (List.map (MvPolynomial.eval₂Hom (RingHom.id Int) v)))
      (cs.map (MvPolynomial.eval₂Hom (RingHom.id Int) v)) = true) :
    List.Forall₂ (fun p q => MvPolynomial.eval₂Hom (RingHom.id Int) v p =
      MvPolynomial.eval₂Hom (RingHom.id Int) v q) (cols.map (polyDot row)) cs := by
  induction cols generalizing cs with
  | nil => cases cs <;> simp only [List.map_nil, List.map_cons, checkRow, Bool.false_eq_true] at h
           exact .nil
  | cons col cols ih =>
      cases cs with
      | nil => simp [checkRow] at h
      | cons c cs =>
          have h := Bool.and_eq_true_iff.mp h
          apply List.Forall₂.cons _ (ih cs h.2)
          rw [polyDot_eval]
          rw [← dotValue_eq mode s r _ _ (Bool.and_eq_true_iff.mp h.1).1]
          exact eq_of_beq (Bool.and_eq_true_iff.mp h.1).2

theorem checkRows_polynomial {k : Nat} (mode : MulMode) (s : SizeBound) (r : Nat)
    (v : Fin k → Int) (cols rows cs : List (List (MvPolynomial (Fin k) Int)))
    (h : checkRows mode s r
      (cols.map (List.map (MvPolynomial.eval₂Hom (RingHom.id Int) v)))
      (rows.map (List.map (MvPolynomial.eval₂Hom (RingHom.id Int) v)))
      (cs.map (List.map (MvPolynomial.eval₂Hom (RingHom.id Int) v))) = true) :
    List.Forall₂ (List.Forall₂ (fun p q => MvPolynomial.eval₂Hom (RingHom.id Int) v p =
      MvPolynomial.eval₂Hom (RingHom.id Int) v q)) (polyProduct cols rows) cs := by
  induction rows generalizing cs with
  | nil => cases cs <;> simp only [List.map_nil, List.map_cons, checkRows, Bool.false_eq_true] at h
           exact .nil
  | cons row rows ih =>
      cases cs with
      | nil => simp [checkRows] at h
      | cons c cs =>
          have h := Bool.and_eq_true_iff.mp h
          exact .cons (checkRow_polynomial mode s r v row cols c h.1) (ih cs h.2)

end Hex.Kronecker
