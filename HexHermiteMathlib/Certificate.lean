/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexHermiteMathlib.Span
public import HexMatrixMathlib.ListProducts
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Basis.Basic

public section

/-! Row-lattice bases and reduced residuals from arbitrary Hermite certificates. -/

namespace HexHermiteMathlib.Checked

open HexMatrixMathlib Module

variable {n m : Nat} {A : Hex.Matrix Int n m}
  {D : Hex.Matrix.RowEchelonData Int n m}

/-- The first, nonzero rows of a checked Hermite form. -/
@[expose] def rows (h : Hex.Matrix.IsHNF A D) : Fin D.rank → (Fin m → ℤ) :=
  fun i => (matrixEquiv D.echelon).row (h.toIsEchelonForm.pivotRow i)

/-- A checked HNF generates the input row lattice. -/
theorem span_form (h : Hex.Matrix.IsHNF A D) :
    Submodule.span ℤ (Set.range (matrixEquiv D.echelon).row) =
      Submodule.span ℤ (Set.range (matrixEquiv A).row) := by
  ext x
  let v : Vector Int m := vectorEquiv.symm x
  have hv : vectorEquiv v = x := vectorEquiv.apply_symm_apply x
  rw [← hv, HexHermiteMathlib.mem_span_iff, HexHermiteMathlib.mem_span_iff]
  exact (h.memLattice_iff v).symm

/-- Removing the zero trailing rows preserves the row span. -/
theorem span_rows (h : Hex.Matrix.IsHNF A D) :
    Submodule.span ℤ (Set.range (rows h)) =
      Submodule.span ℤ (Set.range (matrixEquiv A).row) := by
  rw [← span_form h]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span ⟨h.toIsEchelonForm.pivotRow i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    by_cases hi : i.val < D.rank
    · have he : h.toIsEchelonForm.pivotRow ⟨i.val, hi⟩ = i := Fin.ext rfl
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, by simp only [rows, he]⟩
    · have hz := h.zero_row i (by omega)
      have he : (matrixEquiv D.echelon).row i = 0 := by
        rw [matrixEquiv_row]
        change vectorEquiv D.echelon[i] = 0
        rw [hz, vectorEquiv_zero]
      rw [he]
      exact Submodule.zero_mem _

/-- The positive upper-triangular pivot minor makes the HNF rows independent. -/
theorem rows_independent (h : Hex.Matrix.IsHNF A D) : LinearIndependent ℤ (rows h) := by
  let B : Matrix (Fin D.rank) (Fin D.rank) ℤ :=
    fun i j => rows h i (D.pivotCols.get j)
  have ht : B.IsUpperTriangular := by
    intro i j hij
    change (matrixEquiv D.echelon) (h.toIsEchelonForm.pivotRow i) (D.pivotCols.get j) = 0
    rw [matrixEquiv_apply]
    exact h.below_pivot_zero j (h.toIsEchelonForm.pivotRow i) hij
  have hd : B.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    change (matrixEquiv D.echelon) (h.toIsEchelonForm.pivotRow i) (D.pivotCols.get i) ≠ 0
    rw [matrixEquiv_apply]
    exact Int.ne_of_gt (h.pivot_pos i)
  have hl := Matrix.linearIndependent_rows_of_det_ne_zero hd
  rw [Fintype.linearIndependent_iff] at hl ⊢
  intro c hc i
  apply hl c ?_ i
  funext j
  have he := congrFun hc (D.pivotCols.get j)
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, B] using he

/-- A basis of the original row lattice whose vectors are the nonzero HNF rows. -/
noncomputable def basis (h : Hex.Matrix.IsHNF A D) :
    Basis (Fin D.rank) ℤ (Submodule.span ℤ (Set.range (matrixEquiv A).row)) :=
  (Basis.span (rows_independent h)).map (LinearEquiv.ofEq _ _ (span_rows h))

theorem basis_row (h : Hex.Matrix.IsHNF A D) (i : Fin D.rank) :
    (basis h i : Fin m → ℤ) = rows h i := by
  simp [basis]

/-- A reduced vector in the HNF row lattice vanishes, including when its
support lies entirely outside the pivot columns or the rank is zero. -/
theorem reduced_zero (h : Hex.Matrix.IsHNF A D) (v : Vector Int m)
    (hv : D.echelon.memLattice v)
    (hb : ∀ i : Fin D.rank, 0 ≤ v[D.pivotCols.get i] ∧
      v[D.pivotCols.get i] < D.echelon[h.toIsEchelonForm.pivotRow i][D.pivotCols.get i]) :
    v = 0 := by
  apply h.eq_zero_of_pivots hv
  have aux : ∀ k (hk : k < D.rank), v[D.pivotCols.get ⟨k, hk⟩] = 0 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      let i : Fin D.rank := ⟨k, hk⟩
      obtain ⟨a, ha⟩ := h.pivot_factor hv i (fun j hj => ih j.val hj j.isLt)
      have hd : D.echelon[h.toIsEchelonForm.pivotRow i][D.pivotCols.get i] ∣
          v[D.pivotCols.get i] := ⟨a, by rw [ha, Int.mul_comm]⟩
      have hz := Int.emod_eq_zero_of_dvd hd
      rw [Int.emod_eq_of_lt (hb i).1 (hb i).2] at hz
      exact hz
  exact fun i => aux i.val i.isLt

end HexHermiteMathlib.Checked

namespace HexHermiteMathlib

open HexMatrixMathlib Hex.Matrix.Lists

theorem pivot_bound {n m : Nat} (c : Hex.Matrix.HermiteWitness)
    (hf : c.checkForm n m = true) (i : Fin c.rank) : entry 0 c.pivots i < m := by
  simp only [Hex.Matrix.HermiteWitness.checkForm, Bool.and_eq_true, and_assoc] at hf
  exact Nat.blt_eq.mp ((all_iff _ _).mp hf.2.2.2.1 i i.isLt)

/-- Decode the checked pivot indices and matrices for reference soundness. -/
@[expose, reducible] def decodeWitness (n m : Nat) (c : Hex.Matrix.HermiteWitness)
    (hf : c.checkForm n m = true) : Hex.Matrix.RowEchelonData Int n m where
  rank := c.rank
  echelon := matrixOfLists n m c.form
  transform := matrixOfLists n n c.transform
  pivotCols := Vector.ofFn fun i => ⟨entry 0 c.pivots i, pivot_bound c hf i⟩

theorem decode_pivot (n m : Nat) (c : Hex.Matrix.HermiteWitness)
    (hf : c.checkForm n m = true) (i : Fin c.rank) :
    (decodeWitness n m c hf).pivotCols.get i = ⟨entry 0 c.pivots i, pivot_bound c hf i⟩ := by
  change (Vector.ofFn (fun i : Fin c.rank =>
    (⟨entry 0 c.pivots i, pivot_bound c hf i⟩ : Fin m)))[i.val] = _
  rw [Vector.getElem_ofFn]

/-- The natural-index list clauses imply every clause of the reference HNF shape. -/
theorem form_of_check {n m : Nat} (c : Hex.Matrix.HermiteWitness)
    (hf : c.checkForm n m = true) :
    Hex.Matrix.HNFForm (matrixOfLists n m c.form) c.rank
      (decodeWitness n m c hf).pivotCols := by
  have hs := hf
  simp only [Hex.Matrix.HermiteWitness.checkForm, Bool.and_eq_true, Nat.ble_eq,
    Nat.beq_eq, all_iff, decide_eq_true_eq, and_assoc] at hs
  obtain ⟨hrn, hrm, _, _, sorted, row, zero⟩ := hs
  refine ⟨hrn, hrm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [decode_pivot, decode_pivot]
    have hh := sorted i.val i.isLt j.val j.isLt
    have hb : Nat.blt i.val j.val = true := Nat.blt_eq.mpr hij
    simpa [hb] using hh
  · intro i r hri j hj
    rw [decode_pivot] at hj
    rw [Hex.Matrix.getElem_pair_eq_nested, matrixOfLists_get, hri]
    have hh := (row i.val i.isLt).2.1 j.val j.isLt
    have hb : Nat.blt j.val (entry 0 c.pivots i) = true := Nat.blt_eq.mpr hj
    simpa [hb] using hh
  · intro i r hri
    rw [decode_pivot, Hex.Matrix.getElem_pair_eq_nested, matrixOfLists_get]
    simpa only [hri, Fin.val_mk] using (row i.val i.isLt).1
  · intro i r hir
    rw [decode_pivot, Hex.Matrix.getElem_pair_eq_nested, matrixOfLists_get]
    have hh := ((row i.val i.isLt).2.2 r.val r.isLt).1
    have hb : Nat.blt i.val r.val = true := Nat.blt_eq.mpr hir
    simpa [hb] using hh
  · intro r hr
    have hh := zero r.val r.isLt
    have hb : Nat.ble c.rank r.val = true := Nat.ble_eq.mpr hr
    have hz : all (fun j => decide (Hex.Matrix.Lists.get c.form r.val j = 0)) m = true := by
      simpa [hb] using hh
    apply Vector.ext
    intro j hj
    change (matrixOfLists n m c.form)[r][(⟨j, hj⟩ : Fin m)] = (0 : Vector Int m)[j]
    rw [matrixOfLists_get, Vector.getElem_zero]
    exact of_decide_eq_true ((all_iff _ _).mp hz j hj)
  · intro i r hri
    rw [decode_pivot, Hex.Matrix.getElem_pair_eq_nested, matrixOfLists_get]
    have hh := ((row i.val i.isLt).2.2 r.val r.isLt).2
    have hb : Nat.blt r.val i.val = true := Nat.blt_eq.mpr hri
    have hh' : 0 ≤ Hex.Matrix.Lists.get c.form r.val (entry 0 c.pivots i) ∧
        Hex.Matrix.Lists.get c.form r.val (entry 0 c.pivots i) <
          Hex.Matrix.Lists.get c.form i.val (entry 0 c.pivots i) := by simpa [hb] using hh
    exact hh'.1
  · intro i r hri p hpi
    rw [decode_pivot, Hex.Matrix.getElem_pair_eq_nested, Hex.Matrix.getElem_pair_eq_nested,
      matrixOfLists_get, matrixOfLists_get]
    have hh := ((row i.val i.isLt).2.2 r.val r.isLt).2
    have hb : Nat.blt r.val i.val = true := Nat.blt_eq.mpr hri
    have hh' : 0 ≤ Hex.Matrix.Lists.get c.form r.val (entry 0 c.pivots i) ∧
        Hex.Matrix.Lists.get c.form r.val (entry 0 c.pivots i) <
          Hex.Matrix.Lists.get c.form i.val (entry 0 c.pivots i) := by simpa [hb] using hh
    simpa only [hpi, Fin.val_mk] using hh'.2

theorem check_form {n m : Nat} (rows : List (List Int)) (c : Hex.Matrix.HermiteWitness)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) : c.checkForm n m = true := by
  simp only [Hex.Matrix.checkHermiteList, Bool.and_eq_true, and_assoc] at hc
  exact hc.2.2.2.2.1

/-- Accepted lists establish the packed reference certificate without reducing it. -/
theorem reference_check {n m : Nat} (rows : List (List Int)) (c : Hex.Matrix.HermiteWitness)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) :
    Hex.Matrix.hnfCert (matrixOfLists n m rows) (matrixOfLists n m c.form)
      (matrixOfLists n n c.transform) (matrixOfLists n n c.inverse) c.rank
      (decodeWitness n m c (check_form rows c hc)).pivotCols = true := by
  have hs := hc
  simp only [Hex.Matrix.checkHermiteList, Bool.and_eq_true, and_assoc] at hs
  obtain ⟨_, _, hu, _, hf, hmul, hinv⟩ := hs
  simp only [Hex.Matrix.hnfCert, Bool.and_eq_true, Hex.Matrix.mulEqCert_iff,
    Hex.Matrix.isHNFForm_iff, and_assoc]
  exact ⟨matrix_mul_of_product hu hmul, matrix_inverse_of_product hu hinv, form_of_check c hf⟩

theorem hermite_of_check {n m : Nat} (rows : List (List Int)) (c : Hex.Matrix.HermiteWitness)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) :
    Hex.Matrix.IsHNF (matrixOfLists n m rows) (decodeWitness n m c (check_form rows c hc)) :=
  Hex.Matrix.hnfCert_sound (reference_check rows c hc)

/-- The row-lattice basis goal accepted by the Hermite frontend. -/
abbrev HermiteBasis {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ) (rank : Nat) :=
  Module.Basis (Fin rank) ℤ (Submodule.span ℤ (Set.range A))

/-- Literal HNF data, with its row lattice, basis and arbitrary-witness certificate. -/
structure HermiteResult {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ) where
  rank : Nat
  rank_le : rank ≤ min n m
  form : Matrix (Fin n) (Fin m) ℤ
  inputRows : List (List Int)
  input_eq : A = ofLists n m inputRows
  witness : Hex.Matrix.HermiteWitness
  rank_eq : rank = witness.rank
  form_eq : form = ofLists n m witness.form
  checked : Hex.Matrix.checkHermiteList n m inputRows witness = true
  hnf : Hex.Matrix.IsHNF (matrixOfLists n m inputRows)
    (decodeWitness n m witness (check_form inputRows witness checked))
  span : Submodule.span ℤ (Set.range form) = Submodule.span ℤ (Set.range A)
  basis : HermiteBasis A rank
  basis_row : ∀ i : Fin rank,
    (basis i : Fin m → ℤ) = form ⟨i.val, lt_of_lt_of_le i.isLt
      (le_trans rank_le (Nat.min_le_left n m))⟩

/-- Construct the row basis and form from a checked list witness. -/
@[expose] noncomputable def hermite_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.HermiteWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) : HermiteResult A := by
  let h := hermite_of_check rows c hc
  have hspan : Submodule.span ℤ (Set.range (matrixEquiv (matrixOfLists n m rows)).row) =
      Submodule.span ℤ (Set.range A) := by
    rw [matrixEquiv_matrixOfLists, ← hA]
    rfl
  let b : HermiteBasis A c.rank :=
    (Checked.basis h).map (LinearEquiv.ofEq _ _ hspan)
  refine
    { rank := c.rank
      rank_le := Nat.le_min.mpr ⟨h.rank_le_n, h.rank_le_m⟩
      form := ofLists n m c.form
      inputRows := rows
      input_eq := hA
      witness := c
      rank_eq := rfl
      form_eq := rfl
      checked := hc
      hnf := h
      span := ?_
      basis := b
      basis_row := ?_ }
  · have hs := (Checked.span_form h).trans hspan
    change Submodule.span ℤ (Set.range (matrixEquiv (matrixOfLists n m c.form)).row) = _ at hs
    rw [matrixEquiv_matrixOfLists] at hs
    exact hs
  · intro i
    change ((Checked.basis h).map (LinearEquiv.ofEq _ _ hspan) i : Fin m → ℤ) = _
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Checked.basis_row]
    change (matrixEquiv (matrixOfLists n m c.form)).row _ = _
    rw [matrixEquiv_matrixOfLists]
    rfl

@[simp] theorem hermite_of_checkList_rank {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.HermiteWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) :
    (hermite_of_checkList A rows c hA hc).rank = c.rank := rfl

@[simp] theorem hermite_of_checkList_form {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.HermiteWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) :
    (hermite_of_checkList A rows c hA hc).form = ofLists n m c.form := rfl

end HexHermiteMathlib
