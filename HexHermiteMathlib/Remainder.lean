/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexHermiteMathlib.Certificate

public section

/-! Soundness of structural list remainder checks for integer row lattices. -/

namespace HexHermiteMathlib

open HexMatrixMathlib Hex.Matrix.Lists

private theorem get_ofFn {α : Type*} {k : Nat} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = _
  rw [Vector.getElem_ofFn]

theorem residual_zero_iff (m : Nat) (r : Hex.Matrix.HermiteRemainder) :
    r.isZero m = true ↔ vecOfList m r.residual = 0 := by
  simp only [Hex.Matrix.HermiteRemainder.isZero, all_iff, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    rw [vecOfList_apply, ← entry_eq_getD]
    exact h i i.isLt
  · intro h i hi
    have hh := congrFun h ⟨i, hi⟩
    simpa only [vecOfList_apply, ← entry_eq_getD, Pi.zero_apply] using hh

/-- The checked identity separates a known lattice combination from a residual. -/
theorem remainder_identity {n m : Nat} (rows : List (List Int))
    (c : Hex.Matrix.HermiteWitness) (hc : Hex.Matrix.checkHermiteList n m rows c = true)
    (v : List Int) (r : Hex.Matrix.HermiteRemainder) (hr : Hex.Matrix.checkRemainder m v c r = true) :
    vecOfList m v =
      (∑ i : Fin c.rank, vecOfList c.rank r.coeffs i • Checked.rows (hermite_of_check rows c hc) i) +
        vecOfList m r.residual := by
  simp only [Hex.Matrix.checkRemainder, Bool.and_eq_true, Nat.beq_eq, and_assoc] at hr
  obtain ⟨_, hq, _, he, _⟩ := hr
  let h := hermite_of_check rows c hc
  have hrow (i : Fin c.rank) (j : Fin m) :
      Checked.rows h i j = (c.form.getD i []).getD j 0 := by
    change (matrixEquiv (matrixOfLists n m c.form)) (h.toIsEchelonForm.pivotRow i) j = _
    rw [matrixEquiv_matrixOfLists, ofLists_apply]
    rfl
  have htake (i : Fin c.rank) :
      (c.form.take c.rank).getD i [] = c.form.getD i [] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt]
  funext j
  have hx := of_decide_eq_true ((all_iff _ _).mp he j j.isLt)
  simp only [entry_eq_getD] at hx
  change v.getD j 0 = dot r.coeffs (column j (c.form.take c.rank)) + r.residual.getD j 0 at hx
  change vecOfList m v j =
    ((∑ i : Fin c.rank, vecOfList c.rank r.coeffs i • Checked.rows h i) + vecOfList m r.residual) j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecOfList_apply, hrow]
  rw [hx]
  congr 1
  have hd := dot_eq_sum r.coeffs (column j (c.form.take c.rank))
  rw [hq] at hd
  rw [hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [ListProducts.column_getD, htake]

/-- A checked reduced remainder vanishes exactly on members of the input lattice. -/
theorem mem_iff_remainder {n m : Nat} (rows : List (List Int))
    (c : Hex.Matrix.HermiteWitness) (hc : Hex.Matrix.checkHermiteList n m rows c = true)
    (v : List Int) (r : Hex.Matrix.HermiteRemainder) (hr : Hex.Matrix.checkRemainder m v c r = true) :
    vecOfList m v ∈ Submodule.span ℤ (Set.range (ofLists n m rows).row) ↔
      vecOfList m r.residual = 0 := by
  let h := hermite_of_check rows c hc
  let L := Submodule.span ℤ (Set.range (ofLists n m rows).row)
  have hspan : Submodule.span ℤ (Set.range (Checked.rows h)) = L := by
    have hs := Checked.span_rows h
    rw [matrixEquiv_matrixOfLists] at hs
    exact hs
  have hsum : (∑ i : Fin c.rank, vecOfList c.rank r.coeffs i • Checked.rows h i) ∈ L := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hmem : vecOfList m v ∈ L ↔ vecOfList m r.residual ∈ L := by
    rw [remainder_identity rows c hc v r hr]
    exact L.add_mem_iff_right hsum
  rw [hmem]
  constructor
  · intro ht
    let t : Vector Int m := vectorEquiv.symm (vecOfList m r.residual)
    have he : vectorEquiv t = vecOfList m r.residual := vectorEquiv.apply_symm_apply _
    have hv : (matrixOfLists n m c.form).memLattice t := by
      apply (HexHermiteMathlib.mem_span_iff _ t).mp
      rw [he, Checked.span_form h, matrixEquiv_matrixOfLists]
      exact ht
    have hs := hr
    simp only [Hex.Matrix.checkRemainder, Bool.and_eq_true, and_assoc] at hs
    have hb := (all_iff _ _).mp hs.2.2.2.2
    have htget (j : Fin m) : t[j] = entry 0 r.residual j := by
      change (Vector.ofFn (vecOfList m r.residual))[j.val] = _
      rw [Vector.getElem_ofFn, vecOfList_apply, entry_eq_getD]
    have hz : t = 0 := by
      apply Checked.reduced_zero h t hv
      intro i
      change 0 ≤ t[(decodeWitness n m c (check_form rows c hc)).pivotCols.get i] ∧
        t[(decodeWitness n m c (check_form rows c hc)).pivotCols.get i] <
          (matrixOfLists n m c.form)[h.toIsEchelonForm.pivotRow i][(decodeWitness n m c (check_form rows c hc)).pivotCols.get i]
      simp only [htget, matrixOfLists_get]
      simp only [decodeWitness, get_ofFn, Fin.val_mk, Hex.Matrix.IsEchelonForm.pivotRow]
      simpa only [Bool.and_eq_true, decide_eq_true_eq, Fin.val_mk] using hb i.val i.isLt
    rw [← he, hz, vectorEquiv_zero]
  · intro hz
    rw [hz]
    exact Submodule.zero_mem _

theorem mem_iff_checkList {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (rows : List (List Int)) (c : Hex.Matrix.HermiteWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) (v : Fin m → ℤ) (vs : List Int)
    (hv : v = vecOfList m vs) (r : Hex.Matrix.HermiteRemainder)
    (hr : Hex.Matrix.checkRemainder m vs c r = true) :
    v ∈ Submodule.span ℤ (Set.range A) ↔ r.isZero m = true := by
  subst A v
  exact (mem_iff_remainder rows c hc vs r hr).trans (residual_zero_iff m r).symm

theorem mem_of_checkList {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (rows : List (List Int)) (c : Hex.Matrix.HermiteWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) (v : Fin m → ℤ) (vs : List Int)
    (hv : v = vecOfList m vs) (r : Hex.Matrix.HermiteRemainder)
    (hr : Hex.Matrix.checkRemainder m vs c r = true) (hz : r.isZero m = true) :
    v ∈ Submodule.span ℤ (Set.range A) :=
  (mem_iff_checkList A rows c hA hc v vs hv r hr).mpr hz

theorem not_mem_of_checkList {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ)
    (rows : List (List Int)) (c : Hex.Matrix.HermiteWitness) (hA : A = ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) (v : Fin m → ℤ) (vs : List Int)
    (hv : v = vecOfList m vs) (r : Hex.Matrix.HermiteRemainder)
    (hr : Hex.Matrix.checkRemainder m vs c r = true) (hz : r.isZero m = false) :
    v ∉ Submodule.span ℤ (Set.range A) := by
  intro hm
  have hh := (mem_iff_checkList A rows c hA hc v vs hv r hr).mp hm
  rw [hz] at hh
  contradiction

end HexHermiteMathlib
