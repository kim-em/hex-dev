/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant.Adjugate
public import HexRowReduce.RowEchelon.Contracts

public section

/-! Contracts and the executable shape checker for row Hermite normal form. -/

namespace Hex.Matrix

/-- Hermite normal-form conditions on top of integer row-echelon form. -/
structure IsHNF {n m : Nat} (M : Matrix Int n m)
    (D : RowEchelonData Int n m) : Prop extends IsEchelonForm M D where
  pivot_leading : ∀ (i : Fin D.rank) (j : Fin m),
    j < D.pivotCols.get i → D.echelon[i][j] = 0
  pivot_pos : ∀ (i : Fin D.rank), 0 < D.echelon[i][D.pivotCols.get i]
  above_nonneg : ∀ (i : Fin D.rank) (k : Fin n), k.val < i.val →
    0 ≤ D.echelon[k][D.pivotCols.get i]
  above_lt : ∀ (i : Fin D.rank) (k : Fin n), k.val < i.val →
    D.echelon[k][D.pivotCols.get i] < D.echelon[i][D.pivotCols.get i]

/-- Entry-level HNF clauses, independent of any transform matrix. Row indices
matching pivot indices are quantified explicitly so the predicate remains
well-typed even before its `r ≤ n` clause is used. -/
@[expose]
def HNFForm (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r) : Prop :=
  r ≤ n ∧
  r ≤ m ∧
  (∀ i j : Fin r, i < j → piv.get i < piv.get j) ∧
  (∀ (i : Fin r) (row : Fin n), row.val = i.val →
    ∀ j : Fin m, j < piv.get i → (H.getRow row).get j = 0) ∧
  (∀ (i : Fin r) (row : Fin n), row.val = i.val →
    0 < (H.getRow row).get (piv.get i)) ∧
  (∀ (i : Fin r) (row : Fin n), i.val < row.val →
    (H.getRow row).get (piv.get i) = 0) ∧
  (∀ row : Fin n, r ≤ row.val → H.getRow row = 0) ∧
  (∀ (i : Fin r) (row : Fin n), row.val < i.val →
    0 ≤ (H.getRow row).get (piv.get i)) ∧
  (∀ (i : Fin r) (row : Fin n), row.val < i.val →
    ∀ pivotRow : Fin n, pivotRow.val = i.val →
      (H.getRow row).get (piv.get i) < (H.getRow pivotRow).get (piv.get i))

instance (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r) :
    Decidable (HNFForm H r piv) := by
  unfold HNFForm
  infer_instance

private def HNFFormChecked (H : Matrix Int n m) (r : Nat)
    (piv : Vector (Fin m) r) (hrn : r ≤ n) : Prop :=
  r ≤ m ∧
  (∀ i j : Fin r, i < j → piv.get i < piv.get j) ∧
  (∀ (i : Fin r) (j : Fin m), j < piv.get i →
    (H.getRow (Fin.castLE hrn i)).get j = 0) ∧
  (∀ i : Fin r, 0 < (H.getRow (Fin.castLE hrn i)).get (piv.get i)) ∧
  (∀ (i : Fin r) (row : Fin n), i.val < row.val →
    (H.getRow row).get (piv.get i) = 0) ∧
  (∀ row : Fin n, r ≤ row.val → H.getRow row = 0) ∧
  (∀ (i : Fin r) (row : Fin n), row.val < i.val →
    0 ≤ (H.getRow row).get (piv.get i)) ∧
  (∀ (i : Fin r) (row : Fin n), row.val < i.val →
    (H.getRow row).get (piv.get i) <
      (H.getRow (Fin.castLE hrn i)).get (piv.get i))

private instance (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r)
    (hrn : r ≤ n) : Decidable (HNFFormChecked H r piv hrn) := by
  unfold HNFFormChecked
  infer_instance

private theorem hnfFormChecked_iff (H : Matrix Int n m) (r : Nat)
    (piv : Vector (Fin m) r) (hrn : r ≤ n) :
    HNFFormChecked H r piv hrn ↔ HNFForm H r piv := by
  unfold HNFFormChecked HNFForm
  constructor
  · rintro ⟨hrm, sorted, leading, positive, below, zero, above, reduced⟩
    refine ⟨hrn, hrm, sorted, ?_, ?_, below, zero, above, ?_⟩
    · intro i row hrow j hj
      have : row = Fin.castLE hrn i := by
        apply Fin.ext
        exact hrow
      subst row
      exact leading i j hj
    · intro i row hrow
      have : row = Fin.castLE hrn i := by
        apply Fin.ext
        exact hrow
      subst row
      exact positive i
    · intro i row hrow pivotRow hpivot
      have : pivotRow = Fin.castLE hrn i := by
        apply Fin.ext
        exact hpivot
      subst pivotRow
      exact reduced i row hrow
  · rintro ⟨_, hrm, sorted, leading, positive, below, zero, above, reduced⟩
    refine ⟨hrm, sorted, ?_, ?_, below, zero, above, ?_⟩
    · intro i j hj
      exact leading i (Fin.castLE hrn i) rfl j hj
    · intro i
      exact positive i (Fin.castLE hrn i) rfl
    · intro i row hrow
      exact reduced i row hrow (Fin.castLE hrn i) rfl

/-- Decide all row-HNF shape clauses directly from the entries. -/
@[expose]
def isHNFForm (H : Matrix Int n m) (r : Nat) (piv : Vector (Fin m) r) : Bool :=
  if hrn : r ≤ n then
    decide (
      r ≤ m ∧
      (∀ i j : Fin r, i < j → piv.get i < piv.get j) ∧
      (∀ (i : Fin r) (j : Fin m), j < piv.get i →
        (H.getRow (Fin.castLE hrn i)).get j = 0) ∧
      (∀ i : Fin r, 0 < (H.getRow (Fin.castLE hrn i)).get (piv.get i)) ∧
      (∀ (i : Fin r) (row : Fin n), i.val < row.val →
        (H.getRow row).get (piv.get i) = 0) ∧
      (∀ row : Fin n, r ≤ row.val → H.getRow row = 0) ∧
      (∀ (i : Fin r) (row : Fin n), row.val < i.val →
        0 ≤ (H.getRow row).get (piv.get i)) ∧
      (∀ (i : Fin r) (row : Fin n), row.val < i.val →
        (H.getRow row).get (piv.get i) <
          (H.getRow (Fin.castLE hrn i)).get (piv.get i)))
  else false

@[simp] theorem isHNFForm_iff (H : Matrix Int n m) (r : Nat)
    (piv : Vector (Fin m) r) :
    isHNFForm H r piv = true ↔ HNFForm H r piv := by
  unfold isHNFForm
  split
  next hrn =>
    change decide (HNFFormChecked H r piv hrn) = true ↔ HNFForm H r piv
    simpa only [decide_eq_true_eq] using hnfFormChecked_iff H r piv hrn
  next hrn =>
    simp only [Bool.false_eq_true, false_iff]
    unfold HNFForm
    omega

private theorem int_factor_one {x y : Int} (h : x * y = 1) :
    x = 1 ∨ x = -1 := by
  have hx_dvd : x ∣ (1 : Int) := ⟨y, h.symm⟩
  have hxnat_dvd : x.natAbs ∣ (1 : Nat) := by
    have hdvd := Int.natAbs_dvd_natAbs.mpr hx_dvd
    simpa using hdvd
  have hxnat_le : x.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hxnat_dvd
  have hx_ne : x ≠ 0 := by
    intro hzero
    rw [hzero, Int.zero_mul] at h
    omega
  have hxnat_pos : 1 ≤ x.natAbs := by
    rcases Nat.eq_zero_or_pos x.natAbs with hzero | hpos
    · exact absurd (Int.natAbs_eq_zero.mp hzero) hx_ne
    · exact hpos
  have hxnat_eq : x.natAbs = 1 := by omega
  rcases Int.natAbs_eq x with heq | heq
  · left
    rw [heq, hxnat_eq]
    rfl
  · right
    rw [heq, hxnat_eq]
    rfl

/-- The transform carried by valid HNF data is unimodular over `Int`. -/
theorem IsHNF.det_transform {M : Matrix Int n m} {D : RowEchelonData Int n m}
    (h : IsHNF M D) :
    det D.transform = 1 ∨ det D.transform = -1 := by
  rcases h.toIsEchelonForm.transform_right_inv with ⟨W, hW⟩
  apply int_factor_one
  rw [← det_mul, hW, det_identity]

end Hex.Matrix
