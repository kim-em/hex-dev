/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhausMathlib.Lattice
import HexBerlekampZassenhausMathlib.SignatureClasses

/-!
Executable class-count semantics for the BHKS equivalence-class indicators
(#8519).

Resurrected from the pre-#8411 `Recovery.lean` (6bf20977^), forward-count
cluster only: the executable `bhksEquivalenceClassIndicators` array has size
equal to the RREF signature partition (`bhksEquivalenceClassIndicators_size_eq`),
and — given the cut inclusion `W ⊆ L'` (`CutProjectionHypotheses`) — at least
one class per true-support-equivalence class
(`supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size`).
No reverse `L' = W` separation is consumed.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

/-- The least column `≤ j` sharing column `j`'s signature: the canonical
signature representative of `j`.  It is always `≤ j`, so it stays in range. -/
private def sigRep (sig : Nat → Array Rat) (j : Nat) : Nat :=
  Nat.find (p := fun k => k ≤ j ∧ sig k = sig j) ⟨j, le_refl j, rfl⟩

private theorem sigRep_le (sig : Nat → Array Rat) (j : Nat) : sigRep sig j ≤ j :=
  (Nat.find_spec (p := fun k => k ≤ j ∧ sig k = sig j) ⟨j, le_refl j, rfl⟩).1

private theorem sigRep_sig (sig : Nat → Array Rat) (j : Nat) :
    sig (sigRep sig j) = sig j :=
  (Nat.find_spec (p := fun k => k ≤ j ∧ sig k = sig j) ⟨j, le_refl j, rfl⟩).2

private theorem sigRep_min (sig : Nat → Array Rat) {j k : Nat}
    (hk : k < sigRep sig j) : ¬ (k ≤ j ∧ sig k = sig j) :=
  Nat.find_min (p := fun k => k ≤ j ∧ sig k = sig j) ⟨j, le_refl j, rfl⟩ hk

/-- Forward refinement of the support partition by the signature partition.

If equal column signatures force support-equivalence — the *forward* direction,
available from the inclusion `W ⊆ L'` alone (no reverse `L' = W` separation) —
then every signature class is contained in one support-equivalence class, so the
signature partition refines the support partition and therefore has at least as
many classes.  The map sending each support representative `q` to its signature
representative `sigRep sig q` is the witnessing injection. -/
theorem supportPartitionByMinColumn_length_le_partitionByMinColumn_length
    {r : Nat} (trueSupports : Set (Set (Fin r))) (sig : Nat → Array Rat)
    (hrefine :
      ∀ j k, (hj : j < r) → (hk : k < r) →
        sig j = sig k → supportEquivalent trueSupports ⟨j, hj⟩ ⟨k, hk⟩) :
    (supportPartitionByMinColumn trueSupports).length ≤
      (partitionByMinColumn r sig).length := by
  classical
  rw [supportPartitionByMinColumn, partitionByMinColumn, List.length_map,
    List.length_map]
  have hnodup_supp : (supportRepresentativeColumns trueSupports).Nodup := by
    unfold supportRepresentativeColumns
    exact (List.nodup_range).filter _
  have hnodup_sig : (representativeColumns r sig).Nodup := by
    unfold representativeColumns
    exact (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnodup_supp,
    ← List.toFinset_card_of_nodup hnodup_sig]
  refine Finset.card_le_card_of_injOn (sigRep sig) ?_ ?_
  · -- `sigRep sig q` is a signature representative for each support rep `q`.
    intro q hq
    simp only [Finset.mem_coe, List.mem_toFinset] at hq ⊢
    have hq_lt : q < r := supportRepresentativeColumns_lt trueSupports hq
    rw [mem_representativeColumns_iff]
    refine ⟨lt_of_le_of_lt (sigRep_le sig q) hq_lt, ?_⟩
    intro k hk hsigk
    have hk_le_q : k ≤ q := le_trans (Nat.le_of_lt hk) (sigRep_le sig q)
    have hsig_q : sig k = sig q := by rw [hsigk, sigRep_sig sig q]
    exact sigRep_min sig hk ⟨hk_le_q, hsig_q⟩
  · -- `sigRep sig` is injective on support representatives.
    intro q₁ hq₁ q₂ hq₂ heq
    rw [Finset.mem_coe, List.mem_toFinset] at hq₁ hq₂
    have hq₁_lt : q₁ < r := supportRepresentativeColumns_lt trueSupports hq₁
    have hq₂_lt : q₂ < r := supportRepresentativeColumns_lt trueSupports hq₂
    have hsig_eq : sig q₁ = sig q₂ := by
      rw [← sigRep_sig sig q₁, ← sigRep_sig sig q₂, heq]
    have hsupp : supportEquivalent trueSupports ⟨q₁, hq₁_lt⟩ ⟨q₂, hq₂_lt⟩ :=
      hrefine q₁ q₂ hq₁_lt hq₂_lt hsig_eq
    rcases lt_trichotomy q₁ q₂ with hlt | heq' | hgt
    · exact absurd
        ((supportEquivalentAt_iff trueSupports hq₁_lt hq₂_lt).mpr hsupp)
        (supportRepresentativeColumns_min trueSupports hq₂ q₁ hlt)
    · exact heq'
    · refine absurd
        ((supportEquivalentAt_iff trueSupports hq₂_lt hq₁_lt).mpr ?_)
        (supportRepresentativeColumns_min trueSupports hq₁ q₂ hgt)
      intro S hS
      exact (hsupp S hS).symm

/-- The RREF column signature expression used by
`Hex.bhksEquivalenceClassIndicators`, exposed as a proof-facing definition. -/
def projectedRowsRrefColumnSignature (L : Hex.BhksProjectedRows) (j : Nat) :
    Array Rat :=
  let n := L.projectedRows.size
  let r := L.factorCount
  let M : Hex.Matrix Rat n r := Hex.bhksProjectedRowsAsRatMatrix L.projectedRows n r
  let D := Hex.Matrix.rowReduce M
  let echelonRows : Array (Array Rat) := D.echelon.rows.toArray.map (·.toArray)
  echelonRows.map (·.getD j 0)

theorem matrixEquiv_bhksProjectedRowsAsRatMatrix
    (L : Hex.BhksProjectedRows) :
    HexMatrixMathlib.matrixEquiv
        (Hex.bhksProjectedRowsAsRatMatrix
          L.projectedRows L.projectedRows.size L.factorCount) =
      projectedRowsRatMatrix L := by
  funext i j
  simp [HexMatrixMathlib.matrixEquiv_apply, Hex.bhksProjectedRowsAsRatMatrix,
    projectedRowsRatMatrix, Hex.Matrix.ofFn]

private theorem projectedRowsRrefColumnSignature_eq_iff_forall_echelon
    (L : Hex.BhksProjectedRows) {j k : Nat}
    (hj : j < L.factorCount) (hk : k < L.factorCount) :
    projectedRowsRrefColumnSignature L j = projectedRowsRrefColumnSignature L k ↔
      ∀ i : Fin L.projectedRows.size,
        (Hex.Matrix.rowReduce
          (Hex.bhksProjectedRowsAsRatMatrix
            L.projectedRows L.projectedRows.size L.factorCount)).echelon[i][
              (⟨j, hj⟩ : Fin L.factorCount)] =
        (Hex.Matrix.rowReduce
          (Hex.bhksProjectedRowsAsRatMatrix
            L.projectedRows L.projectedRows.size L.factorCount)).echelon[i][
              (⟨k, hk⟩ : Fin L.factorCount)] := by
  constructor
  · intro h i
    have hget := congrArg (fun a : Array Rat => a.getD i.val 0) h
    simpa [projectedRowsRrefColumnSignature, Array.getD, hj, hk,
      Hex.Matrix.getRow] using hget
  · intro h
    apply Array.ext
    · simp [projectedRowsRrefColumnSignature]
    · intro i hi₁ hi₂
      have hi : i < L.projectedRows.size := by
        simpa [projectedRowsRrefColumnSignature] using hi₁
      have hrow := h ⟨i, hi⟩
      simpa [projectedRowsRrefColumnSignature, Array.getD, hj, hk,
        Hex.Matrix.getRow] using hrow

theorem projectedRowsRrefColumnSignature_eq_iff_forall_mem_projectedRowSpaceRat_coord_eq
    (L : Hex.BhksProjectedRows) {j k : Nat}
    (hj : j < L.factorCount) (hk : k < L.factorCount) :
    projectedRowsRrefColumnSignature L j = projectedRowsRrefColumnSignature L k ↔
      ∀ v : Fin L.factorCount → ℚ,
        v ∈ projectedRowSpaceRat L →
          v ⟨j, hj⟩ = v ⟨k, hk⟩ := by
  rw [projectedRowsRrefColumnSignature_eq_iff_forall_echelon L hj hk]
  have hmatrix := matrixEquiv_bhksProjectedRowsAsRatMatrix L
  unfold projectedRowSpaceRat
  rw [← hmatrix]
  exact rowReduce_columnAgreement_iff_forall_mem_span_coord_eq
    (Hex.bhksProjectedRowsAsRatMatrix
      L.projectedRows L.projectedRows.size L.factorCount) ⟨j, hj⟩ ⟨k, hk⟩

/-- Forward column-signature implication from the cut inclusion `W ⊆ L'`.

This is the one-directional half of
`projectedRowsRrefColumnSignature_eq_iff_supportEquivalent_of_projectedRowSpan_eq`
that needs only the forward inclusion supplied by `CutProjectionHypotheses`
(each true-support indicator lies in `L'`), not the reverse `L' = W`
separation.  Equal RREF column signatures mean every vector of the rational row
space agrees on those two columns; since each support indicator lies in `L'`
(hence in the rational row space), the two columns lie in exactly the same true
supports. -/
theorem projectedRowsRrefColumnSignature_eq_imp_supportEquivalent_of_cut
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcut : CutProjectionHypotheses L trueSupports)
    {j k : Nat} (hj : j < L.factorCount) (hk : k < L.factorCount)
    (hsig :
      projectedRowsRrefColumnSignature L j = projectedRowsRrefColumnSignature L k) :
    supportEquivalent trueSupports ⟨j, hj⟩ ⟨k, hk⟩ := by
  have hcoord :=
    (projectedRowsRrefColumnSignature_eq_iff_forall_mem_projectedRowSpaceRat_coord_eq
      L hj hk).mp hsig
  intro S hS
  have hmem_int :
      indicatorVector (S : Set (Fin L.factorCount)) ∈ projectedRowSpanInt L :=
    hcut.indicator_mem_projected ⟨S, hS⟩
  have hmem_rat :
      intVectorToRat (indicatorVector S) ∈ projectedRowSpaceRat L := by
    have h := intVectorToRat_mem_span_rat_of_mem_span_int
      (S := Set.range fun i : Fin L.projectedRows.size =>
        Matrix.row (projectedRowsIntMatrix L) i) hmem_int
    unfold projectedRowSpaceRat
    rw [range_row_projectedRowsRatMatrix_eq_image]
    exact h
  have heq := hcoord _ hmem_rat
  by_cases hjS : (⟨j, hj⟩ : Fin L.factorCount) ∈ S
  · by_cases hkS : (⟨k, hk⟩ : Fin L.factorCount) ∈ S
    · exact iff_of_true hjS hkS
    · exfalso
      simp [intVectorToRat, indicatorVector, hjS, hkS] at heq
  · by_cases hkS : (⟨k, hk⟩ : Fin L.factorCount) ∈ S
    · exfalso
      simp [intVectorToRat, indicatorVector, hjS, hkS] at heq
    · exact iff_of_false hjS hkS

/-- The number of executable equivalence-class indicators equals the length of
the signature partition `partitionByMinColumn` over the RREF column signatures.
This is a pure restatement of the executable fold semantics, independent of any
lattice hypothesis. -/
theorem bhksEquivalenceClassIndicators_size_eq (L : Hex.BhksProjectedRows) :
    (Hex.bhksEquivalenceClassIndicators L).size =
      (partitionByMinColumn L.factorCount
        (projectedRowsRrefColumnSignature L)).length := by
  let sig := projectedRowsRrefColumnSignature L
  have hfold :
      ((List.range L.factorCount).foldl
        (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) []).map Prod.snd =
        partitionByMinColumn L.factorCount sig :=
    bhksInsertSignatureClass_fold_eq_partitionByMinColumn L.factorCount sig
  unfold Hex.bhksEquivalenceClassIndicators
  change
    (((((List.range L.factorCount).foldl
      (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) []).map Prod.snd).map
        (fun cls => classIndicatorArray L.factorCount cls)).toArray).size =
      (partitionByMinColumn L.factorCount sig).length
  rw [hfold]
  simp

/-- Forward count bound: the executable equivalence-class partition emits at
least one class per true-support-equivalence class.

This is the forward-only `count_ge` core: from the cut inclusion `W ⊆ L'`
(`CutProjectionHypotheses`, certified by the closed cut-survival argument) the
emitted partition refines the true-support partition, so the emitted class count
is at least the support-partition length.  It needs no reverse `L' = W`
separation — and hence no bad-vector resultant valuation — establishing the
lower count bound from the forward inclusion alone. -/
theorem supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcut : CutProjectionHypotheses L trueSupports) :
    (supportPartitionByMinColumn trueSupports).length ≤
      (Hex.bhksEquivalenceClassIndicators L).size := by
  rw [bhksEquivalenceClassIndicators_size_eq]
  apply supportPartitionByMinColumn_length_le_partitionByMinColumn_length
  intro j k hj hk hsig
  exact projectedRowsRrefColumnSignature_eq_imp_supportEquivalent_of_cut
    L trueSupports hcut hj hk hsig

end BHKS

end

end HexBerlekampZassenhausMathlib
