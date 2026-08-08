/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Lattice.ProjectedRows

public section
set_option backward.proofsInPublic true

/-!
Projection of short vectors onto the local-factor coordinates.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

/-!
# True-factor cut-projection producer

The following argument relates the BHKS prefix survivor-span lemma
(`mem_prefixSubmodule_of_normSq_le`) to `CutProjectionHypotheses` *without*
passing through `CutRetention`.  A true factor's CLD vector is a genuine short
lattice vector; the survivor-span lemma places it in the integer span of the
retained prefix rows, and projecting that span to the first `factorCount`
coordinates lands in `projectedRowSpanInt`, exactly where the executable cut
stores the projected rows.
-/

/-- Projection onto the first `r` coordinates as a `ℤ`-linear map. -/
@[expose]
def projFirst (r n : Nat) : (Fin (r + n) → ℤ) →ₗ[ℤ] (Fin r → ℤ) where
  toFun w := fun i => w (Fin.castAdd n i)
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp

@[simp, grind =] theorem projFirst_apply (r n : Nat) (w : Fin (r + n) → ℤ) (i : Fin r) :
    projFirst r n w i = w (Fin.castAdd n i) := rfl

/-- The squared Euclidean norm is the explicit sum of squared coordinates. -/
private theorem normSq_eq_sum {n : Nat} (v : Vector Int n) :
    Vector.normSq v = ∑ i : Fin n, v[i] ^ 2 := by
  unfold Vector.normSq Vector.dotProduct
  rw [finRange_foldl_add_eq_sum (g := fun i => v[i] * v[i])]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- An array `getD` at an in-bounds index is the indexed element. -/
private theorem array_getD_of_lt {α : Type*} (a : Array α) (k : Nat)
    (hk : k < a.size) (d : α) :
    a.getD k d = a[k]'hk := by
  simp [Array.getD, hk]

/-- `init`'s elements persist through the conditional-push fold. -/
private theorem mem_foldl_push_if_of_mem_init {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) (x : β) :
    ∀ (l : List α) (init : Array β), x ∈ init →
      x ∈ l.foldl (fun acc i => if p i then acc.push (g i) else acc) init := by
  intro l
  induction l with
  | nil => intro init hx; simpa using hx
  | cons a as ih =>
      intro init hx
      simp only [List.foldl_cons]
      by_cases hp : p a
      · rw [if_pos hp]; exact ih _ (Array.mem_push.mpr (Or.inl hx))
      · rw [if_neg hp]; exact ih _ hx

/-- A passing element `g i₀` of the conditional-push fold appears in the result. -/
private theorem mem_foldl_push_if {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) (i₀ : α) (hp₀ : p i₀) :
    ∀ (l : List α) (init : Array β), i₀ ∈ l →
      g i₀ ∈ l.foldl (fun acc i => if p i then acc.push (g i) else acc) init := by
  intro l
  induction l with
  | nil => intro init h; exact absurd h List.not_mem_nil
  | cons a as ih =>
      intro init h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | hmem
      · rw [if_pos hp₀]
        exact mem_foldl_push_if_of_mem_init p g (g i₀) as _
          (Array.mem_push.mpr (Or.inr rfl))
      · by_cases hp : p a
        · rw [if_pos hp]; exact ih _ hmem
        · rw [if_neg hp]; exact ih _ hmem

/-- Every element produced by a conditional-push fold either came from the
initial accumulator or is the image of a passing source element. -/
private theorem mem_foldl_push_if_imp {α β : Type*}
    (p : α → Prop) [DecidablePred p] (g : α → β) :
    ∀ (l : List α) (init : Array β) (x : β),
      x ∈ l.foldl (fun acc i => if p i then acc.push (g i) else acc) init →
        x ∈ init ∨ ∃ i ∈ l, p i ∧ g i = x := by
  intro l
  induction l with
  | nil =>
      intro init x hx
      exact Or.inl hx
  | cons a as ih =>
      intro init x hx
      simp only [List.foldl_cons] at hx
      rcases ih _ x hx with hxinit | ⟨i, hi, hpi, hix⟩
      · by_cases hpa : p a
        · rw [if_pos hpa] at hxinit
          rcases Array.mem_push.mp hxinit with hxold | hax
          · exact Or.inl hxold
          · exact Or.inr ⟨a, by simp, hpa, hax.symm⟩
        · rw [if_neg hpa] at hxinit
          exact Or.inl hxinit
      · exact Or.inr ⟨i, List.mem_cons_of_mem a hi, hpi, hix⟩

/-- The projected-indicator array reads off the first-`r`-block coordinate. -/
private theorem bhksProjectIndicator_getD {r n : Nat}
    (v : Vector Int (r + n)) (j : Fin r) :
    (Hex.bhksProjectIndicator r n v).getD j.val 0 = v[Fin.castAdd n j] := by
  have hsize : (Hex.bhksProjectIndicator r n v).size = r := by
    simp [Hex.bhksProjectIndicator]
  have hjlt : j.val < (Hex.bhksProjectIndicator r n v).size := by
    rw [hsize]; exact j.isLt
  have hjrn : j.val < r + n := Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right r n)
  rw [array_getD_of_lt _ _ hjlt]
  simp only [Hex.bhksProjectIndicator, List.getElem_toArray, List.getElem_map,
    List.getElem_range, dif_pos hjrn]
  rfl

/-- A retained prefix row, projected to its first block, is a generator of the
executable projected integer row span. -/
theorem projFirst_vectorEquiv_row_mem
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (i : Fin (L.factorCount + L.coeffWidth))
    (hi : i.val <
        Hex.bhksCutPrefixCount L (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix) :
    projFirst L.factorCount L.coeffWidth
        (HexMatrixMathlib.vectorEquiv
          (Hex.Matrix.row (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix i))
      ∈ projectedRowSpanInt (Hex.bhksProjectedRows L hrows) := by
  set reduced := (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix with hred
  set P := Hex.bhksProjectedRows L hrows with hP
  set el := Hex.bhksProjectIndicator L.factorCount L.coeffWidth (Hex.Matrix.row reduced i)
    with hel
  have hmemArr : el ∈ P.projectedRows := by
    show el ∈ Hex.bhksCutProjectReducedRows L reduced
    exact mem_foldl_push_if (fun k => k.val < Hex.bhksCutPrefixCount L reduced)
      (fun k => Hex.bhksProjectIndicator L.factorCount L.coeffWidth
        (Hex.Matrix.row reduced k)) i hi (List.finRange _) #[] (List.mem_finRange i)
  obtain ⟨k, hk, hkeq⟩ := Array.mem_iff_getElem.mp hmemArr
  have heq : projFirst L.factorCount L.coeffWidth
      (HexMatrixMathlib.vectorEquiv (Hex.Matrix.row reduced i))
        = Matrix.row (projectedRowsIntMatrix P) ⟨k, hk⟩ := by
    funext j
    rw [projFirst_apply, HexMatrixMathlib.vectorEquiv_apply, Hex.Matrix.getElem_row]
    simp only [Matrix.row, projectedRowsIntMatrix]
    rw [array_getD_of_lt _ _ hk, hkeq, hel, bhksProjectIndicator_getD,
      Hex.Matrix.getElem_row]
  rw [heq]
  exact projectedRow_mem_projectedRowSpanInt P ⟨k, hk⟩

/-- Every executable projected row comes from a retained row of the traced
LLL-reduced basis, and is exactly that row's first-coordinate block. -/
theorem projectedRow_exists_retainedSource
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (i : Fin (Hex.bhksProjectedRows L hrows).projectedRows.size) :
    ∃ j : Fin (L.factorCount + L.coeffWidth),
      j.val <
        Hex.bhksCutPrefixCount L (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix ∧
      ∀ k : Fin L.factorCount,
        ((Hex.bhksProjectedRows L hrows).projectedRows.getD i.val #[]).getD k.val 0 =
          ((Hex.bhksProjectedRowsTrace L hrows).reducedMatrix.row j)[
            Fin.castAdd L.coeffWidth k] := by
  set reduced := (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix with hred
  have hmem :
      (Hex.bhksProjectedRows L hrows).projectedRows[i] ∈
        Hex.bhksCutProjectReducedRows L reduced := by
    have hi : (Hex.bhksProjectedRows L hrows).projectedRows[i] ∈
        (Hex.bhksProjectedRows L hrows).projectedRows := Array.getElem_mem ..
    simpa [reduced, Hex.bhksProjectedRows, Hex.bhksProjectedRowsTrace,
      Hex.lllNative.shortVectors, Hex.bhksRowsArrayToMatrix_toArray] using hi
  have hsource := mem_foldl_push_if_imp
    (fun j : Fin (L.factorCount + L.coeffWidth) =>
      j.val < Hex.bhksCutPrefixCount L reduced)
    (fun j => Hex.bhksProjectIndicator L.factorCount L.coeffWidth
      (Hex.Matrix.row reduced j))
    (List.finRange _) #[]
    (Hex.bhksProjectedRows L hrows).projectedRows[i] hmem
  rcases hsource with hempty | ⟨j, _hjmem, hjcut, hjeq⟩
  · simp at hempty
  · refine ⟨j, by simpa [reduced] using hjcut, ?_⟩
    intro k
    have hrow :
        (Hex.bhksProjectedRows L hrows).projectedRows.getD i.val #[] =
          Hex.bhksProjectIndicator L.factorCount L.coeffWidth
            (Hex.Matrix.row reduced j) := by
      rw [array_getD_of_lt _ _ i.isLt]
      exact hjeq.symm
    rw [hrow, bhksProjectIndicator_getD,
      Hex.Matrix.getElem_row]

/-- Projecting a vector of the retained prefix submodule to its first block lands
in the executable projected integer row span. -/
theorem projFirst_mem_projectedRowSpanInt_of_mem_prefixSubmodule
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (w : Fin (L.factorCount + L.coeffWidth) → ℤ)
    (hw : w ∈ HexLLLMathlib.prefixSubmodule
        (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix
        (Hex.bhksCutPrefixCount L (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix)) :
    projFirst L.factorCount L.coeffWidth w ∈
      projectedRowSpanInt (Hex.bhksProjectedRows L hrows) := by
  unfold HexLLLMathlib.prefixSubmodule at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact projFirst_vectorEquiv_row_mem L hrows i.1 i.2
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/--
Build `CutProjectionHypotheses` from any per-support short vector in the BHKS
row lattice.

The vector may include nonzero diagonal-period row coefficients.  The prefix
survivor-span lemma only needs lattice membership plus the tight cut-radius
bound, and the final projection only needs the first block to be the support
indicator.
-/
theorem cutProjectionHypotheses_of_shortVectors
    (L : Hex.BhksLatticeBasis) (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (hbasis : L.basis.independent)
    (trueSupports : Set (Set (Fin (Hex.bhksProjectedRows L hrows).factorCount)))
    (data : ∀ S : trueSupports, SupportShortVectorData L S.1) :
    CutProjectionHypotheses (Hex.bhksProjectedRows L hrows) trueSupports where
  indicator_mem_projected S := by
    set v := (data S).vector with hv
    have hind : (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix.independent := by
      rw [Hex.bhksProjectedRowsTrace_reducedMatrix_eq]
      exact Hex.lllNative_independent L.basis (3 / 4) Hex.lll_delta_lower
        Hex.lll_delta_upper hrows hbasis
    have hmemRed :
        Hex.Matrix.memLattice (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix v :=
      (traceReducedMatrix_memLattice_iff L hrows v).mpr (by
        simpa [hv] using (data S).memLattice)
    have hnorm :
        4 * ((Vector.normSq v : Int) : ℚ) ≤ (Hex.bhksCutRadiusSq4 L : ℚ) := by
      have ht := (data S).four_mul_sq_norm_le
      rw [← hv] at ht
      have hsum :
          (∑ i : Fin (L.factorCount + L.coeffWidth), (((v[i] : Int) : ℝ) ^ 2))
            = ((Vector.normSq v : Int) : ℝ) := by
        rw [normSq_eq_sum]; push_cast; ring
      rw [hsum] at ht
      have hZ : 4 * (Vector.normSq v : Int) ≤ (Hex.bhksCutRadiusSq4 L : Int) := by
        have hr : ((4 * Vector.normSq v : Int) : ℝ)
            ≤ ((Hex.bhksCutRadiusSq4 L : Int) : ℝ) := by push_cast at ht ⊢; linarith
        exact_mod_cast hr
      exact_mod_cast hZ
    have hpref := mem_prefixSubmodule_of_normSq_le L
      (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix hind v hmemRed hnorm
    have hmem := projFirst_mem_projectedRowSpanInt_of_mem_prefixSubmodule L hrows
      (HexMatrixMathlib.vectorEquiv v) hpref
    have hproj : projFirst L.factorCount L.coeffWidth (HexMatrixMathlib.vectorEquiv v)
        = indicatorVector S.1 := by
      funext i
      rw [projFirst_apply, HexMatrixMathlib.vectorEquiv_apply]
      exact (data S).project_eq i
    rwa [hproj] at hmem

/--
**True-factor cut-projection producer.**

Build `CutProjectionHypotheses` for a family of true-factor supports directly
from their CLD-vector certificates (`TrueFactorCLDVectorData`), their tight
norm bounds (`TrueFactorCLDTightNormBound`), and independence of the BHKS basis.
Each true support's indicator vector is the first block of a genuine short
lattice vector, which the prefix survivor-span lemma places in the retained
prefix span; projecting to the first `factorCount` coordinates lands the
indicator in `projectedRowSpanInt`.  This method does **not** pass through
`CutRetention`.
-/

theorem projectedRow_mem_projectedRowSpaceRat
    (L : Hex.BhksProjectedRows) (i : Fin L.projectedRows.size) :
    Matrix.row (projectedRowsRatMatrix L) i ∈ projectedRowSpaceRat L := by
  exact Submodule.subset_span ⟨i, rfl⟩

/-- `intVectorToRat` of the zero vector is the zero rational vector. -/
@[simp, grind =] theorem intVectorToRat_zero {r : Nat} :
    intVectorToRat (0 : Fin r → ℤ) = 0 := by
  funext i
  simp [intVectorToRat]

/-- `intVectorToRat` commutes with pointwise addition. -/
@[simp, grind =] theorem intVectorToRat_add {r : Nat} (u v : Fin r → ℤ) :
    intVectorToRat (u + v) = intVectorToRat u + intVectorToRat v := by
  funext i
  simp [intVectorToRat, Pi.add_apply]

/-- `intVectorToRat` of an integer-scalar multiple is the rational-cast scalar
times the rational vector. -/
@[simp, grind =] theorem intVectorToRat_intSmul {r : Nat} (n : ℤ) (v : Fin r → ℤ) :
    intVectorToRat (n • v) = (n : ℚ) • intVectorToRat v := by
  funext i
  simp only [intVectorToRat, Pi.smul_apply, smul_eq_mul, Int.cast_mul]

/-- Membership in the integer span carries over to membership of the
rational-cast vector in the rational span of the rational-cast generators. -/
theorem intVectorToRat_mem_span_rat_of_mem_span_int
    {r : Nat} {S : Set (Fin r → ℤ)} {v : Fin r → ℤ}
    (hv : v ∈ Submodule.span ℤ S) :
    intVectorToRat v ∈ Submodule.span ℚ (intVectorToRat '' S) := by
  induction hv using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
  | zero =>
      rw [intVectorToRat_zero]
      exact Submodule.zero_mem _
  | add u w _ _ hu hw =>
      rw [intVectorToRat_add]
      exact Submodule.add_mem _ hu hw
  | smul n w _ hw =>
      rw [intVectorToRat_intSmul]
      exact Submodule.smul_mem _ _ hw

/-- The rational projected row is the pointwise rational cast of the integer
projected row.  Both `projectedRowsRatMatrix` and `projectedRowsIntMatrix` read
the same underlying `L.projectedRows` array; the only difference is the
codomain. -/
theorem row_projectedRowsRatMatrix_eq_intVectorToRat
    (L : Hex.BhksProjectedRows) (i : Fin L.projectedRows.size) :
    Matrix.row (projectedRowsRatMatrix L) i =
      intVectorToRat (Matrix.row (projectedRowsIntMatrix L) i) := by
  funext j
  simp [Matrix.row, projectedRowsRatMatrix, projectedRowsIntMatrix,
    intVectorToRat]

/-- The range of the rational projected rows is the image of the range of the
integer projected rows under `intVectorToRat`. -/
theorem range_row_projectedRowsRatMatrix_eq_image
    (L : Hex.BhksProjectedRows) :
    (Set.range fun i : Fin L.projectedRows.size =>
        Matrix.row (projectedRowsRatMatrix L) i) =
      intVectorToRat ''
        (Set.range fun i : Fin L.projectedRows.size =>
          Matrix.row (projectedRowsIntMatrix L) i) := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Matrix.row (projectedRowsIntMatrix L) i, ⟨i, rfl⟩,
      (row_projectedRowsRatMatrix_eq_intVectorToRat L i).symm⟩
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (row_projectedRowsRatMatrix_eq_intVectorToRat L i)⟩
end BHKS

end

end HexBerlekampZassenhausMathlib
