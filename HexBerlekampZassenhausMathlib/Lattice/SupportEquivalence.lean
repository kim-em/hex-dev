/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Lattice.CutProjection

public section
set_option backward.proofsInPublic true

/-!
Support equivalence and exact reduced-row-echelon-form semantics.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

/-!
# Exact RREF semantics once `L' = W`

The following lemmas turn equality of the executable projected integer lattice
with the true-support lattice into the coordinate-agreement relation consumed
by the RREF signature classifier.
-/

/-- Membership in the true-support span forces equal coordinates at columns
with the same true-support membership signature. -/
theorem coord_eq_of_mem_trueSupportSpanInt
    {r : Nat} (trueSupports : Set (Set (Fin r))) {j k : Fin r}
    (hjk : supportEquivalent trueSupports j k)
    {v : Fin r → ℤ} (hv : v ∈ trueSupportSpanInt trueSupports) :
    v j = v k := by
  unfold trueSupportSpanInt at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨S, rfl⟩
      have hmem := hjk S.1 S.2
      change indicatorVector S.1 j = indicatorVector S.1 k
      by_cases hj : j ∈ S.1
      · rw [indicatorVector_apply_mem S.1 hj,
          indicatorVector_apply_mem S.1 (hmem.mp hj)]
      · rw [indicatorVector_apply_not_mem S.1 hj,
          indicatorVector_apply_not_mem S.1 (fun hk => hj (hmem.mpr hk))]
  | zero => simp
  | add u w _ _ hu hw => simp only [Pi.add_apply, hu, hw]
  | smul n w _ hw => simp only [Pi.smul_apply, smul_eq_mul, hw]

/--
For a genuine finite partition, a vector belongs to the true-support span
whenever it is constant on every part.

Together with `coord_eq_of_mem_trueSupportSpanInt`, this characterizes `W` as
the integer vectors that are constant on each true support.
-/
theorem mem_trueSupportSpanInt_of_constant_on_partition
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin r, i ∈ S → i ∈ T → S = T)
    (hne : ∀ S ∈ trueSupports, S.Nonempty)
    (v : Fin r → ℤ)
    (hconstant :
      ∀ S ∈ trueSupports, ∀ i ∈ S, ∀ j ∈ S, v i = v j) :
    v ∈ trueSupportSpanInt trueSupports := by
  classical
  letI : Fintype trueSupports := (Set.toFinite trueSupports).fintype
  let rep : trueSupports → Fin r :=
    fun S => (hne S.1 S.2).choose
  have hrep (S : trueSupports) : rep S ∈ S.1 :=
    (hne S.1 S.2).choose_spec
  let w : Fin r → ℤ :=
    ∑ S : trueSupports, v (rep S) • indicatorVector S.1
  have hw : w ∈ trueSupportSpanInt trueSupports := by
    dsimp only [w]
    exact Submodule.sum_mem _ fun S _ =>
      Submodule.smul_mem _ _ (indicatorVector_mem_trueSupportSpanInt trueSupports S)
  have hvw : v = w := by
    funext i
    obtain ⟨T, hT, hiT⟩ := hcover i
    let T' : trueSupports := ⟨T, hT⟩
    simp only [w, Finset.sum_apply]
    rw [Finset.sum_eq_single T']
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [indicatorVector_apply_mem T hiT, mul_one]
      exact hconstant T hT i hiT (rep T') (hrep T')
    · intro S _ hST
      have hiS : i ∉ S.1 := by
        intro hiS
        have hEq : S.1 = T :=
          hdisjoint S.1 S.2 T hT i hiS hiT
        apply hST
        exact Subtype.ext hEq
      simp [Pi.smul_apply, indicatorVector_apply_not_mem S.1 hiS]
    · intro h
      exact absurd (Finset.mem_univ T') h
  rw [hvw]
  exact hw

/--
Any integer vector outside the true-support span varies on at least one part of
the genuine partition.
-/
theorem exists_ne_on_support_of_not_mem_trueSupportSpanInt
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    (hcover : ∀ i : Fin r, ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin r, i ∈ S → i ∈ T → S = T)
    (hne : ∀ S ∈ trueSupports, S.Nonempty)
    (v : Fin r → ℤ)
    (hv : v ∉ trueSupportSpanInt trueSupports) :
    ∃ S ∈ trueSupports, ∃ i ∈ S, ∃ j ∈ S, v i ≠ v j := by
  by_contra h
  push Not at h
  exact hv <|
    mem_trueSupportSpanInt_of_constant_on_partition
      trueSupports hcover hdisjoint hne v h

/--
Adjust a full BHKS lattice vector outside `W` by full true-support short
vectors.  The adjusted vector has a zero exponent at one local factor, but its
first block is nonzero on every true support.

The correction is performed on row-combination coefficients, not merely on the
projected first block, so the result remains an actual vector of the full BHKS
lattice.
-/
theorem exists_adjustedVector
    (L : Hex.BhksLatticeBasis) (hL : BhksBlockForm L)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcover : ∀ i : Fin L.factorCount, ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin L.factorCount, i ∈ S → i ∈ T → S = T)
    (hne : ∀ S ∈ trueSupports, S.Nonempty)
    (data : ∀ S : trueSupports, SupportShortVectorData L S.1)
    (V U : Nat)
    (v : Vector ℤ (L.factorCount + L.coeffWidth))
    (hvL : Hex.Matrix.memLattice L.basis v)
    (hvBound : ∀ x : Fin (L.factorCount + L.coeffWidth), v[x].natAbs ≤ V)
    (hdataBound : ∀ S (x : Fin (L.factorCount + L.coeffWidth)),
      (data S).vector[x].natAbs ≤ U)
    (hvW :
      (fun i : Fin L.factorCount => v[Fin.castAdd L.coeffWidth i]) ∉
        trueSupportSpanInt trueSupports) :
    ∃ w : Vector ℤ (L.factorCount + L.coeffWidth),
      Hex.Matrix.memLattice L.basis w ∧
      (∃ i : Fin L.factorCount,
        w[Fin.castAdd L.coeffWidth i] = 0) ∧
      (∀ S ∈ trueSupports, ∃ i ∈ S,
        w[Fin.castAdd L.coeffWidth i] ≠ 0) ∧
      ∀ x : Fin (L.factorCount + L.coeffWidth),
        w[x].natAbs ≤ V + V * U + trueSupports.ncard * U := by
  classical
  letI : Fintype trueSupports := (Set.toFinite trueSupports).fintype
  let e : Fin L.factorCount → ℤ :=
    fun i => v[Fin.castAdd L.coeffWidth i]
  obtain ⟨S₀, hS₀, i₀, hi₀, k₀, hk₀, hik⟩ :=
    exists_ne_on_support_of_not_mem_trueSupportSpanInt
      trueSupports hcover hdisjoint hne e hvW
  let S₀' : trueSupports := ⟨S₀, hS₀⟩
  let zeroOn (S : trueSupports) : Prop :=
    ∀ i ∈ S.1, e i = 0
  obtain ⟨c, hc⟩ := hvL
  let supportCoeffs :
      (S : trueSupports) →
        Vector ℤ (L.factorCount + L.coeffWidth) :=
    fun S => (data S).memLattice.choose
  have hsupportCoeffs (S : trueSupports) :
      Hex.Matrix.vecMul (supportCoeffs S) L.basis = (data S).vector :=
    (data S).memLattice.choose_spec
  have hsupportFirst (S : trueSupports) (i : Fin L.factorCount) :
      (supportCoeffs S)[Fin.castAdd L.coeffWidth i] =
        indicatorVector S.1 i := by
    calc
      (supportCoeffs S)[Fin.castAdd L.coeffWidth i] =
          (Hex.Matrix.vecMul (supportCoeffs S) L.basis)[
            Fin.castAdd L.coeffWidth i] :=
        (vecMul_first_of_blockForm L hL (supportCoeffs S) i).symm
      _ = (data S).vector[Fin.castAdd L.coeffWidth i] :=
        congrArg (fun x => x[Fin.castAdd L.coeffWidth i]) (hsupportCoeffs S)
      _ = indicatorVector S.1 i := (data S).project_eq i
  have hcFirst (i : Fin L.factorCount) :
      c[Fin.castAdd L.coeffWidth i] = e i := by
    calc
      c[Fin.castAdd L.coeffWidth i] =
          (Hex.Matrix.vecMul c L.basis)[Fin.castAdd L.coeffWidth i] :=
        (vecMul_first_of_blockForm L hL c i).symm
      _ = v[Fin.castAdd L.coeffWidth i] :=
        congrArg (fun x => x[Fin.castAdd L.coeffWidth i]) hc
      _ = e i := rfl
  have hsupportFirstNat (S : trueSupports) (i : Fin L.factorCount) :
      (supportCoeffs S)[(Fin.castAdd L.coeffWidth i).val]'(by
        simpa using (Fin.castAdd L.coeffWidth i).isLt) =
        indicatorVector S.1 i := by
    simpa only [Fin.getElem_fin] using hsupportFirst S i
  have hcFirstNat (i : Fin L.factorCount) :
      c[(Fin.castAdd L.coeffWidth i).val]'(by
        simpa using (Fin.castAdd L.coeffWidth i).isLt) = e i := by
    simpa only [Fin.getElem_fin] using hcFirst i
  let c' : Vector ℤ (L.factorCount + L.coeffWidth) :=
    Vector.ofFn fun x =>
      c[x] - e i₀ * (supportCoeffs S₀')[x] +
        ∑ S : trueSupports,
          if zeroOn S then (supportCoeffs S)[x] else 0
  let w : Vector ℤ (L.factorCount + L.coeffWidth) :=
    Hex.Matrix.vecMul c' L.basis
  have hwL : Hex.Matrix.memLattice L.basis w := ⟨c', rfl⟩
  have hcoord (i : Fin L.factorCount) :
      w[Fin.castAdd L.coeffWidth i] =
        e i - e i₀ * indicatorVector S₀ i +
          ∑ S : trueSupports,
            if zeroOn S then indicatorVector S.1 i else 0 := by
    change
      (Hex.Matrix.vecMul c' L.basis)[Fin.castAdd L.coeffWidth i] = _
    rw [vecMul_first_of_blockForm L hL]
    dsimp only [c']
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rw [hcFirstNat i, hsupportFirstNat S₀' i]
    simp_rw [hsupportFirstNat]
    rfl
  have hcorrection (T : trueSupports) (i : Fin L.factorCount) (hi : i ∈ T.1) :
      (∑ S : trueSupports,
          if zeroOn S then indicatorVector S.1 i else 0) =
        if zeroOn T then 1 else 0 := by
    rw [Finset.sum_eq_single T]
    · by_cases hzero : zeroOn T
      · rw [if_pos hzero, if_pos hzero,
          indicatorVector_apply_mem T.1 hi]
      · rw [if_neg hzero, if_neg hzero]
    · intro S _ hST
      have hiS : i ∉ S.1 := by
        intro hiS
        apply hST
        exact Subtype.ext (hdisjoint S.1 S.2 T.1 T.2 i hiS hi)
      by_cases hzero : zeroOn S
      · rw [if_pos hzero, indicatorVector_apply_not_mem S.1 hiS]
      · rw [if_neg hzero]
    · intro h
      exact absurd (Finset.mem_univ T) h
  have hS₀_not_zero : ¬ zeroOn S₀' := by
    intro hzero
    exact hik ((hzero i₀ hi₀).trans (hzero k₀ hk₀).symm)
  have hzeroCoord :
      w[Fin.castAdd L.coeffWidth i₀] = 0 := by
    rw [hcoord i₀, indicatorVector_apply_mem S₀ hi₀,
      hcorrection S₀' i₀ hi₀, if_neg hS₀_not_zero]
    ring
  refine ⟨w, hwL, ⟨i₀, hzeroCoord⟩, ?_, ?_⟩
  · intro T hT
    let T' : trueSupports := ⟨T, hT⟩
    by_cases hTS : T = S₀
    · subst T
      refine ⟨k₀, hk₀, ?_⟩
      rw [hcoord k₀, indicatorVector_apply_mem S₀ hk₀,
        hcorrection S₀' k₀ hk₀, if_neg hS₀_not_zero]
      intro h
      apply hik
      linarith
    · have hS₀T : ∀ i ∈ T, i ∉ S₀ := by
        intro i hiT hiS
        exact hTS (hdisjoint T hT S₀ hS₀ i hiT hiS)
      by_cases hzero : zeroOn T'
      · obtain ⟨i, hi⟩ := hne T hT
        refine ⟨i, hi, ?_⟩
        rw [hcoord i, indicatorVector_apply_not_mem S₀ (hS₀T i hi),
          hcorrection T' i hi, if_pos hzero, hzero i hi]
        norm_num
      · dsimp only [zeroOn] at hzero
        push Not at hzero
        obtain ⟨i, hi, hei⟩ := hzero
        refine ⟨i, hi, ?_⟩
        rw [hcoord i, indicatorVector_apply_not_mem S₀ (hS₀T i hi),
          hcorrection T' i hi, if_neg]
        · simpa using hei
        · exact fun hz => hei (hz i hi)
  · intro x
    have hwcoord :
        w[x] =
          v[x] - e i₀ * (data S₀').vector[x] +
            ∑ S : trueSupports,
              if zeroOn S then (data S).vector[x] else 0 := by
      change (Hex.Matrix.vecMul c' L.basis)[x] = _
      rw [vecMul_getElem_eq_sum]
      dsimp only [c']
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]
      change
        (∑ i : Fin (L.factorCount + L.coeffWidth),
          L.basis[i][x] *
            (c[i] - e i₀ * (supportCoeffs S₀')[i] +
              ∑ S : trueSupports,
                if zeroOn S then (supportCoeffs S)[i] else 0)) = _
      have hvx : v[x.val]'x.isLt =
          ∑ i : Fin (L.factorCount + L.coeffWidth),
            L.basis[i][x] * c[i] := by
        simpa only [Fin.getElem_fin] using
          (congrArg (fun z => z[x]) hc.symm).trans
            (vecMul_getElem_eq_sum L.basis c x)
      have hdatax : (data S₀').vector[x.val]'x.isLt =
          ∑ i : Fin (L.factorCount + L.coeffWidth),
            L.basis[i][x] * (supportCoeffs S₀')[i] := by
        simpa only [Fin.getElem_fin] using
          (congrArg (fun z => z[x]) (hsupportCoeffs S₀').symm).trans
            (vecMul_getElem_eq_sum L.basis (supportCoeffs S₀') x)
      rw [hvx, hdatax]
      simp only [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 1
      · congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S _
        by_cases hzero : zeroOn S
        · simp only [if_pos hzero]
          rw [← vecMul_getElem_eq_sum, hsupportCoeffs]
          simp only [Fin.getElem_fin]
        · simp [hzero]
    rw [hwcoord]
    calc
      (v[x] - e i₀ * (data S₀').vector[x] +
          ∑ S : trueSupports,
            if zeroOn S then (data S).vector[x] else 0).natAbs
          ≤ v[x].natAbs +
              (e i₀ * (data S₀').vector[x]).natAbs +
              (∑ S : trueSupports,
                if zeroOn S then (data S).vector[x] else 0).natAbs := by
            exact (Int.natAbs_add_le _ _).trans
              (Nat.add_le_add_right (Int.natAbs_sub_le _ _) _)
      _ ≤ V + V * U + ∑ _S : trueSupports, U := by
            gcongr
            · exact hvBound x
            · rw [Int.natAbs_mul]
              exact Nat.mul_le_mul (by
                simpa [e] using hvBound (Fin.castAdd L.coeffWidth i₀))
                (hdataBound S₀' x)
            · have hsum : ∀ s : Finset trueSupports,
                  (∑ S ∈ s,
                    if zeroOn S then (data S).vector[x] else 0).natAbs ≤
                    ∑ S ∈ s,
                      (if zeroOn S then (data S).vector[x] else 0).natAbs := by
                intro s
                induction s using Finset.induction_on with
                | empty => simp
                | @insert S s hS ih =>
                    rw [Finset.sum_insert hS, Finset.sum_insert hS]
                    exact (Int.natAbs_add_le _ _).trans
                      (Nat.add_le_add_left ih _)
              have hterm : ∀ S : trueSupports,
                  (if zeroOn S then (data S).vector[x] else 0).natAbs ≤ U := by
                intro S
                split
                · exact hdataBound S x
                · simp
              have hsum' :
                  (∑ S : trueSupports,
                    if zeroOn S then (data S).vector[x] else 0).natAbs ≤
                    ∑ S : trueSupports,
                      (if zeroOn S then (data S).vector[x] else 0).natAbs := by
                simpa using hsum Finset.univ
              have hterms :
                  (∑ S : trueSupports,
                    (if zeroOn S then (data S).vector[x] else 0).natAbs) ≤
                    ∑ _S : trueSupports, U :=
                Finset.sum_le_sum fun S _ => hterm S
              exact hsum'.trans hterms
      _ = V + V * U + trueSupports.ncard * U := by
            simp [Finset.sum_const, Set.fintypeCard_eq_ncard]

/--
The geometric half of the BHKS reverse containment.  If every bounded adjusted
lattice vector with one zero local exponent and a nonzero exponent on every
true support is impossible, then every executable retained row belongs to the
true-support span.

The theorem isolates all LLL bookkeeping: the caller supplies only coordinate
bounds for retained rows and support short vectors, plus the algebraic
bad-vector contradiction.
-/
theorem projectedRowSpanInt_le_trueSupportSpanInt_of_no_bad
    (L : Hex.BhksLatticeBasis) (hL : BhksBlockForm L)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hcover : ∀ i : Fin L.factorCount, ∃ S ∈ trueSupports, i ∈ S)
    (hdisjoint :
      ∀ S ∈ trueSupports, ∀ T ∈ trueSupports,
        ∀ i : Fin L.factorCount, i ∈ S → i ∈ T → S = T)
    (hne : ∀ S ∈ trueSupports, S.Nonempty)
    (data : ∀ S : trueSupports, SupportShortVectorData L S.1)
    (V U : Nat)
    (hretainedBound :
      ∀ j : Fin (L.factorCount + L.coeffWidth),
        j.val < Hex.bhksCutPrefixCount L
          (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix →
        ∀ x : Fin (L.factorCount + L.coeffWidth),
          (((Hex.bhksProjectedRowsTrace L hrows).reducedMatrix.row j)[x]).natAbs ≤ V)
    (hdataBound :
      ∀ S (x : Fin (L.factorCount + L.coeffWidth)),
        (data S).vector[x].natAbs ≤ U)
    (hnoBad :
      ∀ w : Vector ℤ (L.factorCount + L.coeffWidth),
        Hex.Matrix.memLattice L.basis w →
        (∃ i : Fin L.factorCount, w[Fin.castAdd L.coeffWidth i] = 0) →
        (∀ S ∈ trueSupports, ∃ i ∈ S,
          w[Fin.castAdd L.coeffWidth i] ≠ 0) →
        (∀ x : Fin (L.factorCount + L.coeffWidth),
          w[x].natAbs ≤ V + V * U + trueSupports.ncard * U) →
        False) :
    projectedRowSpanInt (Hex.bhksProjectedRows L hrows) ≤
      trueSupportSpanInt trueSupports := by
  apply projectedRowSpanInt_le_trueSupportSpanInt_of_rows
  intro i
  by_contra hiW
  obtain ⟨j, hjcut, hproj⟩ := projectedRow_exists_retainedSource L hrows i
  let v :=
    (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix.row j
  have hvRed :
      Hex.Matrix.memLattice
        (Hex.bhksProjectedRowsTrace L hrows).reducedMatrix v := by
    exact matrixRow_memLattice _ j
  have hvL : Hex.Matrix.memLattice L.basis v :=
    (traceReducedMatrix_memLattice_iff L hrows v).mp hvRed
  have hvBound :
      ∀ x : Fin (L.factorCount + L.coeffWidth), v[x].natAbs ≤ V :=
    fun x => hretainedBound j hjcut x
  have hvW :
      (fun k : Fin L.factorCount => v[Fin.castAdd L.coeffWidth k]) ∉
        trueSupportSpanInt trueSupports := by
    intro hvW'
    apply hiW
    have heq :
        Matrix.row
            (projectedRowsIntMatrix (Hex.bhksProjectedRows L hrows)) i =
          fun k : Fin L.factorCount => v[Fin.castAdd L.coeffWidth k] := by
      funext k
      exact hproj k
    rwa [heq]
  obtain ⟨w, hwL, hwzero, hwnonzero, hwBound⟩ :=
    exists_adjustedVector L hL trueSupports hcover hdisjoint hne data V U
      v hvL hvBound hdataBound hvW
  exact hnoBad w hwL hwzero hwnonzero hwBound

/-- Casting an integer vector in the executable projected span to `ℚ` places it
in the rational row space used by RREF. -/
theorem intVectorToRat_mem_projectedRowSpaceRat
    (L : Hex.BhksProjectedRows) {v : Fin L.factorCount → ℤ}
    (hv : v ∈ projectedRowSpanInt L) :
    intVectorToRat v ∈ projectedRowSpaceRat L := by
  have hcast := intVectorToRat_mem_span_rat_of_mem_span_int hv
  unfold projectedRowSpaceRat projectedRowSpanInt at *
  rwa [range_row_projectedRowsRatMatrix_eq_image L]

/--
If `L' = W`, equality of all coordinates in the rational projected row space
is exactly equality of true-support membership signatures.
-/
theorem projectedRowSpace_coordAgreement_iff_supportEquivalent
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hspan : projectedRowSpanInt L = trueSupportSpanInt trueSupports)
    (j k : Fin L.factorCount) :
    (∀ v : Fin L.factorCount → ℚ,
        v ∈ projectedRowSpaceRat L → v j = v k) ↔
      supportEquivalent trueSupports j k := by
  constructor
  · intro hagree S hS
    have hint :
        indicatorVector S ∈ projectedRowSpanInt L := by
      rw [hspan]
      exact indicatorVector_mem_trueSupportSpanInt trueSupports ⟨S, hS⟩
    have hrat := intVectorToRat_mem_projectedRowSpaceRat L hint
    have hcoord := hagree (intVectorToRat (indicatorVector S)) hrat
    change ((indicatorVector S j : ℤ) : ℚ) =
      ((indicatorVector S k : ℤ) : ℚ) at hcoord
    have hz : indicatorVector S j = indicatorVector S k := by
      exact_mod_cast hcoord
    by_cases hj : j ∈ S
    · have hk : k ∈ S := by
        by_contra hk
        rw [indicatorVector_apply_mem S hj,
          indicatorVector_apply_not_mem S hk] at hz
        omega
      exact ⟨fun _ => hk, fun _ => hj⟩
    · have hk : k ∉ S := by
        intro hk
        rw [indicatorVector_apply_not_mem S hj,
          indicatorVector_apply_mem S hk] at hz
        omega
      exact ⟨fun h => absurd h hj, fun h => absurd h hk⟩
  · intro hequiv v hv
    unfold projectedRowSpaceRat at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨i, rfl⟩
        have hint :
            Matrix.row (projectedRowsIntMatrix L) i ∈
              trueSupportSpanInt trueSupports := by
          rw [← hspan]
          exact projectedRow_mem_projectedRowSpanInt L i
        have hcoord :=
          coord_eq_of_mem_trueSupportSpanInt trueSupports hequiv hint
        simpa [projectedRowsRatMatrix, projectedRowsIntMatrix, Matrix.row]
          using congrArg (fun z : ℤ => (z : ℚ)) hcoord
    | zero => simp
    | add u w _ _ hu hw => simp only [Pi.add_apply, hu, hw]
    | smul q w _ hw => simp only [Pi.smul_apply, smul_eq_mul, hw]

/-- The executable rational matrix and the Mathlib-facing projected-row matrix
have identical entries. -/
theorem matrixEquiv_projectedRowsAsRat_eq
    (L : Hex.BhksProjectedRows) :
    HexMatrixMathlib.matrixEquiv
        (Hex.bhksProjectedRowsAsRatMatrix
          L.projectedRows L.projectedRows.size L.factorCount) =
      projectedRowsRatMatrix L := by
  ext i j
  rw [HexMatrixMathlib.matrixEquiv_apply]
  unfold Hex.bhksProjectedRowsAsRatMatrix projectedRowsRatMatrix
  rw [Hex.Matrix.getElem_ofFn]

/--
Once `L' = W`, two columns of the executable RREF agree exactly when the
corresponding lifted-factor indices lie in the same true supports.
-/
theorem rowReduce_columnAgreement_iff_supportEquivalent
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hspan : projectedRowSpanInt L = trueSupportSpanInt trueSupports)
    (j k : Fin L.factorCount) :
    let M := Hex.bhksProjectedRowsAsRatMatrix
      L.projectedRows L.projectedRows.size L.factorCount
    (∀ i : Fin L.projectedRows.size,
        (Hex.Matrix.rowReduce M).echelon[i][j] =
          (Hex.Matrix.rowReduce M).echelon[i][k]) ↔
      supportEquivalent trueSupports j k := by
  dsimp only
  rw [rowReduce_columnAgreement_iff_forall_mem_span_coord_eq]
  have hrows :
      (Set.range fun i : Fin L.projectedRows.size =>
          Matrix.row
            (HexMatrixMathlib.matrixEquiv
              (Hex.bhksProjectedRowsAsRatMatrix
                L.projectedRows L.projectedRows.size L.factorCount)) i) =
        Set.range (fun i : Fin L.projectedRows.size =>
          Matrix.row (projectedRowsRatMatrix L) i) := by
    rw [matrixEquiv_projectedRowsAsRat_eq L]
  rw [hrows]
  exact projectedRowSpace_coordAgreement_iff_supportEquivalent
    L trueSupports hspan j k
end BHKS

end

end HexBerlekampZassenhausMathlib
