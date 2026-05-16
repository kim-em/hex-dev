import HexBerlekampZassenhausMathlib.Lattice
import HexBerlekampZassenhausMathlib.ColumnSignature
import HexBerlekampZassenhausMathlib.SignatureClasses
import HexBerlekampZassenhausMathlib.TerminationBound

/-!
Forward-verification bridge for BHKS recovery at fixed precision.

This module connects the abstract `L' = W` separation theorem from
`Lattice.lean`/`TerminationBound.lean` (BHKS Lemma 3.4 / Group D obligation
that issue #3034 specialised to the executable cap) to the executable
equivalence-class recovery surface in `HexBerlekampZassenhaus/Basic.lean`.

Two layers are exposed:

* `EquivalenceClassRecoveryHypotheses` and
  `bhksEquivalenceClassIndicators_eq_of_recovery`: package the BHKS Lemma 3.3
  output as an abstract hypothesis that the executable
  `bhksEquivalenceClassIndicators` array matches a target indicator list,
  given `L' = W`.  The unconditional discharge of this hypothesis (B7)
  depends on still-open executable RREF correctness work, so it is left
  abstract here.

* `RecoveryHypotheses` and `bhksRecover_eq_some_of_recovery`: package the
  forward-verification clause of the SPEC Group D obligation
  (precision ≥ Mignotte; A2 reconstruction; B7 indicator identification;
  exact division of every candidate; product equals input) as a single
  proof-facing record, then show the executable `bhksRecover?` returns
  `some <expected factors>` under these hypotheses.

The theorem statements are intentionally scoped to a single
precision/recovery call as required by issue #3035: the outer
precision-doubling loop and the public `factorFast_terminates` theorem are
out of scope for this module.
-/

namespace HexBerlekampZassenhausMathlib

namespace BHKS

theorem supportEquivalent_iff_forall_mem_trueFactorIndicatorLattice_rat_coord_eq
    {r : Nat} (trueSupports : Set (Set (Fin r))) (j k : Fin r) :
    supportEquivalent trueSupports j k ↔
      ∀ v : Fin r → ℚ,
        v ∈ trueFactorIndicatorLattice_rat trueSupports →
          v j = v k := by
  constructor
  · intro hsupport v hv
    unfold trueFactorIndicatorLattice_rat at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨S, rfl⟩
      have hmem := hsupport S S.2
      by_cases hj : j ∈ S.1
      · have hk : k ∈ S.1 := (hmem.mp hj)
        simp [intVectorToRat, indicatorVector, hj, hk]
      · have hk : k ∉ S.1 := by
          intro hk
          exact hj ((hmem.mpr hk))
        simp [intVectorToRat, indicatorVector, hj, hk]
    | zero =>
      simp
    | add u v _ _ hu hv =>
      simp [Pi.add_apply, hu, hv]
    | smul a v _ hv =>
      simp [Pi.smul_apply, hv]
  · intro hcoords S hS
    constructor
    · intro hj
      by_contra hk
      have hmem :
          intVectorToRat (indicatorVector S) ∈
            trueFactorIndicatorLattice_rat trueSupports := by
        exact Submodule.subset_span ⟨⟨S, hS⟩, rfl⟩
      have hcoord := hcoords (intVectorToRat (indicatorVector S)) hmem
      simp [intVectorToRat, indicatorVector, hj, hk] at hcoord
    · intro hk
      by_contra hj
      have hmem :
          intVectorToRat (indicatorVector S) ∈
            trueFactorIndicatorLattice_rat trueSupports := by
        exact Submodule.subset_span ⟨⟨S, hS⟩, rfl⟩
      have hcoord := hcoords (intVectorToRat (indicatorVector S)) hmem
      simp [intVectorToRat, indicatorVector, hj, hk] at hcoord

private theorem partitionByMinColumn_eq_supportPartitionByMinColumn_of_iff
    {r : Nat} (trueSupports : Set (Set (Fin r))) (sig : Nat → Array Rat)
    (hiff :
      ∀ j k, (hj : j < r) → (hk : k < r) →
        (sig j = sig k ↔
          supportEquivalent trueSupports ⟨j, hj⟩ ⟨k, hk⟩)) :
    partitionByMinColumn r sig = supportPartitionByMinColumn trueSupports := by
  have hreps : representativeColumns r sig =
      supportRepresentativeColumns trueSupports := by
    unfold representativeColumns supportRepresentativeColumns
    apply List.filter_congr
    intro rep hrep
    have hrep_lt : rep < r := List.mem_range.mp hrep
    congr 1
    apply List.filter_congr
    intro k hk
    have hk_lt_r : k < r := lt_of_lt_of_le (List.mem_range.mp hk) (Nat.le_of_lt hrep_lt)
    have hprop :
        sig k = sig rep ↔ supportEquivalentAt trueSupports k rep :=
      (hiff k rep hk_lt_r hrep_lt).trans
        (supportEquivalentAt_iff trueSupports hk_lt_r hrep_lt).symm
    by_cases hsig : sig k = sig rep
    · have hsup : supportEquivalentAt trueSupports k rep := hprop.mp hsig
      simp [hsig, hsup]
    · have hsup : ¬ supportEquivalentAt trueSupports k rep := fun h => hsig (hprop.mpr h)
      simp [hsig, hsup]
  unfold partitionByMinColumn supportPartitionByMinColumn
  rw [hreps]
  apply List.map_congr_left
  intro rep hrep
  have hrep_lt : rep < r := supportRepresentativeColumns_lt trueSupports hrep
  unfold supportClassMembers
  apply List.filter_congr
  intro j hj
  have hj_lt : j < r := List.mem_range.mp hj
  have hprop :
      sig j = sig rep ↔ supportEquivalentAt trueSupports j rep :=
    (hiff j rep hj_lt hrep_lt).trans
      (supportEquivalentAt_iff trueSupports hj_lt hrep_lt).symm
  by_cases hsig : sig j = sig rep
  · have hsup : supportEquivalentAt trueSupports j rep := hprop.mp hsig
    simp [hsig, hsup]
  · have hsup : ¬ supportEquivalentAt trueSupports j rep := fun h => hsig (hprop.mpr h)
    simp [hsig, hsup]

/-- The RREF column signature expression used by
`Hex.bhksEquivalenceClassIndicators`, exposed as a proof-facing definition. -/
def projectedRowsRrefColumnSignature (L : Hex.BhksProjectedRows) (j : Nat) :
    Array Rat :=
  let n := L.projectedRows.size
  let r := L.factorCount
  let M : Hex.Matrix Rat n r := Hex.bhksProjectedRowsAsRatMatrix L.projectedRows n r
  let D := Hex.Matrix.rref M
  let echelonRows : Array (Array Rat) := D.echelon.toArray.map (·.toArray)
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
        (Hex.Matrix.rref
          (Hex.bhksProjectedRowsAsRatMatrix
            L.projectedRows L.projectedRows.size L.factorCount)).echelon[i][
              (⟨j, hj⟩ : Fin L.factorCount)] =
        (Hex.Matrix.rref
          (Hex.bhksProjectedRowsAsRatMatrix
            L.projectedRows L.projectedRows.size L.factorCount)).echelon[i][
              (⟨k, hk⟩ : Fin L.factorCount)] := by
  constructor
  · intro h i
    have hget := congrArg (fun a : Array Rat => a.getD i.val 0) h
    simpa [projectedRowsRrefColumnSignature, Array.getD, hj, hk] using hget
  · intro h
    apply Array.ext
    · simp [projectedRowsRrefColumnSignature]
    · intro i hi₁ hi₂
      have hi : i < L.projectedRows.size := by
        simpa [projectedRowsRrefColumnSignature] using hi₁
      have hrow := h ⟨i, hi⟩
      simpa [projectedRowsRrefColumnSignature, Array.getD, hj, hk] using hrow

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
  exact rref_columnAgreement_iff_forall_mem_span_coord_eq
    (Hex.bhksProjectedRowsAsRatMatrix
      L.projectedRows L.projectedRows.size L.factorCount) ⟨j, hj⟩ ⟨k, hk⟩

theorem projectedRowsRrefColumnSignature_eq_iff_supportEquivalent_of_projectedRowSpan_eq
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hint : projectedRowSpanInt L = trueFactorIndicatorLattice trueSupports)
    {j k : Nat} (hj : j < L.factorCount) (hk : k < L.factorCount) :
    projectedRowsRrefColumnSignature L j = projectedRowsRrefColumnSignature L k ↔
      supportEquivalent trueSupports ⟨j, hj⟩ ⟨k, hk⟩ := by
  have hsig :=
    projectedRowsRrefColumnSignature_eq_iff_forall_mem_projectedRowSpaceRat_coord_eq
      L hj hk
  have hspace := projectedRowSpaceRat_eq_trueFactorIndicatorLattice_rat
    L trueSupports hint
  rw [hspace] at hsig
  exact hsig.trans
    (supportEquivalent_iff_forall_mem_trueFactorIndicatorLattice_rat_coord_eq
      trueSupports ⟨j, hj⟩ ⟨k, hk⟩).symm

theorem bhksEquivalenceClassIndicators_eq_expectedIndicatorArrayOfSupports
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hint : projectedRowSpanInt L = trueFactorIndicatorLattice trueSupports) :
    Hex.bhksEquivalenceClassIndicators L =
      expectedIndicatorArrayOfSupports trueSupports := by
  let sig := projectedRowsRrefColumnSignature L
  have hpartition :
      partitionByMinColumn L.factorCount sig =
        supportPartitionByMinColumn trueSupports := by
    exact partitionByMinColumn_eq_supportPartitionByMinColumn_of_iff
      trueSupports sig
      (fun j k hj hk =>
        projectedRowsRrefColumnSignature_eq_iff_supportEquivalent_of_projectedRowSpan_eq
          L trueSupports hint hj hk)
  have hfold :
      ((List.range L.factorCount).foldl
        (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) []).map Prod.snd =
        supportPartitionByMinColumn trueSupports := by
    rw [bhksInsertSignatureClass_fold_eq_partitionByMinColumn, hpartition]
  unfold Hex.bhksEquivalenceClassIndicators expectedIndicatorArrayOfSupports
  change
    ((((List.range L.factorCount).foldl
      (fun acc j => Hex.bhksInsertSignatureClass (sig j) j acc) []).map Prod.snd).map
        (fun cls => classIndicatorArray L.factorCount cls)).toArray =
      ((supportPartitionByMinColumn trueSupports).map
        (fun members => classIndicatorArray L.factorCount members)).toArray
  rw [hfold]

/-- The executable BHKS lattice basis at the abstract Hensel-lift data.

This is the same expression that `Hex.bhksRecover?` builds internally;
extracting it as a named definition lets the proof-facing recovery layer
refer to it without rebuilding the lift data each time. -/
def latticeBasisOfLiftData (f : Hex.ZPoly) (d : Hex.LiftData) :
    Hex.BhksLatticeBasis :=
  Hex.bhksLatticeBasis f d.p d.k d.liftedFactors

/-- Positive-dimension hypothesis on the executable BHKS lattice basis at the
abstract Hensel-lift data.  The executable `Hex.bhksRecover?` early-returns
`none` when this fails. -/
abbrev HasPositiveDimension (f : Hex.ZPoly) (d : Hex.LiftData) : Prop :=
  1 ≤ (latticeBasisOfLiftData f d).factorCount +
      (latticeBasisOfLiftData f d).coeffWidth

/-- The executable BHKS projected-row data at the abstract Hensel-lift data. -/
def projectedRowsOfLiftData (f : Hex.ZPoly) (d : Hex.LiftData)
    (hrows : HasPositiveDimension f d) : Hex.BhksProjectedRows :=
  Hex.bhksProjectedRows (latticeBasisOfLiftData f d) hrows
    (Hex.bhksLatticeBasis_independent f d.p d.k d.liftedFactors d.p_pos)

/-- Executable bad-vector witness whose lattice and projected rows are the
ones used by the forward-recovery package at the given lift data.  The
remaining fields identify the selected local factor and auxiliary polynomial
for the bad-vector route; cap-separation callers supply their proof obligations
through `ExecutableCapSeparationHypotheses`. -/
def badVectorWitnessOfLiftData
    (f : Hex.ZPoly) (d : Hex.LiftData) (hrows : HasPositiveDimension f d)
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly) :
    ExecutableBadVectorWitness where
  input := f
  liftData := d
  lattice := latticeBasisOfLiftData f d
  projectedRows := projectedRowsOfLiftData f d hrows
  localFactorIndex := localFactorIndex
  localFactorDegree := localFactorDegree
  H := H
  lattice_matches_lift := rfl
  projected_factor_count := rfl

/--
Specialize the executable-cap BHKS separation theorem to the projected-row
shape used by `ForwardRecoveryInputs`.

The conclusion has the same shape as
`ForwardRecoveryInputs.lattice_eq_indicators`; the later B7/A2 recovery fields
remain outside this theorem and can be supplied independently.
-/
theorem projectedRowsOfLiftData_eq_trueFactorIndicatorLattice_of_cap
    (f : Hex.ZPoly) (d : Hex.LiftData) (hrows : HasPositiveDimension f d)
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d hrows).factorCount)))
    {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
        trueSupports) :
    projectedRowSpanInt (projectedRowsOfLiftData f d hrows) =
      trueFactorIndicatorLattice trueSupports :=
  projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap
    (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
    trueSupports ha C hC_nonneg hC hcap

/-- The executable BHKS equivalence-class indicator array at the abstract
Hensel-lift data. -/
def equivalenceClassIndicatorsOfLiftData (f : Hex.ZPoly) (d : Hex.LiftData)
    (hrows : HasPositiveDimension f d) : Array (Array Int) :=
  Hex.bhksEquivalenceClassIndicators (projectedRowsOfLiftData f d hrows)

/--
Proof-facing hypotheses for the BHKS Lemma 3.3 / B7 step at fixed precision.

`SeparationHypotheses` (or the cap-specialised
`ExecutableCapSeparationHypotheses` from `TerminationBound.lean`) provides
`L' = W`.  The `indicators_match` field is the abstract conclusion of BHKS
Lemma 3.3 connecting the executable rref + signature partition to a target
indicator list; `EquivalenceClassRecoveryHypotheses.ofIndicatorLattice`
discharges it for the canonical support-driven indicator array.
-/
structure EquivalenceClassRecoveryHypotheses
    (f : Hex.ZPoly) (d : Hex.LiftData) where
  /-- Positive lattice dimension so the projected rows are well-defined. -/
  rows_pos : HasPositiveDimension f d
  /-- True-factor supports backing the indicator lattice `W`. -/
  trueSupports :
    Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount))
  /-- The BHKS `L' = W` conclusion specialised to this lift data. -/
  lattice_eq_indicators :
    BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
      BHKS.trueFactorIndicatorLattice trueSupports
  /-- BHKS Lemma 3.3 conclusion: the executable equivalence-class indicators
      match a target list determined by the true-factor supports. -/
  expectedIndicators : Array (Array Int)
  indicators_match :
    equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators

/-- Lift-data form of the B7 bridge: when the executable projected row span is
the true-factor indicator lattice, the executable equivalence-class indicators
are the canonical support-driven indicator array. -/
theorem equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports) :
    equivalenceClassIndicatorsOfLiftData f d rows_pos =
      expectedIndicatorArrayOfSupports trueSupports :=
  bhksEquivalenceClassIndicators_eq_expectedIndicatorArrayOfSupports
    (projectedRowsOfLiftData f d rows_pos) trueSupports lattice_eq_indicators

namespace EquivalenceClassRecoveryHypotheses

/-- Build the B7 recovery package directly from `L' = W`, targeting the
canonical support-driven indicator array. -/
noncomputable def ofIndicatorLattice
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports) :
    EquivalenceClassRecoveryHypotheses f d where
  rows_pos := rows_pos
  trueSupports := trueSupports
  lattice_eq_indicators := lattice_eq_indicators
  expectedIndicators := expectedIndicatorArrayOfSupports trueSupports
  indicators_match :=
    equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports
      rows_pos trueSupports lattice_eq_indicators

end EquivalenceClassRecoveryHypotheses

/-- Under the equivalence-class recovery hypotheses, the executable
`bhksEquivalenceClassIndicators` output is exactly the expected indicator
list. This is the BHKS Lemma 3.3 / B7 bridge from `L' = W` to the executable
indicator surface. -/
theorem bhksEquivalenceClassIndicators_eq_of_recovery
    (f : Hex.ZPoly) (d : Hex.LiftData)
    (h : EquivalenceClassRecoveryHypotheses f d) :
    equivalenceClassIndicatorsOfLiftData f d h.rows_pos = h.expectedIndicators :=
  h.indicators_match

/-- BHKS Lemma 3.3 conclusion exposed at the raw projected rows, for callers
that already have the projected-rows value in hand. -/
theorem bhksEquivalenceClassIndicators_projectedRows_eq_of_recovery
    (f : Hex.ZPoly) (d : Hex.LiftData)
    (h : EquivalenceClassRecoveryHypotheses f d) :
    Hex.bhksEquivalenceClassIndicators
        (projectedRowsOfLiftData f d h.rows_pos) = h.expectedIndicators :=
  h.indicators_match

/--
Proof-facing hypotheses for forward BHKS recovery at fixed precision.

The fields encode the four guards inside the executable `Hex.bhksRecover?`:
positive lattice dimension, non-degenerate equivalence-class partition,
successful per-indicator integer reconstruction, and exact product check.
By the SPEC Group D forward-verification argument, these guards hold
simultaneously when the precision dominates Mignotte and `L' = W` holds.
The discharge of each individual field from the abstract precision /
separation hypotheses is left to later bridge work; this record packages
exactly what the executable function needs to return `some`.
-/
structure RecoveryHypotheses (f : Hex.ZPoly) (d : Hex.LiftData) where
  /-- Positive lattice dimension so the recovery enters the recovery branch. -/
  rows_pos : HasPositiveDimension f d
  /-- The equivalence-class partition is non-degenerate, so the executable
      function does not bail out via `bhksDegenerateIndicatorPartition`. -/
  nondegenerate :
    Hex.bhksDegenerateIndicatorPartition
        (projectedRowsOfLiftData f d rows_pos)
        (equivalenceClassIndicatorsOfLiftData f d rows_pos) = false
  /-- The verified factor list returned by the executable recovery. -/
  expectedFactors : Array Hex.ZPoly
  /-- Per-indicator centred-residue reconstruction succeeds and divides `f`. -/
  candidates_eq :
    Hex.bhksIndicatorCandidates? f d
        (equivalenceClassIndicatorsOfLiftData f d rows_pos) =
      some expectedFactors
  /-- The reconstructed factors multiply back to `f`, so the final product
      check inside `Hex.bhksRecover?` succeeds. -/
  product_eq : Array.polyProduct expectedFactors = f

/--
Forward-verification theorem (SPEC Group D, scoped to one precision/recovery
call): under the executable-cap recovery hypotheses, `Hex.bhksRecover? f d`
returns `some <expected factors>`.

This composes with `BHKS.projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap`
from `TerminationBound.lean` (the executable-cap `L' = W` theorem closed in
issue #3034): when the recovery hypotheses are constructed at any precision
that meets `Hex.factorFastPrecisionCap f`, the executable `bhksRecover?` call
inside `Hex.factorFastCoreWithBound` returns `some _`, so that loop iteration
exits via the success branch rather than the precision-doubling fallback.
-/
theorem bhksRecover_eq_some_of_recovery
    (f : Hex.ZPoly) (d : Hex.LiftData) (h : RecoveryHypotheses f d) :
    Hex.bhksRecover? f d = some h.expectedFactors := by
  have hrows : 1 ≤ (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount +
      (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors).coeffWidth := h.rows_pos
  have hnondeg :
      Hex.bhksDegenerateIndicatorPartition
          (Hex.bhksProjectedRows (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
            hrows (Hex.bhksLatticeBasis_independent f d.p d.k d.liftedFactors d.p_pos))
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (Hex.bhksLatticeBasis_independent f d.p d.k d.liftedFactors d.p_pos))) = false :=
    h.nondegenerate
  have hcand :
      Hex.bhksIndicatorCandidates? f d
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (Hex.bhksLatticeBasis_independent f d.p d.k d.liftedFactors d.p_pos))) =
        some h.expectedFactors :=
    h.candidates_eq
  have hprod := h.product_eq
  exact Hex.bhksRecover?_eq_some_of_checks f d hrows hnondeg hcand hprod

/-- Corollary form of `bhksRecover_eq_some_of_recovery` that drops the
expected-factors witness from the conclusion: under the recovery hypotheses,
`Hex.bhksRecover? f d` is in the `some _` branch. -/
theorem bhksRecover_isSome_of_recovery
    (f : Hex.ZPoly) (d : Hex.LiftData) (h : RecoveryHypotheses f d) :
    (Hex.bhksRecover? f d).isSome := by
  rw [bhksRecover_eq_some_of_recovery f d h]
  rfl

/--
Assemble the forward-recovery candidate equality from per-indicator A2
reconstruction facts.

This is the Mathlib-side bridge to the Mathlib-free fold helper
`Hex.bhksIndicatorCandidates?_eq_some_of_getD`: callers prove each expected
indicator reconstructs and exactly divides `f`, then this theorem supplies the
raw `ForwardRecoveryInputs.candidates_eq` equality.
-/
theorem bhksIndicatorCandidates?_eq_some_of_forwardCandidates
    (f : Hex.ZPoly) (d : Hex.LiftData)
    (expectedIndicators : Array (Array Int)) (expectedFactors : Array Hex.ZPoly)
    (hsize : expectedFactors.size = expectedIndicators.size)
    (hcandidate :
      ∀ i, i < expectedIndicators.size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate? f d (expectedIndicators.getD i #[]) =
            some (expectedFactors.getD i 0, quotient)) :
    Hex.bhksIndicatorCandidates? f d expectedIndicators =
      some expectedFactors :=
  Hex.bhksIndicatorCandidates?_eq_some_of_getD
    f d expectedIndicators expectedFactors hsize hcandidate

/--
Single-indicator A2 reconstruction from Mignotte precision. The selected
lifted factors are supplied explicitly by `hselected`, while
`hindicator_product` is the B7/A2-facing modular-product fact: after scaling
the selected lifted-factor product by `lc(f)`, it reduces modulo `p^k` to the
expected integer factor. The coefficient bound needed for centred lifting is
derived from `defaultFactorCoeffBound_valid`.
-/
theorem bhksIndicatorCandidate?_eq_some_of_mignottePrecision
    (f : Hex.ZPoly) (d : Hex.LiftData) (indicator : Array Int)
    (selected : Array Hex.ZPoly) (expectedFactor : Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (hselected :
      Hex.bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hdvd : expectedFactor ∣ f)
    (hexpected_prim : Hex.ZPoly.Primitive expectedFactor)
    (hexpected_sign : 0 ≤ Hex.DensePoly.leadingCoeff expectedFactor)
    (hexpected_monic : Hex.DensePoly.Monic expectedFactor)
    (hexpected_degree : 0 < expectedFactor.degree?.getD 0)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (hindicator_product :
      Hex.ZPoly.reduceModPow
          (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f) (Array.polyProduct selected))
          d.p d.k =
        Hex.ZPoly.reduceModPow expectedFactor d.p d.k) :
    ∃ quotient,
      Hex.bhksIndicatorCandidate? f d indicator =
        some (expectedFactor, quotient) :=
  Hex.bhksIndicatorCandidate?_eq_some_of_mignottePrecision
    f d indicator selected expectedFactor hselected hdvd
    (defaultFactorCoeffBound_valid f hf_ne_zero expectedFactor hdvd)
    hexpected_prim hexpected_sign hexpected_monic hexpected_degree
    hprecision hindicator_product

/--
Proof-facing inputs for the SPEC Group D forward-verification clause at one
precision/recovery call: `L' = W` (deliverable 1, supplied by issue #3034 at
the executable cap) plus the residual abstract obligations B7 (BHKS
Lemma 3.3 indicator identification) and A2 (Mignotte centred-residue
reconstruction) that this layer treats as hypotheses.

The Mignotte precision side condition is the SPEC's
`p^k > 2 · defaultFactorCoeffBound f`; the Group D obligation establishes
this whenever `Hex.factorFastPrecisionCap f ≤ k`, since the cap dominates
the Mignotte coefficient bound.  The two abstract obligations
(`indicators_match`, `candidates_eq`) wrap the per-step BHKS Lemma 3.3 / A2
content and are the natural follow-up tasks for later bridge work.
-/
structure ForwardRecoveryInputs (f : Hex.ZPoly) (d : Hex.LiftData) where
  /-- Positive lattice dimension so the projected rows / recovery branch make
      sense. -/
  rows_pos : HasPositiveDimension f d
  /-- True-factor supports backing the indicator lattice `W`. -/
  trueSupports :
    Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount))
  /-- BHKS `L' = W` at this lift data, supplied by #3034's
      `BHKS.projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap`. -/
  lattice_eq_indicators :
    BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
      BHKS.trueFactorIndicatorLattice trueSupports
  /-- Mignotte-precision side condition: the modular precision exceeds twice
      the executable Mignotte coefficient bound, so the centred-residue lift
      is unique. -/
  mignotte_precision :
    2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k
  /-- BHKS Lemma 3.3 / B7 conclusion, left abstract: the executable
      equivalence-class indicators agree with a target indicator list
      `expectedIndicators`. -/
  expectedIndicators : Array (Array Int)
  indicators_match :
    equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators
  /-- The chosen indicator partition is non-degenerate. -/
  nondegenerate :
    Hex.bhksDegenerateIndicatorPartition
        (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false
  /-- A2 + exact division, left abstract: each indicator reconstructs into a
      verified integer factor.  `expectedFactors` is the resulting factor
      array. -/
  expectedFactors : Array Hex.ZPoly
  candidates_eq :
    Hex.bhksIndicatorCandidates? f d expectedIndicators = some expectedFactors
  /-- Final product check: the verified factors multiply back to `f`. -/
  product_eq : Array.polyProduct expectedFactors = f

namespace ForwardRecoveryInputs

/--
Proof-facing package saying that `expectedFactors` is the true integer-factor
list for the current recovery target.  The per-factor fields are exactly the
facts needed by the A2 candidate reconstruction wrapper; `product_eq` is the
final executable recovery guard.
-/
structure ExpectedTrueFactors (f : Hex.ZPoly)
    (expectedIndicators : Array (Array Int))
    (expectedFactors : Array Hex.ZPoly) where
  /-- The true-factor list has one factor for each expected indicator. -/
  size_eq : expectedFactors.size = expectedIndicators.size
  /-- Every expected true factor divides the recovery target. -/
  divides :
    ∀ i, i < expectedIndicators.size →
      expectedFactors.getD i 0 ∣ f
  /-- Expected true factors are primitive integer polynomials. -/
  primitive :
    ∀ i, i < expectedIndicators.size →
      Hex.ZPoly.Primitive (expectedFactors.getD i 0)
  /-- Expected true factors use the positive-leading-coefficient convention. -/
  leadingCoeff_nonneg :
    ∀ i, i < expectedIndicators.size →
      0 ≤ Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0)
  /-- Expected true factors are monic at the square-free-core layer. -/
  monic :
    ∀ i, i < expectedIndicators.size →
      Hex.DensePoly.Monic (expectedFactors.getD i 0)
  /-- Expected true factors are nonconstant. -/
  positive_degree :
    ∀ i, i < expectedIndicators.size →
      0 < (expectedFactors.getD i 0).degree?.getD 0
  /-- The expected true factors multiply back to the recovery target. -/
  product_eq : Array.polyProduct expectedFactors = f

/--
The final BHKS recovery product guard follows directly from an expected
true-factor-list package.
-/
theorem productOfExpectedFactors
    {f : Hex.ZPoly} {expectedIndicators : Array (Array Int)}
    {expectedFactors : Array Hex.ZPoly}
    (h : ExpectedTrueFactors f expectedIndicators expectedFactors) :
    Array.polyProduct expectedFactors = f :=
  h.product_eq

/-- Extract the B7 equivalence-class recovery package from the full
forward-recovery input bundle. -/
def toEquivalenceClassRecoveryHypotheses {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d) : EquivalenceClassRecoveryHypotheses f d where
  rows_pos := h.rows_pos
  trueSupports := h.trueSupports
  lattice_eq_indicators := h.lattice_eq_indicators
  expectedIndicators := h.expectedIndicators
  indicators_match := h.indicators_match

/--
The executable non-degeneracy guard follows from the shape facts supplied by
the true-support indicator partition: the projected lattice has rows, the
partition has at least one class, and B7 did not collapse all local factors
into the single all-ones class.
-/
theorem nondegenerateOfTrueSupportIndicators
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (expectedIndicators : Array (Array Int))
    (hprojected_nonempty :
      (projectedRowsOfLiftData f d rows_pos).projectedRows.isEmpty = false)
    (hindicators_nonempty : expectedIndicators.isEmpty = false)
    (hnot_single_all_ones :
      (expectedIndicators.size == 1 &&
        Hex.bhksIndicatorAllOnes
          (projectedRowsOfLiftData f d rows_pos).factorCount
          (expectedIndicators.getD 0 #[])) = false) :
    Hex.bhksDegenerateIndicatorPartition
        (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false := by
  unfold Hex.bhksDegenerateIndicatorPartition
  rw [hindicators_nonempty, hprojected_nonempty]
  simp only [Bool.false_or]
  exact hnot_single_all_ones

/--
Build `ForwardRecoveryInputs` when the A2/exact-division obligation is
available as per-indicator reconstruction witnesses rather than as the folded
candidate equality.
-/
def ofIndicatorCandidateFacts
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (expectedIndicators : Array (Array Int))
    (indicators_match :
      equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false)
    (expectedFactors : Array Hex.ZPoly)
    (hsize : expectedFactors.size = expectedIndicators.size)
    (hcandidate :
      ∀ i, i < expectedIndicators.size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate? f d (expectedIndicators.getD i #[]) =
            some (expectedFactors.getD i 0, quotient))
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d where
  rows_pos := rows_pos
  trueSupports := trueSupports
  lattice_eq_indicators := lattice_eq_indicators
  mignotte_precision := mignotte_precision
  expectedIndicators := expectedIndicators
  indicators_match := indicators_match
  nondegenerate := nondegenerate
  expectedFactors := expectedFactors
  candidates_eq :=
    bhksIndicatorCandidates?_eq_some_of_forwardCandidates
      f d expectedIndicators expectedFactors hsize hcandidate
  product_eq := product_eq

/--
Fold the single-indicator Mignotte reconstruction theorem over an expected
indicator array. This is the A2 candidate-equality bridge for
`ForwardRecoveryInputs`: callers supply the selected lifted-factor products,
true-factor facts, and modular product equalities for each indicator, and the
executable candidate fold returns the expected factor array.
-/
theorem candidatesOfMignottePrecision
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (expectedIndicators : Array (Array Int))
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (hsize : expectedFactors.size = expectedIndicators.size)
    (hselected :
      ∀ i, i < expectedIndicators.size →
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            (expectedIndicators.getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hdivides :
      ∀ i, i < expectedIndicators.size →
        expectedFactors.getD i 0 ∣ f)
    (hprimitive :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.Primitive (expectedFactors.getD i 0))
    (hsign :
      ∀ i, i < expectedIndicators.size →
        0 ≤ Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0))
    (hmonic :
      ∀ i, i < expectedIndicators.size →
        Hex.DensePoly.Monic (expectedFactors.getD i 0))
    (hdegree :
      ∀ i, i < expectedIndicators.size →
        0 < (expectedFactors.getD i 0).degree?.getD 0)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (hproduct :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)
              (Array.polyProduct (selectedFactors.getD i #[])))
            d.p d.k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k) :
    Hex.bhksIndicatorCandidates? f d expectedIndicators =
      some expectedFactors :=
  bhksIndicatorCandidates?_eq_some_of_forwardCandidates
    f d expectedIndicators expectedFactors hsize
    (fun i hi =>
      bhksIndicatorCandidate?_eq_some_of_mignottePrecision
        f d (expectedIndicators.getD i #[])
        (selectedFactors.getD i #[]) (expectedFactors.getD i 0)
        hf_ne_zero (hselected i hi) (hdivides i hi)
        (hprimitive i hi) (hsign i hi) (hmonic i hi) (hdegree i hi)
        hprecision (hproduct i hi))

/--
Build `ForwardRecoveryInputs` from per-indicator Mignotte reconstruction
facts. This is the A2 capstone constructor: callers supply the selected-factor
array for each indicator, the modular-product equality that B7/A2 establishes,
and the expected true-factor facts; this constructor packages them through the
existing candidate fold.
-/
def ofMignottePrecisionCandidateProducts
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (expectedIndicators : Array (Array Int))
    (indicators_match :
      equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false)
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (hsize : expectedFactors.size = expectedIndicators.size)
    (hselected :
      ∀ i, i < expectedIndicators.size →
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            (expectedIndicators.getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hdivides :
      ∀ i, i < expectedIndicators.size →
        expectedFactors.getD i 0 ∣ f)
    (hprimitive :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.Primitive (expectedFactors.getD i 0))
    (hsign :
      ∀ i, i < expectedIndicators.size →
        0 ≤ Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0))
    (hmonic :
      ∀ i, i < expectedIndicators.size →
        Hex.DensePoly.Monic (expectedFactors.getD i 0))
    (hdegree :
      ∀ i, i < expectedIndicators.size →
        0 < (expectedFactors.getD i 0).degree?.getD 0)
    (hproduct :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)
              (Array.polyProduct (selectedFactors.getD i #[])))
            d.p d.k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k)
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d :=
  { rows_pos := rows_pos
    trueSupports := trueSupports
    lattice_eq_indicators := lattice_eq_indicators
    mignotte_precision := mignotte_precision
    expectedIndicators := expectedIndicators
    indicators_match := indicators_match
    nondegenerate := nondegenerate
    expectedFactors := expectedFactors
    candidates_eq :=
      candidatesOfMignottePrecision
        expectedIndicators selectedFactors expectedFactors hf_ne_zero hsize
        hselected hdivides hprimitive hsign hmonic hdegree mignotte_precision
        hproduct
    product_eq := product_eq }

/--
Build `ForwardRecoveryInputs` from the expected true-factor package plus
per-indicator Mignotte reconstruction facts.  This is the product-check
wrapper for the forward-recovery layer: callers identify the true factor list
once, and the final `Array.polyProduct expectedFactors = f` guard is extracted
by `productOfExpectedFactors`.
-/
def ofMignottePrecisionExpectedFactors
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (expectedIndicators : Array (Array Int))
    (indicators_match :
      equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false)
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (htrue : ExpectedTrueFactors f expectedIndicators expectedFactors)
    (hselected :
      ∀ i, i < expectedIndicators.size →
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            (expectedIndicators.getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hproduct :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)
              (Array.polyProduct (selectedFactors.getD i #[])))
            d.p d.k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCandidateProducts
    rows_pos trueSupports lattice_eq_indicators mignotte_precision
    expectedIndicators indicators_match nondegenerate
    selectedFactors expectedFactors hf_ne_zero htrue.size_eq
    hselected htrue.divides htrue.primitive htrue.leadingCoeff_nonneg
    htrue.monic htrue.positive_degree hproduct
    (productOfExpectedFactors htrue)

/--
Mignotte-precision `ForwardRecoveryInputs` constructor targeting the canonical
support-driven indicator array.  Mirrors
`ofMignottePrecisionCandidateProducts` but selects
`expectedIndicators := expectedIndicatorArrayOfSupports trueSupports`
internally and discharges `indicators_match` via
`equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports`,
removing the duplicated B7 indicator-array plumbing from callers.

The remaining fields (`mignotte_precision`, `nondegenerate`,
`selectedFactors`, `expectedFactors`, per-indicator Mignotte reconstruction
facts, and the final product check) pass through unchanged.  The candidate
facts are stated against the canonical indicator array
`expectedIndicatorArrayOfSupports trueSupports`, so callers consume the
support-driven indicator partition directly.
-/
noncomputable def ofMignottePrecisionCanonicalIndicators
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (hsize :
      expectedFactors.size = (expectedIndicatorArrayOfSupports trueSupports).size)
    (hselected :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hdivides :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        expectedFactors.getD i 0 ∣ f)
    (hprimitive :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.Primitive (expectedFactors.getD i 0))
    (hsign :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        0 ≤ Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0))
    (hmonic :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.DensePoly.Monic (expectedFactors.getD i 0))
    (hdegree :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        0 < (expectedFactors.getD i 0).degree?.getD 0)
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)
              (Array.polyProduct (selectedFactors.getD i #[])))
            d.p d.k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k)
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCandidateProducts
    rows_pos trueSupports lattice_eq_indicators mignotte_precision
    (expectedIndicatorArrayOfSupports trueSupports)
    (equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports
      rows_pos trueSupports lattice_eq_indicators)
    nondegenerate selectedFactors expectedFactors hf_ne_zero hsize
    hselected hdivides hprimitive hsign hmonic hdegree hproduct product_eq

/--
Mignotte-precision `ForwardRecoveryInputs` constructor from the expected
true-factor package, targeting the canonical support-driven indicator array.
This is the canonical-indicator wrapper corresponding to
`ofMignottePrecisionExpectedFactors`; callers identify the true factor list
once, and the final product check is extracted by `productOfExpectedFactors`.
-/
noncomputable def ofMignottePrecisionCanonicalIndicatorsExpectedFactors
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (htrue :
      ExpectedTrueFactors f
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hselected :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)
              (Array.polyProduct (selectedFactors.getD i #[])))
            d.p d.k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCanonicalIndicators
    rows_pos trueSupports lattice_eq_indicators mignotte_precision
    nondegenerate selectedFactors expectedFactors hf_ne_zero htrue.size_eq
    hselected htrue.divides htrue.primitive htrue.leadingCoeff_nonneg
    htrue.monic htrue.positive_degree hproduct
    (productOfExpectedFactors htrue)

/--
Mignotte-precision `ForwardRecoveryInputs` constructor specialised to the
public `factorFast` lift shape `d = henselLiftData f (precisionForCoeffBound
(factorFastPrecisionCap f) primeData.p) primeData`.  Drops the
`mignotte_precision` side condition (discharged via
`mignotte_precision_of_liftData_precisionForCoeffBound_factorFastPrecisionCap`
under `hp : 2 ≤ d.p` and the lift-data shape equation `hk`).  Mirrors
`ofCapSeparationCanonicalIndicatorsAtPrecisionForCoeffBound` for the Mignotte
chain that arrives with the `ExpectedTrueFactors` package directly.
-/
noncomputable def ofMignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (hp : 2 ≤ d.p)
    (hk : d.k =
      Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) d.p)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : f ≠ 0)
    (htrue :
      ExpectedTrueFactors f
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hselected :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)
              (Array.polyProduct (selectedFactors.getD i #[])))
            d.p d.k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCanonicalIndicatorsExpectedFactors
    rows_pos trueSupports lattice_eq_indicators
    (mignotte_precision_of_liftData_precisionForCoeffBound_factorFastPrecisionCap
      f d hp hk)
    nondegenerate selectedFactors expectedFactors hf_ne_zero htrue
    hselected hproduct

/--
Build `ForwardRecoveryInputs f d` from cap-level BHKS separation plus the
abstract B7/A2 obligations.

`lattice_eq_indicators` is supplied internally by
`BHKS.projectedRowsOfLiftData_eq_trueFactorIndicatorLattice_of_cap`, which
specialises issue #3034's executable-cap separation theorem to the
projected-row shape consumed by `ForwardRecoveryInputs`.  The remaining
fields (`mignotte_precision`, `expectedIndicators`, `indicators_match`,
`nondegenerate`, `expectedFactors`, per-indicator candidate facts, and the
final product check) pass through unchanged to `ofIndicatorCandidateFacts`.
-/
def ofCapSeparation
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le : Hex.factorFastPrecisionCap f ≤ d.k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfLiftData f d rows_pos localFactorIndex
          localFactorDegree H)
        trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (expectedIndicators : Array (Array Int))
    (indicators_match :
      equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false)
    (expectedFactors : Array Hex.ZPoly)
    (hsize : expectedFactors.size = expectedIndicators.size)
    (hcandidate :
      ∀ i, i < expectedIndicators.size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate? f d (expectedIndicators.getD i #[]) =
            some (expectedFactors.getD i 0, quotient))
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d :=
  ofIndicatorCandidateFacts
    rows_pos trueSupports
    (projectedRowsOfLiftData_eq_trueFactorIndicatorLattice_of_cap
      f d rows_pos localFactorIndex localFactorDegree H trueSupports
      hcap_le C hC_nonneg hC hcap)
    mignotte_precision
    expectedIndicators indicators_match nondegenerate
    expectedFactors hsize hcandidate product_eq

/--
Cap-separation form of `ForwardRecoveryInputs` targeting the canonical
support-driven indicator array.  Mirrors `ofCapSeparation` but selects
`expectedIndicators := expectedIndicatorArrayOfSupports trueSupports`
internally and discharges `indicators_match` via
`equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports`,
removing the duplicated B7 indicator-array plumbing from callers.

The remaining fields (`mignotte_precision`, `nondegenerate`,
`expectedFactors`, per-indicator candidate facts, and the final product
check) pass through unchanged.  The candidate facts are stated against the
canonical indicator array `expectedIndicatorArrayOfSupports trueSupports`,
so callers consume the support-driven indicator partition directly.
-/
noncomputable def ofCapSeparationCanonicalIndicators
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le : Hex.factorFastPrecisionCap f ≤ d.k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfLiftData f d rows_pos localFactorIndex
          localFactorDegree H)
        trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (expectedFactors : Array Hex.ZPoly)
    (hsize :
      expectedFactors.size = (expectedIndicatorArrayOfSupports trueSupports).size)
    (hcandidate :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate? f d
              ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
            some (expectedFactors.getD i 0, quotient))
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d :=
  have lattice_eq_indicators :
      BHKS.projectedRowSpanInt (projectedRowsOfLiftData f d rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports :=
    projectedRowsOfLiftData_eq_trueFactorIndicatorLattice_of_cap
      f d rows_pos localFactorIndex localFactorDegree H trueSupports
      hcap_le C hC_nonneg hC hcap
  ofCapSeparation rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcap mignotte_precision
    (expectedIndicatorArrayOfSupports trueSupports)
    (equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports
      rows_pos trueSupports lattice_eq_indicators)
    nondegenerate expectedFactors hsize hcandidate product_eq

/--
Cap-separation `ForwardRecoveryInputs` constructor specialised to the public
`factorFast` lift shape `d = henselLiftData f (precisionForCoeffBound
(factorFastPrecisionCap f) primeData.p) primeData`.  Drops both the explicit
`expectedIndicators`/`indicators_match` plumbing (canonical support-driven
indicator array) and the `mignotte_precision` side condition (discharged via
`mignotte_precision_of_liftData_precisionForCoeffBound_factorFastPrecisionCap`
under `hp : 2 ≤ d.p`).
-/
noncomputable def ofCapSeparationCanonicalIndicatorsAtPrecisionForCoeffBound
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le : Hex.factorFastPrecisionCap f ≤ d.k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfLiftData f d rows_pos localFactorIndex
          localFactorDegree H)
        trueSupports)
    (hp : 2 ≤ d.p)
    (hk : d.k =
      Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) d.p)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (expectedFactors : Array Hex.ZPoly)
    (hsize :
      expectedFactors.size = (expectedIndicatorArrayOfSupports trueSupports).size)
    (hcandidate :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate? f d
              ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
            some (expectedFactors.getD i 0, quotient))
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d :=
  ofCapSeparationCanonicalIndicators rows_pos trueSupports
    localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcap
    (mignotte_precision_of_liftData_precisionForCoeffBound_factorFastPrecisionCap
      f d hp hk)
    nondegenerate expectedFactors hsize hcandidate product_eq

/-- Promote a SPEC-input bundle to the immediate recovery hypotheses
consumed by `bhksRecover_eq_some_of_recovery`.  The promotion is a
field-by-field repackaging that uses `indicators_match` to substitute
`expectedIndicators` for the executable equivalence-class output in the
non-degenerate and candidate fields. -/
def toRecoveryHypotheses {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d) : RecoveryHypotheses f d where
  rows_pos := h.rows_pos
  nondegenerate := by
    have hindicators := h.indicators_match
    show
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d h.rows_pos)
          (equivalenceClassIndicatorsOfLiftData f d h.rows_pos) = false
    rw [hindicators]
    exact h.nondegenerate
  expectedFactors := h.expectedFactors
  candidates_eq := by
    have hindicators := h.indicators_match
    show
      Hex.bhksIndicatorCandidates? f d
        (equivalenceClassIndicatorsOfLiftData f d h.rows_pos) =
        some h.expectedFactors
    rw [hindicators]
    exact h.candidates_eq
  product_eq := h.product_eq

/-- The B7 indicator conclusion exposed directly from a
`ForwardRecoveryInputs` bundle. -/
theorem equivalenceClassIndicators_eq_expected {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d) :
    equivalenceClassIndicatorsOfLiftData f d h.rows_pos = h.expectedIndicators :=
  bhksEquivalenceClassIndicators_eq_of_recovery
    f d h.toEquivalenceClassRecoveryHypotheses

/-- Raw projected-row form of `equivalenceClassIndicators_eq_expected`. -/
theorem projectedRows_indicators_eq_expected {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d) :
    Hex.bhksEquivalenceClassIndicators
        (projectedRowsOfLiftData f d h.rows_pos) = h.expectedIndicators :=
  bhksEquivalenceClassIndicators_projectedRows_eq_of_recovery
    f d h.toEquivalenceClassRecoveryHypotheses

/-- The non-degeneracy guard after rewriting the expected indicators back to
the executable indicator array. -/
theorem nondegenerate_of_executableIndicators {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d) :
    Hex.bhksDegenerateIndicatorPartition
        (projectedRowsOfLiftData f d h.rows_pos)
        (equivalenceClassIndicatorsOfLiftData f d h.rows_pos) = false := by
  rw [h.equivalenceClassIndicators_eq_expected]
  exact h.nondegenerate

/-- The folded A2/exact-division candidate equality after rewriting the
expected indicators back to the executable indicator array. -/
theorem candidates_eq_of_executableIndicators {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d) :
    Hex.bhksIndicatorCandidates? f d
        (equivalenceClassIndicatorsOfLiftData f d h.rows_pos) =
      some h.expectedFactors := by
  rw [h.equivalenceClassIndicators_eq_expected]
  exact h.candidates_eq

end ForwardRecoveryInputs

/--
SPEC Group D forward-verification statement at one precision/recovery
call: under `L' = W` (deliverable 1) and Mignotte-precision plus the
residual abstract obligations B7 / A2, the executable
`Hex.bhksRecover? f d` returns `some <expected factors>`.

This is the headline theorem the issue asks for: the bridge from the
cap-specialised `L' = W` of #3034 (`mignotte_precision` is automatic at any
precision meeting `Hex.factorFastPrecisionCap f`) to the success branch of
the executable BHKS recovery pipeline.
-/
theorem bhksRecover_eq_some_of_forwardInputs
    (f : Hex.ZPoly) (d : Hex.LiftData) (h : ForwardRecoveryInputs f d) :
    Hex.bhksRecover? f d = some h.expectedFactors :=
  bhksRecover_eq_some_of_recovery f d h.toRecoveryHypotheses

/-- Corollary form: under the SPEC forward-verification inputs,
`Hex.bhksRecover? f d` is `some _`. -/
theorem bhksRecover_isSome_of_forwardInputs
    (f : Hex.ZPoly) (d : Hex.LiftData) (h : ForwardRecoveryInputs f d) :
    (Hex.bhksRecover? f d).isSome :=
  bhksRecover_isSome_of_recovery f d h.toRecoveryHypotheses

/--
Cap-level specialisation: compose `ForwardRecoveryInputs.ofCapSeparation`
with `bhksRecover_eq_some_of_forwardInputs` at a fixed `LiftData`.  Under
cap-level BHKS separation and the residual B7/A2 obligations,
`Hex.bhksRecover? f d` returns `some expectedFactors`.
-/
theorem bhksRecover_eq_some_of_capSeparation
    (f : Hex.ZPoly) (d : Hex.LiftData)
    (rows_pos : HasPositiveDimension f d)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d rows_pos).factorCount)))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le : Hex.factorFastPrecisionCap f ≤ d.k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfLiftData f d rows_pos localFactorIndex
          localFactorDegree H)
        trueSupports)
    (mignotte_precision :
      2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k)
    (expectedIndicators : Array (Array Int))
    (indicators_match :
      equivalenceClassIndicatorsOfLiftData f d rows_pos = expectedIndicators)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData f d rows_pos) expectedIndicators = false)
    (expectedFactors : Array Hex.ZPoly)
    (hsize : expectedFactors.size = expectedIndicators.size)
    (hcandidate :
      ∀ i, i < expectedIndicators.size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate? f d (expectedIndicators.getD i #[]) =
            some (expectedFactors.getD i 0, quotient))
    (product_eq : Array.polyProduct expectedFactors = f) :
    Hex.bhksRecover? f d = some expectedFactors :=
  bhksRecover_eq_some_of_forwardInputs f d
    (ForwardRecoveryInputs.ofCapSeparation rows_pos trueSupports
      localFactorIndex localFactorDegree H hcap_le C hC_nonneg hC hcap
      mignotte_precision expectedIndicators indicators_match nondegenerate
      expectedFactors hsize hcandidate product_eq)

/--
Compose the Mathlib-side forward-recovery inputs with the executable scheduled
fast-path bridge: if a scheduled lift for the normalized square-free core
satisfies the forward-verification inputs, then the public `Hex.factorFast`
entry point succeeds.
-/
theorem factorFast_ne_none_of_forwardInputs_on_schedule
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    {target : Nat}
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hnormalized :
      primeData = Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)
    (hinputs :
      ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.henselLiftData
          (Hex.normalizeForFactor f).squareFreeCore target primeData))
    (hmem :
      let a := Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) primeData.p
      target ∈
        Hex.henselPrecisionSchedule a
          (Hex.initialHenselPrecision a)
          (Hex.ZPoly.quadraticDoublingSteps a + 2)) :
    Hex.factorFast f ≠ none := by
  have hrecover :
      Hex.bhksRecover? (Hex.normalizeForFactor f).squareFreeCore
          (Hex.henselLiftData
            (Hex.normalizeForFactor f).squareFreeCore target primeData) =
        some hinputs.expectedFactors :=
    bhksRecover_eq_some_of_forwardInputs
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.henselLiftData
        (Hex.normalizeForFactor f).squareFreeCore target primeData)
      hinputs
  exact
    Hex.factorFast_ne_none_of_core_recovery_on_schedule
      f primeData hB_pos hnormalized hmem hrecover

/--
Canonical scheduled-precision specialisation of
`factorFast_ne_none_of_forwardInputs_on_schedule`: if the SPEC Group D
forward-recovery inputs hold at the executable terminal precision
`a = precisionForCoeffBound (factorFastPrecisionCap f) primeData.p`, the
public `Hex.factorFast` entry point succeeds.  The doubling-schedule
membership obligation is discharged here using
`Hex.cap_mem_henselPrecisionSchedule`, so later HO-4 work only needs to
provide the `ForwardRecoveryInputs` bundle plus the surrounding BHKS
semantic hypotheses.
-/
theorem factorFast_ne_none_of_forwardInputs_at_cap
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hnormalized :
      primeData = Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)
    (hinputs :
      ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.henselLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.precisionForCoeffBound
            (Hex.factorFastPrecisionCap f) primeData.p)
          primeData)) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_forwardInputs_on_schedule
    f primeData hB_pos hnormalized hinputs
    (Hex.cap_mem_henselPrecisionSchedule _)

/-- The Hensel-lift data produced by the public `factorFast` pipeline for
`f` at the executable cap precision: a lift of the normalized square-free
core of `f` to precision `precisionForCoeffBound (factorFastPrecisionCap f)
primeData.p` over `primeData`. Local abbreviation used inside the HO-4 leaf
capstones to factor out the repeated nested lift-data expression. -/
private abbrev factorFastCapLiftData
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData) : Hex.LiftData :=
  Hex.henselLiftData
    (Hex.normalizeForFactor f).squareFreeCore
    (Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) primeData.p)
    primeData

/--
HO-4 leaf capstone: compose
`ForwardRecoveryInputs.ofCapSeparationCanonicalIndicatorsAtPrecisionForCoeffBound`
with `factorFast_ne_none_of_forwardInputs_at_cap`.

Given cap-level BHKS separation on the normalized square-free core lift, B7
non-degeneracy of the canonical support-driven indicator partition, and the
A2/exact-division candidate facts (a candidate-product witness per indicator,
plus the final product check), the public `Hex.factorFast f` returns `some _`.

This is the natural HO-4 leaf entry point for callers that arrive with
executable cap separation: the two-step
`ForwardRecoveryInputs` construction and the `factorFast`-success forward
inference fold into a single application.  See
`ofCapSeparationCanonicalIndicatorsAtPrecisionForCoeffBound` for the producer
side and `factorFast_ne_none_of_forwardInputs_at_cap` for the consumer side.
The Mignotte-side parallel entry point is
`factorFast_ne_none_of_mignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound`.
-/
theorem factorFast_ne_none_of_capSeparationCanonicalIndicatorsAtPrecisionForCoeffBound
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hnormalized :
      primeData = Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)
    (hp : 2 ≤ (factorFastCapLiftData f primeData).p)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (expectedFactors : Array Hex.ZPoly)
    (hsize : expectedFactors.size =
      (expectedIndicatorArrayOfSupports trueSupports).size)
    (hcandidate :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        ∃ quotient,
          Hex.bhksIndicatorCandidate?
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData)
              ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
            some (expectedFactors.getD i 0, quotient))
    (product_eq :
      Array.polyProduct expectedFactors =
        (Hex.normalizeForFactor f).squareFreeCore) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_forwardInputs_at_cap f primeData hB_pos hnormalized
    (ForwardRecoveryInputs.ofCapSeparationCanonicalIndicatorsAtPrecisionForCoeffBound
      rows_pos trueSupports localFactorIndex localFactorDegree H
      hcap_le C hC_nonneg hC hcap hp hk nondegenerate
      expectedFactors hsize hcandidate product_eq)

/--
HO-4 leaf capstone: compose
`ForwardRecoveryInputs.ofMignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound`
with `factorFast_ne_none_of_forwardInputs_at_cap`.

Given the B7 canonical lattice identification on the normalized square-free
core lift, B7 non-degeneracy of the canonical support-driven indicator
partition, and the A2/exact-division Mignotte reconstruction facts (an
indicator-selected factor list per indicator, the `ExpectedTrueFactors`
package, and the per-indicator scaled-product reduction check), the public
`Hex.factorFast f` returns `some _`.

This is the Mignotte-side HO-4 leaf entry point parallel to
`factorFast_ne_none_of_capSeparationCanonicalIndicatorsAtPrecisionForCoeffBound`:
the two-step `ForwardRecoveryInputs` construction and the `factorFast`-success
forward inference fold into a single application.  See
`ofMignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound`
for the producer side and `factorFast_ne_none_of_forwardInputs_at_cap` for the
consumer side.
-/
theorem factorFast_ne_none_of_mignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (lattice_eq_indicators :
      BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos) =
        BHKS.trueFactorIndicatorLattice trueSupports)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hnormalized :
      primeData = Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)
    (hp : 2 ≤ (factorFastCapLiftData f primeData).p)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (nondegenerate :
      Hex.bhksDegenerateIndicatorPartition
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos)
          (expectedIndicatorArrayOfSupports trueSupports) = false)
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (htrue :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hselected :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.bhksIndicatorSelectedFactors
            (factorFastCapLiftData f primeData).liftedFactors
            ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
          some (selectedFactors.getD i #[]))
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct (selectedFactors.getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_forwardInputs_at_cap f primeData hB_pos hnormalized
    (ForwardRecoveryInputs.ofMignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound
      rows_pos trueSupports lattice_eq_indicators hp hk nondegenerate
      selectedFactors expectedFactors hf_ne_zero htrue hselected hproduct)

end BHKS

end HexBerlekampZassenhausMathlib
