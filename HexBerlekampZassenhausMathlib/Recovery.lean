import HexBerlekampZassenhausMathlib.Lattice
import HexBerlekampZassenhausMathlib.ColumnSignature
import HexBerlekampZassenhausMathlib.SignatureClasses
import HexBerlekampZassenhausMathlib.TerminationBound
import HexBerlekampZassenhausMathlib.BadVectorAuxiliary

/-!
Forward-verification of BHKS recovery at fixed precision.

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

The theorem statements are intentionally scoped to forward recovery and the
prime-search-safe fast branch.  Because the executable prime search is finite,
the final public success theorem for the current `factorFast` API must carry a
`choosePrimeData? = some primeData` witness; the hypothesis-free termination
target belongs to a different API with an unbounded prime chooser.
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
Specialise the `ProjectedBadVectorSetupBridge` constructor to the
`badVectorWitnessOfLiftData` witness shape.  Forgetting the heavyweight
`BadVectorBridgeData` package to the compact cap-separation surface combines
the four field projections — `auxiliary_eq`/`auxiliaryCorrections`,
`localFactorDegree_pos_of_bridge_data`,
`coprime_input_aux_over_rat_of_bridge_data`, and
`resultant_divisible_by_p_pow_of_bridge_data` — into one assembled bridge for
use by `capSeparationOfBridgeData`.
-/
def bridgeOfLiftData
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (hrows : HasPositiveDimension f d)
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d hrows).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
        trueSupports) :
    ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge
        (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
        trueSupports :=
  bridge.toProjectedBadVectorSetupBridge

/--
Cap-separation hypotheses for the `badVectorWitnessOfLiftData` witness,
assembled from the project-level `BadVectorBridgeData` package plus the cut
and resultant-bound side conditions that remain #5204 / #5216 territory.

This is the single consumer wrapper that ties the BHKS D1 bridge surface
together: the `BadVectorBridgeData` carries the four bridge fields, and the
`hcut`/`hp`/`hlt` arguments supply the cap structure and the analytic
strict inequality.
-/
def capSeparationOfBridgeData
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (hrows : HasPositiveDimension f d)
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData f d hrows).factorCount)))
    (hcut :
      CutProjectionHypotheses (projectedRowsOfLiftData f d hrows) trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
        trueSupports)
    (hp : 0 < d.p)
    (hlt :
      (HexPolyZMathlib.l2norm
            (badVectorWitnessOfLiftData
              f d hrows localFactorIndex localFactorDegree H).inputPolynomial) ^
          (badVectorWitnessOfLiftData
              f d hrows localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm
            (badVectorWitnessOfLiftData
              f d hrows localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^
          (badVectorWitnessOfLiftData
              f d hrows localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      (d.p ^ (d.k * localFactorDegree) : ℝ)) :
    ExecutableCapSeparationHypotheses
      (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
      trueSupports :=
  ExecutableCapSeparationHypotheses.ofProjectedBadVectorSetupBridge
    (badVectorWitnessOfLiftData f d hrows localFactorIndex localFactorDegree H)
    trueSupports hcut
    (bridgeOfLiftData hrows localFactorIndex localFactorDegree H trueSupports bridge)
    hp hlt

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

/-- Lift-data form of the B7 implication: when the executable projected row span is
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
list. This is the BHKS Lemma 3.3 / B7 implication from `L' = W` to the
executable indicator surface. -/
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
separation hypotheses is left to later follow-up work; this record packages
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
          (Hex.bhksProjectedRows (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) = false :=
    h.nondegenerate
  have hcand :
      Hex.bhksIndicatorCandidates? f d
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors) hrows)) =
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

This is the Mathlib-side wrapper around the Mathlib-free fold helper
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
Single-indicator A2 reconstruction from the monic-transform coordinate. The
selected lifted factors are supplied explicitly by `hselected`, while
`hdilated` is the B7/A2-facing reconstruction fact: after centered lifting in
the monic-transform coordinate and dilating back by `lc(f)`, the result is the
expected integer factor.
-/
theorem bhksIndicatorCandidate?_eq_some_of_dilatedCenteredLift
    (f : Hex.ZPoly) (d : Hex.LiftData) (indicator : Array Int)
    (selected : Array Hex.ZPoly) (expectedFactor : Hex.ZPoly)
    (hselected :
      Hex.bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hdvd : expectedFactor ∣ f)
    (hexpected_prim : Hex.ZPoly.Primitive expectedFactor)
    (hexpected_sign : 0 ≤ Hex.DensePoly.leadingCoeff expectedFactor)
    (hexpected_pos_lc : 0 < Hex.DensePoly.leadingCoeff expectedFactor)
    (hexpected_degree : 0 < expectedFactor.degree?.getD 0)
    (hdilated :
      Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
          (Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k)) =
        expectedFactor) :
    ∃ quotient,
      Hex.bhksIndicatorCandidate? f d indicator =
        some (expectedFactor, quotient) :=
  Hex.bhksIndicatorCandidate?_eq_some_of_dilatedCenteredLift
    f d indicator selected expectedFactor hselected hdvd
    hexpected_prim hexpected_sign hexpected_pos_lc hexpected_degree hdilated

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
content and are the natural follow-up tasks for later work.
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

/-- Auxiliary: a `getD` lookup at an in-range index is a member of `toList`. -/
private theorem getD_mem_toList_of_lt_size
    {α : Type} (xs : Array α) (default : α) (i : Nat) (hi : i < xs.size) :
    xs.getD i default ∈ xs.toList := by
  have hi_list : i < xs.toList.length := by simpa using hi
  have hgetD_eq : xs.getD i default = xs.toList[i]'hi_list := by
    simp [Array.getD, Array.getElem_toList, hi]
  rw [hgetD_eq]
  exact List.getElem_mem hi_list

/-- Per-index variant of `bhksIndicatorCandidates?_dvd`: any indexed factor in
the candidate array divides the recovery target. -/
theorem bhksIndicatorCandidates?_getD_dvd
    {f : Hex.ZPoly} {d : Hex.LiftData}
    {expectedIndicators : Array (Array Int)}
    {expectedFactors : Array Hex.ZPoly}
    (h : Hex.bhksIndicatorCandidates? f d expectedIndicators = some expectedFactors)
    (i : Nat) (hi : i < expectedIndicators.size) :
    expectedFactors.getD i 0 ∣ f := by
  have hsize := Hex.bhksIndicatorCandidates?_size_eq h
  have hi_cand : i < expectedFactors.size := by rw [hsize]; exact hi
  have hmem :=
    getD_mem_toList_of_lt_size expectedFactors (0 : Hex.ZPoly) i hi_cand
  exact Hex.bhksIndicatorCandidates?_dvd h _ hmem

/-- Per-index variant of `bhksIndicatorCandidates?_primitive`. -/
theorem bhksIndicatorCandidates?_getD_primitive
    {f : Hex.ZPoly} {d : Hex.LiftData}
    {expectedIndicators : Array (Array Int)}
    {expectedFactors : Array Hex.ZPoly}
    (h : Hex.bhksIndicatorCandidates? f d expectedIndicators = some expectedFactors)
    (i : Nat) (hi : i < expectedIndicators.size) :
    Hex.ZPoly.Primitive (expectedFactors.getD i 0) := by
  have hsize := Hex.bhksIndicatorCandidates?_size_eq h
  have hi_cand : i < expectedFactors.size := by rw [hsize]; exact hi
  have hmem :=
    getD_mem_toList_of_lt_size expectedFactors (0 : Hex.ZPoly) i hi_cand
  exact Hex.bhksIndicatorCandidates?_primitive h _ hmem

/-- Per-index variant of `bhksIndicatorCandidates?_leadingCoeff_nonneg`. -/
theorem bhksIndicatorCandidates?_getD_leadingCoeff_nonneg
    {f : Hex.ZPoly} {d : Hex.LiftData}
    {expectedIndicators : Array (Array Int)}
    {expectedFactors : Array Hex.ZPoly}
    (h : Hex.bhksIndicatorCandidates? f d expectedIndicators = some expectedFactors)
    (i : Nat) (hi : i < expectedIndicators.size) :
    0 ≤ Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0) := by
  have hsize := Hex.bhksIndicatorCandidates?_size_eq h
  have hi_cand : i < expectedFactors.size := by rw [hsize]; exact hi
  have hmem :=
    getD_mem_toList_of_lt_size expectedFactors (0 : Hex.ZPoly) i hi_cand
  exact Hex.bhksIndicatorCandidates?_leadingCoeff_nonneg h _ hmem

/-- Per-index variant of `bhksIndicatorCandidates?_positive_degree`. -/
theorem bhksIndicatorCandidates?_getD_positive_degree
    {f : Hex.ZPoly} {d : Hex.LiftData}
    {expectedIndicators : Array (Array Int)}
    {expectedFactors : Array Hex.ZPoly}
    (h : Hex.bhksIndicatorCandidates? f d expectedIndicators = some expectedFactors)
    (i : Nat) (hi : i < expectedIndicators.size) :
    0 < (expectedFactors.getD i 0).degree?.getD 0 := by
  have hsize := Hex.bhksIndicatorCandidates?_size_eq h
  have hi_cand : i < expectedFactors.size := by rw [hsize]; exact hi
  have hmem :=
    getD_mem_toList_of_lt_size expectedFactors (0 : Hex.ZPoly) i hi_cand
  exact Hex.bhksIndicatorCandidates?_positive_degree h _ hmem

/-- Monic transfer: a primitive divisor of a monic integer polynomial with
nonnegative leading coefficient is itself monic.  Over `ℤ`, the leading
coefficients of a `g ∣ f` factorisation multiply to `1`, so `0 ≤
leadingCoeff g` forces `leadingCoeff g = 1`. -/
private theorem monic_of_dvd_monic_of_leadingCoeff_nonneg
    {f g : Hex.ZPoly}
    (hf_monic : Hex.DensePoly.Monic f)
    (hg_dvd : g ∣ f)
    (hg_sign : 0 ≤ Hex.DensePoly.leadingCoeff g) :
    Hex.DensePoly.Monic g := by
  have hf_lead_one : Hex.DensePoly.leadingCoeff f = 1 := hf_monic
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_lead_one
    simp at hf_lead_one
  rcases hg_dvd with ⟨q, hf_eq⟩
  have hg_ne : g ≠ 0 := by
    intro hzero
    apply hf_ne
    rw [hf_eq, hzero, Hex.DensePoly.zero_mul]
  have hq_ne : q ≠ 0 := by
    intro hzero
    apply hf_ne
    rw [hf_eq, hzero, Hex.DensePoly.mul_comm_poly]
    exact Hex.DensePoly.zero_mul g
  have hlead_mul :
      Hex.DensePoly.leadingCoeff (g * q) =
        Hex.DensePoly.leadingCoeff g * Hex.DensePoly.leadingCoeff q :=
    Hex.ZPoly.leadingCoeff_mul_of_nonzero g q hg_ne hq_ne
  have hlead_one :
      Hex.DensePoly.leadingCoeff g * Hex.DensePoly.leadingCoeff q = 1 := by
    rw [← hlead_mul, ← hf_eq, hf_lead_one]
  exact Int.eq_one_of_mul_eq_one_right hg_sign hlead_one

/-- Per-index monic transfer for `bhksIndicatorCandidates?`: when the
recovery target is monic, every candidate factor is monic. -/
theorem bhksIndicatorCandidates?_getD_monic_of_monic
    {f : Hex.ZPoly} {d : Hex.LiftData}
    {expectedIndicators : Array (Array Int)}
    {expectedFactors : Array Hex.ZPoly}
    (hmonic : Hex.DensePoly.Monic f)
    (h : Hex.bhksIndicatorCandidates? f d expectedIndicators = some expectedFactors)
    (i : Nat) (hi : i < expectedIndicators.size) :
    Hex.DensePoly.Monic (expectedFactors.getD i 0) :=
  monic_of_dvd_monic_of_leadingCoeff_nonneg
    hmonic
    (bhksIndicatorCandidates?_getD_dvd h i hi)
    (bhksIndicatorCandidates?_getD_leadingCoeff_nonneg h i hi)

/-- The `ExpectedTrueFactors` constructor for the BHKS recovery-tail path.
From a `ForwardRecoveryInputs` package (which carries the executable
`bhksIndicatorCandidates? = some expectedFactors` witness and the product
identity) and a monic recovery target, package the per-factor structural
facts that downstream consumers (e.g. the recovery-tail
`CanonicalRecoveryTailInputs.ofCanonicalSupportRepresentations` constructor)
require. -/
theorem expectedTrueFactors_of_monic
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (hmonic : Hex.DensePoly.Monic f)
    (h : ForwardRecoveryInputs f d) :
    ExpectedTrueFactors f h.expectedIndicators h.expectedFactors where
  size_eq :=
    Hex.bhksIndicatorCandidates?_size_eq h.candidates_eq
  divides i hi :=
    bhksIndicatorCandidates?_getD_dvd h.candidates_eq i hi
  primitive i hi :=
    bhksIndicatorCandidates?_getD_primitive h.candidates_eq i hi
  leadingCoeff_nonneg i hi :=
    bhksIndicatorCandidates?_getD_leadingCoeff_nonneg h.candidates_eq i hi
  monic i hi :=
    bhksIndicatorCandidates?_getD_monic_of_monic hmonic h.candidates_eq i hi
  positive_degree i hi :=
    bhksIndicatorCandidates?_getD_positive_degree h.candidates_eq i hi
  product_eq := h.product_eq

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

/-- The canonical support-driven indicator array is nonempty whenever the
support partition has at least one class. -/
theorem expectedIndicatorArrayOfSupports_nonempty {r : Nat}
    (trueSupports : Set (Set (Fin r)))
    (hclasses :
      (supportPartitionByMinColumn trueSupports).length ≠ 0) :
    (expectedIndicatorArrayOfSupports trueSupports).isEmpty = false := by
  rw [Bool.eq_false_iff]
  intro hempty
  apply hclasses
  have hsize :
      (expectedIndicatorArrayOfSupports trueSupports).size = 0 := by
    rw [Array.size_eq_zero_iff]
    exact Array.isEmpty_iff.mp hempty
  simpa [expectedIndicatorArrayOfSupports] using hsize

/-- The canonical support-driven indicator array is not the degenerate
single all-ones partition whenever the support partition is not a singleton. -/
theorem expectedIndicatorArrayOfSupports_not_single_all_ones {r : Nat}
    (trueSupports : Set (Set (Fin r)))
    (hclasses :
      (supportPartitionByMinColumn trueSupports).length ≠ 1) :
    ((expectedIndicatorArrayOfSupports trueSupports).size == 1 &&
        Hex.bhksIndicatorAllOnes r
          ((expectedIndicatorArrayOfSupports trueSupports).getD 0 #[])) = false := by
  have hsize :
      (expectedIndicatorArrayOfSupports trueSupports).size ≠ 1 := by
    intro h
    apply hclasses
    simpa [expectedIndicatorArrayOfSupports] using h
  simp [hsize]

/-- Direct non-degeneracy wrapper for the canonical support-driven indicator
array, independent of the lift-data recovery bundle. -/
theorem canonicalSupportIndicators_nondegenerate
    (L : Hex.BhksProjectedRows)
    (trueSupports : Set (Set (Fin L.factorCount)))
    (hprojected_nonempty : L.projectedRows.isEmpty = false)
    (hclasses_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length) :
    Hex.bhksDegenerateIndicatorPartition
      L (expectedIndicatorArrayOfSupports trueSupports) = false := by
  have hclasses_nonempty :
      (supportPartitionByMinColumn trueSupports).length ≠ 0 := by
    omega
  have hclasses_not_single :
      (supportPartitionByMinColumn trueSupports).length ≠ 1 := by
    omega
  unfold Hex.bhksDegenerateIndicatorPartition
  rw [expectedIndicatorArrayOfSupports_nonempty trueSupports hclasses_nonempty,
    hprojected_nonempty]
  simp only [Bool.false_or]
  exact expectedIndicatorArrayOfSupports_not_single_all_ones
    trueSupports hclasses_not_single

/-- The selected lifted factors attached to an explicit support-class member
list, using the canonical BHKS selector array. -/
def selectedFactorsOfMembers
    (liftedFactors : Array Hex.ZPoly) (members : List Nat) : Array Hex.ZPoly :=
  Hex.bhksIndicatorSelectedFactorsArray liftedFactors
    (classIndicatorArray liftedFactors.size members)

/-- Proof-side lifted-factor subset selected by a support-class member list. -/
def liftedFactorSubsetOfMembers
    (d : Hex.LiftData) (members : List Nat) : LiftedFactorSubset d :=
  Finset.univ.filter fun i : LiftedFactorIndex d => i.val ∈ members

/-- Membership in `liftedFactorSubsetOfMembers` is exactly membership of the
underlying array index in the support-class member list. -/
theorem mem_liftedFactorSubsetOfMembers
    (d : Hex.LiftData) (members : List Nat) (i : LiftedFactorIndex d) :
    i ∈ liftedFactorSubsetOfMembers d members ↔ i.val ∈ members := by
  simp [liftedFactorSubsetOfMembers]

/-- General `filterMap`/`filter`-`map` equivalence used to align executable
indicator selection with proof-side lifted-factor subsets. -/
private theorem List.filterMap_if_eq_map_filter
    {α β : Type _} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x with
      | true => simp [hp, ih]
      | false => simp [hp, ih]

/-- A class indicator has one entry for each lifted factor. -/
theorem classIndicatorArray_size (r : Nat) (members : List Nat) :
    (classIndicatorArray r members).size = r := by
  simp [classIndicatorArray]

/-- Class indicators are always `0/1` rows. -/
theorem classIndicatorArray_bits (r : Nat) (members : List Nat) :
    ∀ i, i < (classIndicatorArray r members).size →
      (classIndicatorArray r members).getD i 0 = 0 ∨
        (classIndicatorArray r members).getD i 0 = 1 := by
  intro i hi
  have hi_r : i < r := by
    simpa [classIndicatorArray] using hi
  by_cases hmem : i ∈ members
  · right
    simp [classIndicatorArray, hi_r, hmem]
  · left
    simp [classIndicatorArray, hi_r, hmem]

/-- Members of a class are selected by its canonical indicator row. -/
theorem classIndicatorArray_getD_eq_one_of_mem
    {r : Nat} {members : List Nat} {j : Nat}
    (hj : j < r) (hmem : j ∈ members) :
    (classIndicatorArray r members).getD j 0 = 1 := by
  simp [classIndicatorArray, hj, hmem]

/-- The executable BHKS selector for a member list is the order-preserving
filter of the lifted-factor array by those members. -/
private theorem selectedFactorsOfMembers_toList
    (liftedFactors : Array Hex.ZPoly) (members : List Nat) :
    (selectedFactorsOfMembers liftedFactors members).toList =
      ((List.range liftedFactors.size).filter fun i => i ∈ members).map
        (fun i => liftedFactors.getD i 0) := by
  unfold selectedFactorsOfMembers Hex.bhksIndicatorSelectedFactorsArray
  let indicator := classIndicatorArray liftedFactors.size members
  let step := fun (selected : Array Hex.ZPoly) (i : Nat) =>
    if indicator.getD i 0 == 1 then
      selected.push (liftedFactors.getD i 0)
    else
      selected
  have hfold :
      ∀ (indices : List Nat) (selected : Array Hex.ZPoly),
        (indices.foldl step selected).toList =
          selected.toList ++
            (indices.filter fun i => indicator.getD i 0 == 1).map
              (fun i => liftedFactors.getD i 0) := by
    intro indices
    induction indices with
    | nil =>
        intro selected
        simp
    | cons i rest ih =>
        intro selected
        by_cases hone : indicator.getD i 0 == 1
        · rw [List.foldl_cons]
          simp only [step, hone, if_true]
          rw [ih (selected.push (liftedFactors.getD i 0))]
          have hfilter :
              (List.filter (fun i => indicator.getD i 0 == 1) (i :: rest)) =
                i :: List.filter (fun i => indicator.getD i 0 == 1) rest := by
            simp only [List.filter]
            rw [hone]
          rw [hfilter]
          simp [List.append_assoc]
        · rw [List.foldl_cons]
          have hfalse : (indicator.getD i 0 == 1) = false := by
            cases h : indicator.getD i 0 == 1 <;> simp_all
          simp only [step, hfalse]
          simp only [Bool.false_eq_true, if_false]
          rw [ih selected]
          have hfilter :
              (List.filter (fun i => indicator.getD i 0 == 1) (i :: rest)) =
                List.filter (fun i => indicator.getD i 0 == 1) rest := by
            simp only [List.filter]
            rw [hfalse]
          rw [hfilter]
  change ((List.range indicator.size).foldl step #[]).toList =
    ((List.range liftedFactors.size).filter fun i => i ∈ members).map
      (fun i => liftedFactors.getD i 0)
  rw [hfold]
  simp only [List.nil_append]
  have hfilter :
      (List.range (classIndicatorArray liftedFactors.size members).size).filter
          (fun i => indicator.getD i 0 == 1) =
        (List.range liftedFactors.size).filter fun i => i ∈ members := by
    rw [classIndicatorArray_size]
    apply List.filter_congr
    intro i hi
    have hi_size : i < liftedFactors.size := List.mem_range.mp hi
    have hget :
        indicator.getD i 0 = if i ∈ members then 1 else 0 := by
      simp [indicator, classIndicatorArray, hi_size]
    by_cases hmem : i ∈ members
    · simp [hget, hmem]
    · simp [hget, hmem]
  rw [hfilter]

/-- The proof-side selected lifted-factor list for member-induced subsets is
the same order-preserving filter of the lifted-factor array, indexed by
`Fin`. -/
private theorem liftedSubsetSelectedList_liftedFactorSubsetOfMembers
    (d : Hex.LiftData) (members : List Nat) :
    liftedSubsetSelectedList d (liftedFactorSubsetOfMembers d members) =
      ((List.finRange d.liftedFactors.size).filter
          fun i : Fin d.liftedFactors.size => i.val ∈ members).map
        (liftedFactor d) := by
  unfold liftedSubsetSelectedList liftedSubsetMask
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  rw [List.filterMap_if_eq_map_filter]
  simp [liftedFactor, liftedFactorSubsetOfMembers]

/-- The executable selector product for a class-member list equals the
proof-side lifted-factor subset product induced by that same member list. -/
theorem selectedFactorsOfMembers_polyProduct
    (d : Hex.LiftData) (members : List Nat) :
    Array.polyProduct (selectedFactorsOfMembers d.liftedFactors members) =
      liftedFactorProduct d (liftedFactorSubsetOfMembers d members) := by
  rw [← polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [polyProduct_toPolynomial, polyProduct_toPolynomial]
  rw [selectedFactorsOfMembers_toList,
    liftedSubsetSelectedList_liftedFactorSubsetOfMembers]
  have hmap :
      ((List.finRange d.liftedFactors.size).filter
          fun i : Fin d.liftedFactors.size => i.val ∈ members).map
        (fun i => i.val) =
        (List.range d.liftedFactors.size).filter fun i => i ∈ members := by
    have hcoe_inj :
        Function.Injective (fun i : Fin d.liftedFactors.size => i.val) := by
      intro a b h
      exact Fin.ext h
    rw [List.map_filter
        (f := fun i : Fin d.liftedFactors.size => i.val)
        (p := fun i : Fin d.liftedFactors.size => i.val ∈ members)
        hcoe_inj
        (List.finRange d.liftedFactors.size)]
    rw [List.map_coe_finRange_eq_range]
    apply List.filter_congr
    intro i hi
    have hi_size : i < d.liftedFactors.size := List.mem_range.mp hi
    by_cases hmem : i ∈ members
    · rw [show decide (i ∈ members) = true from decide_eq_true hmem]
      apply decide_eq_true
      exact ⟨⟨i, hi_size⟩, by simp [hmem], rfl⟩
    · rw [show decide (i ∈ members) = false from decide_eq_false hmem]
      apply decide_eq_false
      intro hx
      rcases hx with ⟨x, hxmem, hxi⟩
      exact hmem (by
        have hxmem' : x.val ∈ members := of_decide_eq_true hxmem
        simpa [hxi] using hxmem')
  rw [← hmap]
  apply congrArg List.prod
  rw [List.toList_toArray]
  rw [List.map_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  simp [Function.comp_def, liftedFactor, Array.getD]

/--
A successful BHKS indicator candidate represents the integer factor selected by
the corresponding member-induced lifted-factor subset, once the core and lifted
factors are monic.
-/
theorem bhksIndicatorCandidate?_representsIntegerFactorAtLift
    {core : Hex.ZPoly} {d : Hex.LiftData} {indicator : Array Int}
    {candidate quotient : Hex.ZPoly} {members : List Nat}
    (h : Hex.bhksIndicatorCandidate? core d indicator = some (candidate, quotient))
    (hselected :
      Hex.bhksIndicatorSelectedFactors d.liftedFactors indicator =
        some (selectedFactorsOfMembers d.liftedFactors members))
    (hcore_monic : Hex.DensePoly.Monic core)
    (hliftedFactor_monic :
      ∀ i, i < d.liftedFactors.size →
        Hex.DensePoly.Monic (d.liftedFactors.getD i 0))
    (hp_two_lt : 2 < d.p ^ d.k) :
      RepresentsIntegerFactorAtLift core d candidate
        (liftedFactorSubsetOfMembers d members) := by
  unfold RepresentsIntegerFactorAtLift scaledLiftedFactorProduct
  rw [← selectedFactorsOfMembers_polyProduct d members]
  exact bhksIndicatorCandidate?_reduceModPow_eq_of_monic h hselected hcore_monic
    (by
      intro factor hfactor
      rw [selectedFactorsOfMembers_toList] at hfactor
      rcases List.mem_map.mp hfactor with ⟨i, hi, rfl⟩
      exact hliftedFactor_monic i (List.mem_range.mp (List.mem_filter.mp hi).1))
    (Nat.le_of_lt hp_two_lt)

/--
The BHKS selected-factor operation succeeds on a nonempty class indicator whose
members all lie inside the lifted-factor array.
-/
theorem bhksIndicatorSelectedFactors_classIndicatorArray
    (liftedFactors : Array Hex.ZPoly) (members : List Nat)
    (hnonempty : ∃ j, j ∈ members)
    (hbounds : ∀ j, j ∈ members → j < liftedFactors.size) :
    Hex.bhksIndicatorSelectedFactors liftedFactors
        (classIndicatorArray liftedFactors.size members) =
      some (selectedFactorsOfMembers liftedFactors members) := by
  unfold selectedFactorsOfMembers
  apply Hex.bhksIndicatorSelectedFactors_eq_some_selectedArray_of_getD
  · exact classIndicatorArray_size liftedFactors.size members
  · exact classIndicatorArray_bits liftedFactors.size members
  · rcases hnonempty with ⟨j, hj_mem⟩
    exact ⟨j, by simpa [classIndicatorArray_size] using hbounds j hj_mem,
      classIndicatorArray_getD_eq_one_of_mem (hbounds j hj_mem) hj_mem⟩

/-- Canonical selected-factor arrays corresponding to
`expectedIndicatorArrayOfSupports`. -/
noncomputable def selectedFactorArraysOfSupports
    (liftedFactors : Array Hex.ZPoly)
    {r : Nat} (trueSupports : Set (Set (Fin r))) : Array (Array Hex.ZPoly) :=
  ((supportPartitionByMinColumn trueSupports).map
    (fun members => selectedFactorsOfMembers liftedFactors members)).toArray

/-- Canonical proof-side lifted-factor subsets corresponding to
`supportPartitionByMinColumn`. -/
noncomputable def liftedFactorSubsetsOfSupports
    (d : Hex.LiftData)
    {r : Nat} (trueSupports : Set (Set (Fin r))) :
    Array (LiftedFactorSubset d) :=
  ((supportPartitionByMinColumn trueSupports).map
    (fun members => liftedFactorSubsetOfMembers d members)).toArray

/-- Indexed form of `liftedFactorSubsetsOfSupports`. -/
theorem liftedFactorSubsetsOfSupports_getD
    (d : Hex.LiftData)
    {r : Nat} (trueSupports : Set (Set (Fin r)))
    {i : Nat}
    (hi : i < (supportPartitionByMinColumn trueSupports).length) :
    (liftedFactorSubsetsOfSupports d trueSupports).getD i ∅ =
      liftedFactorSubsetOfMembers d
        ((supportPartitionByMinColumn trueSupports).getD i []) := by
  simp [liftedFactorSubsetsOfSupports, hi]

/-- Indexed canonical selector-product equality for the support partition. -/
theorem selectedFactorArraysOfSupports_polyProduct
    (d : Hex.LiftData)
    {r : Nat} (trueSupports : Set (Set (Fin r))) :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      Array.polyProduct
          ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[]) =
        liftedFactorProduct d
          ((liftedFactorSubsetsOfSupports d trueSupports).getD i ∅) := by
  intro i hi
  let classes := supportPartitionByMinColumn trueSupports
  have hi_classes : i < classes.length := by
    simpa [expectedIndicatorArrayOfSupports, classes] using hi
  have hselected :
      (selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[] =
        selectedFactorsOfMembers d.liftedFactors (classes.getD i []) := by
    simp [selectedFactorArraysOfSupports, classes, hi_classes]
  have hsubset :
      (liftedFactorSubsetsOfSupports d trueSupports).getD i ∅ =
        liftedFactorSubsetOfMembers d (classes.getD i []) := by
    simp [liftedFactorSubsetsOfSupports, classes, hi_classes]
  rw [hselected, hsubset]
  exact selectedFactorsOfMembers_polyProduct d (classes.getD i [])

/--
Convert a proof-side lifted-subset representation into the exact modular
product equality consumed by the Mignotte recovery wrapper, once the executable
selected-factor array has been identified with that lifted subset's product.
-/
theorem productCongruence_of_representsIntegerFactorAtLift
    {core : Hex.ZPoly} {d : Hex.LiftData} {selected : Array Hex.ZPoly}
    {expectedFactor : Hex.ZPoly} {S : LiftedFactorSubset d}
    (hselected_product :
      Array.polyProduct selected = liftedFactorProduct d S)
    (hrep : RepresentsIntegerFactorAtLift core d expectedFactor S) :
    Hex.ZPoly.reduceModPow
        (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
          (Array.polyProduct selected)) d.p d.k =
      Hex.ZPoly.reduceModPow expectedFactor d.p d.k := by
  unfold RepresentsIntegerFactorAtLift scaledLiftedFactorProduct at hrep
  rw [hselected_product]
  exact hrep

/--
Indexed form of `productCongruence_of_representsIntegerFactorAtLift`.
Callers provide, for each expected indicator, the proof-side lifted subset
selected by the canonical class plus its `RepresentsIntegerFactorAtLift`
certificate; this theorem returns the `hproduct` family expected by
`ofMignottePrecision...`.
-/
theorem productCongruencesOfSelectedRepresentations
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (expectedIndicators : Array (Array Int))
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
    (supportSubsets : Array (LiftedFactorSubset d))
    (hselected_product :
      ∀ i, i < expectedIndicators.size →
        Array.polyProduct (selectedFactors.getD i #[]) =
          liftedFactorProduct d (supportSubsets.getD i ∅))
    (hrep :
      ∀ i, i < expectedIndicators.size →
        RepresentsIntegerFactorAtLift core d (expectedFactors.getD i 0)
          (supportSubsets.getD i ∅)) :
    ∀ i, i < expectedIndicators.size →
      Hex.ZPoly.reduceModPow
          (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
            (Array.polyProduct (selectedFactors.getD i #[])))
          d.p d.k =
        Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k := by
  intro i hi
  exact productCongruence_of_representsIntegerFactorAtLift
    (hselected_product i hi) (hrep i hi)

/--
Canonical-support specialisation of the per-class Mignotte product bridge.
It targets `selectedFactorArraysOfSupports` directly, matching the hypothesis
surface of
`factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`.
-/
theorem productCongruencesOfCanonicalSupportRepresentations
    {core : Hex.ZPoly} {d : Hex.LiftData} {r : Nat}
    (trueSupports : Set (Set (Fin r)))
    (expectedFactors : Array Hex.ZPoly)
    (supportSubsets : Array (LiftedFactorSubset d))
    (hselected_product :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Array.polyProduct
            ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[]) =
          liftedFactorProduct d (supportSubsets.getD i ∅))
    (hrep :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        RepresentsIntegerFactorAtLift core d (expectedFactors.getD i 0)
          (supportSubsets.getD i ∅)) :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      Hex.ZPoly.reduceModPow
          (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
            (Array.polyProduct
              ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[])))
          d.p d.k =
        Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k :=
  productCongruencesOfSelectedRepresentations
    (expectedIndicatorArrayOfSupports trueSupports)
    (selectedFactorArraysOfSupports d.liftedFactors trueSupports)
    expectedFactors supportSubsets hselected_product hrep

/--
Canonical-support bridge using the subset array induced directly by
`supportPartitionByMinColumn`.
-/
theorem productCongruencesOfCanonicalSupportMemberRepresentations
    {core : Hex.ZPoly} {d : Hex.LiftData} {r : Nat}
    (trueSupports : Set (Set (Fin r)))
    (expectedFactors : Array Hex.ZPoly)
    (hselected_product :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Array.polyProduct
            ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[]) =
          liftedFactorProduct d
            ((liftedFactorSubsetsOfSupports d trueSupports).getD i ∅))
    (hrep :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        RepresentsIntegerFactorAtLift core d (expectedFactors.getD i 0)
          ((liftedFactorSubsetsOfSupports d trueSupports).getD i ∅)) :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      Hex.ZPoly.reduceModPow
          (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
            (Array.polyProduct
              ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[])))
          d.p d.k =
        Hex.ZPoly.reduceModPow (expectedFactors.getD i 0) d.p d.k :=
  productCongruencesOfCanonicalSupportRepresentations
    trueSupports expectedFactors
    (liftedFactorSubsetsOfSupports d trueSupports) hselected_product hrep

/--
The canonical support-driven indicators select the corresponding canonical
lifted-factor arrays, one support class at a time.
-/
theorem bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports
    (d : Hex.LiftData)
    (trueSupports : Set (Set (Fin d.liftedFactors.size)))
    (hclass_nonempty :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∃ j, j ∈ members)
    (hclass_bounds :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∀ j, j ∈ members → j < d.liftedFactors.size) :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      Hex.bhksIndicatorSelectedFactors d.liftedFactors
          ((expectedIndicatorArrayOfSupports trueSupports).getD i #[]) =
        some ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[]) := by
  intro i hi
  let classes := supportPartitionByMinColumn trueSupports
  have hi_classes : i < classes.length := by
    simpa [expectedIndicatorArrayOfSupports, classes] using hi
  have hmem : classes.getD i [] ∈ classes := by
    have hgetD : classes.getD i [] = classes[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_classes]
    rw [hgetD]
    exact List.getElem_mem hi_classes
  have hindicator :
      (expectedIndicatorArrayOfSupports trueSupports).getD i #[] =
        classIndicatorArray d.liftedFactors.size (classes.getD i []) := by
    simp [expectedIndicatorArrayOfSupports, classes, hi_classes]
  have hselected :
      (selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[] =
        selectedFactorsOfMembers d.liftedFactors (classes.getD i []) := by
    simp [selectedFactorArraysOfSupports, classes, hi_classes]
  rw [hindicator, hselected]
  exact bhksIndicatorSelectedFactors_classIndicatorArray
    d.liftedFactors (classes.getD i [])
    (hclass_nonempty (classes.getD i []) hmem)
    (hclass_bounds (classes.getD i []) hmem)

/--
Every support-equivalence class in `supportPartitionByMinColumn` contains its
representative column, so each class is nonempty.  This discharges the
`hclass_nonempty` premise of the canonical-support recovery wrapper directly
from the canonical partition's shape, with no recovery-side hypothesis. -/
theorem supportPartitionByMinColumn_class_nonempty {r : Nat}
    (trueSupports : Set (Set (Fin r))) :
    ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
      ∃ j, j ∈ members := by
  intro members hmem
  unfold supportPartitionByMinColumn at hmem
  rw [List.mem_map] at hmem
  obtain ⟨rep, hrep_mem, rfl⟩ := hmem
  exact ⟨rep, supportClassMembers_rep_mem trueSupports hrep_mem⟩

/--
Every member of every support-equivalence class lies below the support index
dimension `r`.  At the executable lift-data layer, `r` is definitionally the
size of `d.liftedFactors`, so this discharges the `hclass_bounds` premise of
the canonical-support recovery wrapper directly. -/
theorem supportPartitionByMinColumn_class_lt {r : Nat}
    (trueSupports : Set (Set (Fin r))) :
    ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
      ∀ j, j ∈ members → j < r := by
  intro members hmem j hj
  unfold supportPartitionByMinColumn at hmem
  rw [List.mem_map] at hmem
  obtain ⟨rep, _, rfl⟩ := hmem
  exact ((mem_supportClassMembers_iff trueSupports rep j).mp hj).1

/--
Canonical per-class representation certificates extracted from a successful
`ForwardRecoveryInputs` candidate fold.

The candidate fold supplies, for each canonical indicator, the verified integer
candidate returned by `bhksIndicatorCandidate?`; the support partition lemmas
identify the same indicator with its selected lifted-factor subset.
-/
theorem bhksIndicatorCandidates?_canonicalRepresentations
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (h : ForwardRecoveryInputs f d)
    (trueSupports :
       Set (Set (Fin (projectedRowsOfLiftData f d h.rows_pos).factorCount)))
    (hindicators :
       h.expectedIndicators = expectedIndicatorArrayOfSupports trueSupports)
    (hf_monic : Hex.DensePoly.Monic f)
    (hliftedFactor_monic :
      ∀ i, i < d.liftedFactors.size →
        Hex.DensePoly.Monic (d.liftedFactors.getD i 0))
    (hp_two_lt : 2 < d.p ^ d.k) :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        RepresentsIntegerFactorAtLift f d (h.expectedFactors.getD i 0)
          ((liftedFactorSubsetsOfSupports d trueSupports).getD i ∅) := by
  intro i hi
  have hi_expected : i < h.expectedIndicators.size := by
    simpa [hindicators] using hi
  rcases Hex.bhksIndicatorCandidates?_getD_candidate h.candidates_eq i hi_expected with
    ⟨quotient, hcandidate⟩
  let classes := supportPartitionByMinColumn trueSupports
  have hi_classes : i < classes.length := by
    simpa [expectedIndicatorArrayOfSupports, classes] using hi
  have hselected :
      Hex.bhksIndicatorSelectedFactors d.liftedFactors
          (h.expectedIndicators.getD i #[]) =
        some (selectedFactorsOfMembers d.liftedFactors (classes.getD i [])) := by
    have hs :=
      bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports
        d trueSupports
        (supportPartitionByMinColumn_class_nonempty trueSupports)
        (supportPartitionByMinColumn_class_lt trueSupports)
        i hi
    have hselectedArray :
        (selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[] =
          selectedFactorsOfMembers d.liftedFactors (classes.getD i []) := by
      simp [selectedFactorArraysOfSupports, classes, hi_classes]
    have hs_expected :
        Hex.bhksIndicatorSelectedFactors d.liftedFactors
            (h.expectedIndicators.getD i #[]) =
          some ((selectedFactorArraysOfSupports d.liftedFactors trueSupports).getD i #[]) := by
      simpa [hindicators] using hs
    rw [hselectedArray] at hs_expected
    exact hs_expected
  have hrep :
      RepresentsIntegerFactorAtLift f d (h.expectedFactors.getD i 0)
        (liftedFactorSubsetOfMembers d (classes.getD i [])) :=
    bhksIndicatorCandidate?_representsIntegerFactorAtLift
      hcandidate hselected hf_monic hliftedFactor_monic hp_two_lt
  simpa [liftedFactorSubsetsOfSupports, classes, hi_classes] using hrep

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
indicator array. This is the A2 candidate-equality assembly for
`ForwardRecoveryInputs`: callers supply the selected lifted-factor products,
true-factor facts, and dilated centered-lift equalities for each indicator, and the
executable candidate fold returns the expected factor array.
-/
theorem candidatesOfDilatedCenteredLift
    {f : Hex.ZPoly} {d : Hex.LiftData}
    (expectedIndicators : Array (Array Int))
    (selectedFactors : Array (Array Hex.ZPoly))
    (expectedFactors : Array Hex.ZPoly)
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
    (hpos_lc :
      ∀ i, i < expectedIndicators.size →
        0 < Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0))
    (hdegree :
      ∀ i, i < expectedIndicators.size →
        0 < (expectedFactors.getD i 0).degree?.getD 0)
    (hdilated :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
            (Hex.centeredLiftPoly
              (Array.polyProduct (selectedFactors.getD i #[])) (d.p ^ d.k)) =
          expectedFactors.getD i 0) :
    Hex.bhksIndicatorCandidates? f d expectedIndicators =
      some expectedFactors :=
  bhksIndicatorCandidates?_eq_some_of_forwardCandidates
    f d expectedIndicators expectedFactors hsize
    (fun i hi =>
      bhksIndicatorCandidate?_eq_some_of_dilatedCenteredLift
        f d (expectedIndicators.getD i #[])
        (selectedFactors.getD i #[]) (expectedFactors.getD i 0)
        (hselected i hi) (hdivides i hi)
        (hprimitive i hi) (hsign i hi) (hpos_lc i hi) (hdegree i hi)
        (hdilated i hi))

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
    (hpos_lc :
      ∀ i, i < expectedIndicators.size →
        0 < Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0))
    (hdegree :
      ∀ i, i < expectedIndicators.size →
        0 < (expectedFactors.getD i 0).degree?.getD 0)
    (hdilated :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
            (Hex.centeredLiftPoly
              (Array.polyProduct (selectedFactors.getD i #[])) (d.p ^ d.k)) =
          expectedFactors.getD i 0)
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
      candidatesOfDilatedCenteredLift
        expectedIndicators selectedFactors expectedFactors hsize
        hselected hdivides hprimitive hsign hpos_lc hdegree hdilated
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
    (hdilated :
      ∀ i, i < expectedIndicators.size →
        Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
            (Hex.centeredLiftPoly
              (Array.polyProduct (selectedFactors.getD i #[])) (d.p ^ d.k)) =
          expectedFactors.getD i 0) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCandidateProducts
    rows_pos trueSupports lattice_eq_indicators mignotte_precision
    expectedIndicators indicators_match nondegenerate
    selectedFactors expectedFactors hf_ne_zero htrue.size_eq
    hselected htrue.divides htrue.primitive htrue.leadingCoeff_nonneg
    (fun i hi => by
      have hlc := htrue.monic i hi
      rw [hlc]
      decide)
    htrue.positive_degree hdilated
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
    (hpos_lc :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        0 < Hex.DensePoly.leadingCoeff (expectedFactors.getD i 0))
    (hdegree :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        0 < (expectedFactors.getD i 0).degree?.getD 0)
    (hdilated :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
            (Hex.centeredLiftPoly
              (Array.polyProduct (selectedFactors.getD i #[])) (d.p ^ d.k)) =
          expectedFactors.getD i 0)
    (product_eq : Array.polyProduct expectedFactors = f) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCandidateProducts
    rows_pos trueSupports lattice_eq_indicators mignotte_precision
    (expectedIndicatorArrayOfSupports trueSupports)
    (equivalenceClassIndicatorsOfLiftData_eq_expectedIndicatorArrayOfSupports
      rows_pos trueSupports lattice_eq_indicators)
    nondegenerate selectedFactors expectedFactors hf_ne_zero hsize
    hselected hdivides hprimitive hsign hpos_lc hdegree hdilated product_eq

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
    (hdilated :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff f)
            (Hex.centeredLiftPoly
              (Array.polyProduct (selectedFactors.getD i #[])) (d.p ^ d.k)) =
          expectedFactors.getD i 0) :
    ForwardRecoveryInputs f d :=
  ofMignottePrecisionCanonicalIndicators
    rows_pos trueSupports lattice_eq_indicators mignotte_precision
    nondegenerate selectedFactors expectedFactors hf_ne_zero htrue.size_eq
    hselected htrue.divides htrue.primitive htrue.leadingCoeff_nonneg
    (fun i hi => by
      have hlc := htrue.monic i hi
      rw [hlc]
      decide)
    htrue.positive_degree hdilated
    (productOfExpectedFactors htrue)

/--
Mignotte-precision `ForwardRecoveryInputs` constructor specialised to the
public `factorFast` lift shape `d = toMonicLiftData f (factorFastPrecisionCap f)
primeData` (the monic-core lift the executable fast path recovers against).  Drops the
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
`factorFast` lift shape `d = toMonicLiftData f (factorFastPrecisionCap f)
primeData` (the monic-core lift the executable fast path recovers against).  Drops both the explicit
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

This is the headline theorem the issue asks for: the implication from the
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
fast-path lemma: if a scheduled lift for the normalized square-free core
satisfies the forward-verification inputs, then the public `Hex.factorFast`
entry point succeeds.
-/
theorem factorFast_ne_none_of_forwardInputs_on_schedule
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    {target : Nat}
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hinputs :
      ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
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
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore target primeData) =
        some hinputs.expectedFactors :=
    bhksRecover_eq_some_of_forwardInputs
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.toMonicLiftData
        (Hex.normalizeForFactor f).squareFreeCore target primeData)
      hinputs
  exact
    Hex.factorFast_ne_none_of_core_recovery_on_schedule
      f primeData hB_pos hchoose hmem hrecover

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
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hinputs :
      ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.precisionForCoeffBound
            (Hex.factorFastPrecisionCap f) primeData.p)
          primeData)) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_forwardInputs_on_schedule
    f primeData hB_pos hchoose hinputs
    (Hex.cap_mem_henselPrecisionSchedule _)

/-- The monic-core lift data produced by the public `factorFast` pipeline for
`f` at the executable cap precision: `toMonicLiftData` of the normalized
square-free core of `f` at cap count `factorFastPrecisionCap f` over
`primeData`. This matches the lift data the executable fast path actually
recovers against (`factorFast_ne_none_of_core_recovery_on_schedule`). Local
abbreviation used inside the HO-4 leaf capstones to factor out the repeated
nested lift-data expression. -/
private abbrev factorFastCapLiftData
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData) : Hex.LiftData :=
  Hex.ZPoly.toMonicLiftData
    (Hex.normalizeForFactor f).squareFreeCore
    (Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) primeData.p)
    primeData

/--
The bad-vector witness attached to the actual Hensel lift used by
`Hex.factorFast`: the normalized square-free core lifted to
`precisionForCoeffBound (factorFastPrecisionCap f) primeData.p`.

This is a named cap-lift specialization of `badVectorWitnessOfLiftData`, so
callers no longer have to rebuild the nested executable lift expression before
feeding the witness to the cap-separation layer.
-/
def badVectorWitnessOfFactorFastCapLiftData
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly) :
    ExecutableBadVectorWitness :=
  badVectorWitnessOfLiftData
    (Hex.normalizeForFactor f).squareFreeCore
    (factorFastCapLiftData f primeData)
    rows_pos localFactorIndex localFactorDegree H

/--
The input-polynomial l2-norm squared for the actual `factorFast` cap-lift
witness is bounded by the executable squared coefficient norm of the normalized
square-free core, with the `+ 1` slack used by the BHKS cap.
-/
theorem factorFastCapLift_input_l2norm_sq_le_coeffNormSq_add_one
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly) :
    (HexPolyZMathlib.l2norm
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial) ^ 2 ≤
      ((Hex.normalizeForFactor f).squareFreeCore.coeffNormSq + 1 : ℝ) := by
  change
    (HexPolyZMathlib.l2norm
        (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore)) ^ 2 ≤
      ((Hex.normalizeForFactor f).squareFreeCore.coeffNormSq + 1 : ℝ)
  exact
    l2norm_toPolynomial_sq_le_coeffNormSq_add_one
      (Hex.normalizeForFactor f).squareFreeCore

/--
Concrete input-polynomial l2norm bound for the actual `factorFast` cap-lift
bad-vector witness.

This is the input-side fact needed by
`ExecutableBadVectorWitness.l2norm_product_lt_divisor_of_l2norm_bounds`,
specialized to `badVectorWitnessOfFactorFastCapLiftData`.
-/
theorem factorFastCapLift_inputPolynomial_l2norm_le_coeffL2NormBound
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly) :
    HexPolyZMathlib.l2norm
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial ≤
      (Hex.ZPoly.coeffL2NormBound
        (Hex.normalizeForFactor f).squareFreeCore : ℝ) :=
  ExecutableBadVectorWitness.inputPolynomial_l2norm_le_coeffL2NormBound
    (badVectorWitnessOfFactorFastCapLiftData
      f primeData rows_pos localFactorIndex localFactorDegree H)

/--
Strict Hadamard/l2norm comparison for the actual `factorFast` cap-lift
bad-vector witness, with the input bound discharged automatically by
`factorFastCapLift_inputPolynomial_l2norm_le_coeffL2NormBound`.

This is the cap-lift specialisation of
`ExecutableBadVectorWitness.l2norm_product_lt_divisor_of_auxiliary_bound`:
callers only have to supply the auxiliary-polynomial l2 bound and the cap
arithmetic against `coeffL2NormBound (normalizeForFactor f).squareFreeCore`,
and the resulting Hadamard/l2norm comparison is exactly the field consumed by
`FactorFastCapLiftAnalyticComparison`.
-/
theorem factorFastCapLift_l2norm_product_lt_divisor_of_auxiliary_bound
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (hstrict :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
          auxiliaryBound ^
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
        ((factorFastCapLiftData f primeData).p ^
            ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ)) :
    (HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      (HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ) :=
  ExecutableBadVectorWitness.l2norm_product_lt_divisor_of_auxiliary_bound
    (badVectorWitnessOfFactorFastCapLiftData
      f primeData rows_pos localFactorIndex localFactorDegree H)
    hauxiliary hstrict

/--
Actual-cap corrected auxiliary-polynomial identity supplied by
`BadVectorBridgeData`.

This is the `factorFast` cap-lift specialization of
`ExecutableBadVectorWitness.BadVectorBridgeData.auxiliary_eq'`, with the
canonical correction accessor exposed in the conclusion so later constructor
code can consume the field without rebuilding the cap-lift witness expression.
-/
theorem factorFastCapLift_auxiliary_eq_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports) :
    (badVectorWitnessOfFactorFastCapLiftData
      f primeData rows_pos localFactorIndex localFactorDegree H).H =
      BHKS.auxiliaryPolynomialWithCorrections
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).input
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).liftData
        ((badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v)
        (bridge.auxiliaryCorrections v hin hnot) :=
  bridge.auxiliary_eq' v hin hnot

/--
Actual-cap coefficientwise Hensel-lift congruence between a packaged true
factor and its corresponding lifted local factor.
-/
theorem factorFastCapLift_trueFactor_liftedFactor_coeff_dvd_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (i : Nat)
    (hi :
      i <
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).liftData.liftedFactors.size)
    (j : Nat) :
    ((((badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.p) ^
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.k : Nat) : ℤ) ∣
      (Hex.DensePoly.coeff (bridge.trueFactor i) j -
        Hex.DensePoly.coeff
          ((badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).liftData.liftedFactors.getD i 0)
          j) :=
  ExecutableBadVectorWitness.BadVectorBridgeData.trueFactor_liftedFactor_coeff_dvd_of_bridge_data
    bridge i hi j

/--
Actual-cap selected-index Hensel-lift congruence supplied by
`BadVectorBridgeData`.
-/
theorem factorFastCapLift_selected_trueFactor_liftedFactor_coeff_dvd_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (j : Nat) :
    ((((badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.p) ^
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.k : Nat) : ℤ) ∣
      (Hex.DensePoly.coeff
          (bridge.trueFactor
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).localFactorIndex)
          j -
        Hex.DensePoly.coeff
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).selectedLiftedFactor
          j) :=
  ExecutableBadVectorWitness.BadVectorBridgeData.selected_trueFactor_liftedFactor_coeff_dvd_of_bridge_data
    bridge j

/--
Actual-cap per-coefficient precision separation supplied by
`BadVectorBridgeData`.
-/
theorem factorFastCapLift_precision_separation_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (j : Nat)
    (hj :
      j <
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).input.degree?.getD 0) :
    2 *
        Hex.bhksCoeffBound
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).input j <
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.p ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).liftData.k :=
  ExecutableBadVectorWitness.BadVectorBridgeData.precision_separation_of_bridge_data
    bridge j hj

/--
Actual-cap selected local-factor degree positivity supplied by
`BadVectorBridgeData`.
-/
theorem factorFastCapLift_localFactorDegree_pos_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports) :
    0 <
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).localFactorDegree :=
  ExecutableBadVectorWitness.localFactorDegree_pos_of_bridge_data bridge

/--
Actual-cap rational coprimality clause supplied by `BadVectorBridgeData`.
-/
theorem factorFastCapLift_coprime_input_aux_over_rat_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports) :
    IsCoprime
      ((badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.map
          (Int.castRingHom ℚ))
      ((badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.map
          (Int.castRingHom ℚ)) :=
  ExecutableBadVectorWitness.coprime_input_aux_over_rat_of_bridge_data bridge

/--
Actual-cap `p^(k*d)` resultant divisibility clause supplied by
`BadVectorBridgeData`.
-/
theorem factorFastCapLift_resultant_divisible_by_p_pow_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports) :
    (((badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.p ^
      ((badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).liftData.k *
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).localFactorDegree) :
      Nat) : ℤ) ∣
      Polynomial.resultant
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial :=
  ExecutableBadVectorWitness.resultant_divisible_by_p_pow_of_bridge_data bridge

/--
Actual-cap corrected auxiliary-polynomial squared-l2 bound supplied by
`BadVectorBridgeData`.

This is the factor-fast cap-lift specialization of
`ExecutableBadVectorWitness.BadVectorBridgeData.auxiliaryPolynomial_l2norm_sq_le_of_bridge_data`.
It exposes the corrected diagonal-row contribution through the bridge
correction accessor, so later cap-separation code can bound the real
auxiliary norm without falling back to the zero-correction auxiliary theorem.
-/
theorem factorFastCapLift_auxiliaryPolynomial_l2norm_sq_le_of_bridge_data
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j) :
    (HexPolyZMathlib.l2norm
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^ 2 ≤
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) :=
  ExecutableBadVectorWitness.BadVectorBridgeData.auxiliaryPolynomial_l2norm_sq_le_of_bridge_data
    bridge v hin hnot hcld

/--
The remaining analytic comparison needed by cap separation at the actual
`factorFast` cap lift.

The field is the #5216-style Hadamard/l2norm upper-bound comparison, but the
package is indexed by the cap-lift witness.  Downstream actual-cap callers can
carry this named object instead of passing the raw
`ExecutableCapSeparationHypotheses.l2norm_upper_lt_divisor` field directly.
-/
structure FactorFastCapLiftAnalyticComparison
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly) where
  hadamard_l2norm_lt_divisor :
    (HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      (HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ)

/--
Extract the actual-cap analytic comparison from an already assembled
cap-separation hypothesis package.

This is the non-raw call shape for later `factorFast` cap-lift code that has
already built `ExecutableCapSeparationHypotheses`: callers can pass this named
comparison to the actual-cap projected-row-span bridge without restating the
Hadamard/l2norm inequality field.
-/
def FactorFastCapLiftAnalyticComparison.ofCapSeparationHypotheses
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (hcap :
      ExecutableCapSeparationHypotheses
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports) :
    FactorFastCapLiftAnalyticComparison
      f primeData rows_pos localFactorIndex localFactorDegree H where
  hadamard_l2norm_lt_divisor := hcap.l2norm_upper_lt_divisor

/--
Supply the actual-cap analytic comparison directly from the bridge-data
cap-separation inputs.

This is the small producer surface for callers that have the projected
bad-vector bridge, cut hypotheses, prime positivity, and the BHKS
Hadamard/l2norm strict inequality, but do not want to build a full
`ExecutableCapSeparationHypotheses` package just to extract its analytic
field.  Internally it composes through `capSeparationOfBridgeData`, so the
bridge-to-bad-vector setup remains shared with the projected-row-span
cap-separation theorem.
-/
theorem FactorFastCapLiftAnalyticComparison.ofBridgeData
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hp : 0 < (factorFastCapLiftData f primeData).p)
    (hlt :
      (HexPolyZMathlib.l2norm
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial) ^
          (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^
          (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ)) :
    FactorFastCapLiftAnalyticComparison
      f primeData rows_pos localFactorIndex localFactorDegree H :=
  FactorFastCapLiftAnalyticComparison.ofCapSeparationHypotheses
    f primeData rows_pos localFactorIndex localFactorDegree H trueSupports
    (capSeparationOfBridgeData rows_pos localFactorIndex localFactorDegree H
      trueSupports hcut bridge hp hlt)

/--
Actual-cap analytic comparison from separate l2-norm bounds and the remaining
strict cap-arithmetic inequality.

This instantiates
`ExecutableBadVectorWitness.l2norm_product_lt_divisor_of_l2norm_bounds` at the
`factorFastCapLiftData` witness, so downstream actual-cap constructors can
feed concrete input/auxiliary norm bounds and a cap-arithmetic estimate without
restating the Hadamard monotonicity step.
-/
theorem FactorFastCapLiftAnalyticComparison.ofL2normBounds
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    {inputBound auxiliaryBound : ℝ}
    (hinput :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial ≤
        inputBound)
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (hstrict :
      inputBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ)) :
    FactorFastCapLiftAnalyticComparison
      f primeData rows_pos localFactorIndex localFactorDegree H where
  hadamard_l2norm_lt_divisor :=
    ExecutableBadVectorWitness.l2norm_product_lt_divisor_of_l2norm_bounds
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H)
      hinput hauxiliary hstrict

/--
Actual-cap analytic comparison from the corrected auxiliary-polynomial
squared-l2 bound supplied by `BadVectorBridgeData`.

The theorem plugs the corrected auxiliary l2 estimate into the cap-lift
Hadamard comparison.  Callers provide the remaining arithmetic step bounding
the explicit corrected RHS by `auxiliaryBound ^ 2`, plus the strict divisor
comparison for that `auxiliaryBound`.
-/
theorem FactorFastCapLiftAnalyticComparison.ofBridgeDataCorrectedAuxiliaryL2normSq
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (hstrict :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ)) :
    FactorFastCapLiftAnalyticComparison
      f primeData rows_pos localFactorIndex localFactorDegree H := by
  have hauxiliary_sq :
      (HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^ 2 ≤
        auxiliaryBound ^ 2 :=
    (factorFastCapLift_auxiliaryPolynomial_l2norm_sq_le_of_bridge_data
      f primeData rows_pos localFactorIndex localFactorDegree H trueSupports
      bridge v hin hnot hcld).trans hauxiliary_sq_bound
  have hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound := by
    exact le_of_sq_le_sq hauxiliary_sq hauxiliaryBound_nonneg
  exact
    FactorFastCapLiftAnalyticComparison.ofL2normBounds
      f primeData rows_pos localFactorIndex localFactorDegree H
      (factorFastCapLift_inputPolynomial_l2norm_le_coeffL2NormBound
        f primeData rows_pos localFactorIndex localFactorDegree H)
      hauxiliary hstrict

/--
Actual-cap bad-vector contradiction from the named cap-lift analytic
comparison package.

This is the `factorFastCapLiftData`-specialized form of the generic
`ExecutableBadVectorWitness.no_bhks_bad_setup_at_factorFastPrecisionCap`
wrapper from `TerminationBound.lean`: callers that have already produced
`FactorFastCapLiftAnalyticComparison` no longer need to project the raw
Hadamard/l2norm inequality before eliminating an executable bad-vector setup.
-/
theorem no_bhks_bad_setup_of_factorFastCapLiftAnalyticComparison
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (h_bad :
      ExecutableBadVectorWitness.IsBhksBadVectorSetup
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H))
    (hp : 0 < (factorFastCapLiftData f primeData).p)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H) :
    False :=
  ExecutableBadVectorWitness.no_bhks_bad_setup_at_factorFastPrecisionCap
    (badVectorWitnessOfFactorFastCapLiftData
      f primeData rows_pos localFactorIndex localFactorDegree H)
    C hC_nonneg hC h_bad hp hcomparison.hadamard_l2norm_lt_divisor

/--
Cap-separation hypotheses for the actual `factorFast` cap lift, assembled from
the landed bridge package and the named cap-lift analytic comparison package.
-/
def capSeparationOfBridgeDataAtFactorFastCapLift
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hp : 0 < (factorFastCapLiftData f primeData).p)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H) :
    ExecutableCapSeparationHypotheses
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H)
      trueSupports :=
  capSeparationOfBridgeData rows_pos localFactorIndex localFactorDegree H
    trueSupports hcut bridge hp hcomparison.hadamard_l2norm_lt_divisor

/--
Actual-cap BHKS separation for the projected rows built by the public
`factorFast` lift.

This composes the cap-lift witness, bad-vector bridge package, cut hypotheses,
and named analytic comparison into the projected row-span equality consumed by
the recovery layer.
-/
theorem projectedRowSpan_eq_trueFactorIndicatorLattice_of_factorFastCapLift_bridge
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (trueSupports :
      Set (Set (Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount)))
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hp : 0 < (factorFastCapLiftData f primeData).p)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H) :
    projectedRowSpanInt
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos) =
      trueFactorIndicatorLattice trueSupports :=
  projectedRowsOfLiftData_eq_trueFactorIndicatorLattice_of_cap
    (Hex.normalizeForFactor f).squareFreeCore
    (factorFastCapLiftData f primeData)
    rows_pos localFactorIndex localFactorDegree H trueSupports
    hcap_le C hC_nonneg hC
    (capSeparationOfBridgeDataAtFactorFastCapLift
      f primeData rows_pos localFactorIndex localFactorDegree H
      trueSupports hcut bridge hp hcomparison)

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
side and `factorFast_ne_none_of_forwardInputs_at_cap` for the caller side.
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
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_forwardInputs_at_cap f primeData hB_pos hchoose
    (ForwardRecoveryInputs.ofCapSeparationCanonicalIndicatorsAtPrecisionForCoeffBound
      rows_pos trueSupports localFactorIndex localFactorDegree H
      hcap_le C hC_nonneg hC hcap hp hk nondegenerate
      expectedFactors hsize hcandidate product_eq)

/--
Bridge-data form of
`factorFast_ne_none_of_capSeparationCanonicalIndicatorsAtPrecisionForCoeffBound`.

This wrapper is the capstone-facing consumer for the bad-vector package built
in `BadVector.lean`: callers provide `BadVectorBridgeData` plus the cut and
resultant-bound side conditions, and the theorem assembles the
`ExecutableCapSeparationHypotheses` required by the existing cap-separation
recovery theorem.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hlt :
      (HexPolyZMathlib.l2norm
            (badVectorWitnessOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData)
              rows_pos localFactorIndex localFactorDegree H).inputPolynomial) ^
          (badVectorWitnessOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData)
              rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm
            (badVectorWitnessOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData)
              rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^
          (badVectorWitnessOfLiftData
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData)
              rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ))
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_capSeparationCanonicalIndicatorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC
    (capSeparationOfBridgeData rows_pos localFactorIndex localFactorDegree H
      trueSupports hcut bridge (by omega) hlt)
    hB_pos hchoose hp hk nondegenerate expectedFactors hsize hcandidate
    product_eq

/--
Variant of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound`
that internalizes the `1 ≤ Hex.factorFastPrecisionCap f` side condition via
`HexBerlekampZassenhausMathlib.one_le_factorFastPrecisionCap`.  All other
hypotheses are passed through unchanged.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalCapPositive
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge
    hcomparison.hadamard_l2norm_lt_divisor
    (one_le_factorFastPrecisionCap f)
    hchoose hp hk nondegenerate expectedFactors hsize hcandidate product_eq

/--
Variant of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound`
that internalises the `2 ≤ (factorFastCapLiftData f primeData).p` side
condition.

The lower bound is derived from `hchoose` via `Hex.choosePrimeData?_prime`
and `Nat.Prime.two_le`, exploiting that `(factorFastCapLiftData f primeData).p`
unfolds definitionally to `primeData.p`.  All other hypotheses are passed
through unchanged.

This is the canonical-indicators analogue of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalPrimeLowerBound`:
the two internalisations target the indicator-side and support-side
canonical capstones respectively and compose with the in-flight
cap-positivity internalisation (PR #6364) on the final assembly path.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalPrimeLowerBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge
    hcomparison.hadamard_l2norm_lt_divisor hB_pos hchoose
    (Hex.choosePrimeData?_prime _ _ hchoose).two_le
    hk nondegenerate expectedFactors hsize hcandidate product_eq

/--
Variant of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound`
that internalises both easy executable-cap side conditions:
`1 ≤ factorFastPrecisionCap f` and
`2 ≤ (factorFastCapLiftData f primeData).p`.

The cap positivity follows from the packaged BHKS threshold slack via
`one_le_factorFastPrecisionCap`; the prime lower bound follows from `hchoose`.
This leaves callers with only the genuine cap-separation and candidate-product
facts needed by the canonical-indicators recovery path.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalPrimeLowerBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge hcomparison
    (one_le_factorFastPrecisionCap f) hchoose hk nondegenerate expectedFactors
    hsize hcandidate product_eq

/--
Actual-cap version of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound`.

This is the canonical-indicator counterpart to the support-side
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound`:
callers can provide bridge data indexed by the named
`badVectorWitnessOfFactorFastCapLiftData` witness together with the named
`FactorFastCapLiftAnalyticComparison`, rather than restating the underlying
`badVectorWitnessOfLiftData` expression or projecting the raw l2norm
inequality.
-/
theorem factorFast_ne_none_of_factorFastCapLiftBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalIndicatorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge hcomparison hchoose hk
    nondegenerate expectedFactors hsize hcandidate product_eq

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
caller side.
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
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
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
  factorFast_ne_none_of_forwardInputs_at_cap f primeData hB_pos hchoose
    (ForwardRecoveryInputs.ofMignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound
      rows_pos trueSupports lattice_eq_indicators hp hk nondegenerate
      selectedFactors expectedFactors hf_ne_zero htrue hselected hproduct)

/--
Canonical-support wrapper for
`factorFast_ne_none_of_mignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound`.

The caller supplies the genuinely mathematical recovery facts: B7 lattice
identification, the expected true factors, and the per-class Mignotte product
congruence.  The support-driven non-degeneracy guard and the selected lifted
factor arrays are derived internally from `trueSupports`, so later HO-4 call
sites do not have to repeat the raw executable `nondegenerate` and `hselected`
fields.
-/
theorem factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound
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
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hp : 2 ≤ (factorFastCapLiftData f primeData).p)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (hprojected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (hclasses_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hclass_nonempty :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∃ j, j ∈ members)
    (hclass_bounds :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∀ j, j ∈ members →
          j < (factorFastCapLiftData f primeData).liftedFactors.size)
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (htrue :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_mignottePrecisionCanonicalIndicatorsExpectedFactorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports lattice_eq_indicators hB_pos hchoose
    hp hk
    (ForwardRecoveryInputs.canonicalSupportIndicators_nondegenerate
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos)
      trueSupports hprojected_nonempty hclasses_two)
    (ForwardRecoveryInputs.selectedFactorArraysOfSupports
      (factorFastCapLiftData f primeData).liftedFactors trueSupports)
    expectedFactors hf_ne_zero htrue
    (ForwardRecoveryInputs.bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports
      (factorFastCapLiftData f primeData) trueSupports
      hclass_nonempty hclass_bounds)
    hproduct

set_option maxHeartbeats 1000000 in
/-- Canonical-support recovery inputs at the `factorFast` cap lift.

Bundles every hypothesis consumed by the canonical-support recovery wrapper
`factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`
other than the `factorFast`-pipeline scaffolding (`hB_pos`, `hchoose`, `hp`,
`hk`):

* the BHKS `L' = W` identification (`lattice_eq_indicators`);
* the support-partition shape facts (`projected_nonempty`, `classes_two`,
  `class_nonempty`, `class_bounds`);
* the expected true-factor package (`expected_true_factors`);
* the per-indicator Mignotte product congruence (`product_congr`).

The `class_nonempty` and `class_bounds` fields are unconditional shape facts
of `supportPartitionByMinColumn` discharged by
`ForwardRecoveryInputs.supportPartitionByMinColumn_class_nonempty` and
`ForwardRecoveryInputs.supportPartitionByMinColumn_class_lt`; the
`ofExpectedFactors` constructor wires them in automatically. -/
structure CanonicalRecoveryInputs
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData) where
  /-- Positive lattice dimension so the projected rows are well-defined. -/
  rows_pos : HasPositiveDimension
    (Hex.normalizeForFactor f).squareFreeCore
    (factorFastCapLiftData f primeData)
  /-- Canonical true-factor supports indexed by the lifted-factor positions. -/
  trueSupports : Set (Set (Fin (projectedRowsOfLiftData
    (Hex.normalizeForFactor f).squareFreeCore
    (factorFastCapLiftData f primeData)
    rows_pos).factorCount))
  /-- BHKS `L' = W` at the canonical true-factor indicator lattice. -/
  lattice_eq_indicators :
    BHKS.projectedRowSpanInt
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos) =
      BHKS.trueFactorIndicatorLattice trueSupports
  /-- Projected rows are nonempty. -/
  projected_nonempty :
    (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).projectedRows.isEmpty = false
  /-- The support-equivalence partition has at least two classes (nontrivial
      fast path). -/
  classes_two :
    2 ≤ (supportPartitionByMinColumn trueSupports).length
  /-- Every support class is nonempty. -/
  class_nonempty :
    ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
      ∃ j, j ∈ members
  /-- Members of each support class lie inside the lifted-factor array. -/
  class_bounds :
    ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
      ∀ j, j ∈ members →
        j < (factorFastCapLiftData f primeData).liftedFactors.size
  /-- Nonzero square-free core. -/
  hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0
  /-- The expected true-factor integer array. -/
  expectedFactors : Array Hex.ZPoly
  /-- The expected true-factor package backing the canonical indicator array. -/
  expected_true_factors :
    ForwardRecoveryInputs.ExpectedTrueFactors
      (Hex.normalizeForFactor f).squareFreeCore
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors
  /-- Per-indicator Mignotte product congruence. -/
  product_congr :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      Hex.ZPoly.reduceModPow
          (Hex.DensePoly.scale
            (Hex.DensePoly.leadingCoeff
              (Hex.normalizeForFactor f).squareFreeCore)
            (Array.polyProduct
              ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                (factorFastCapLiftData f primeData).liftedFactors
                trueSupports).getD i #[])))
          (factorFastCapLiftData f primeData).p
          (factorFastCapLiftData f primeData).k =
        Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
          (factorFastCapLiftData f primeData).p
          (factorFastCapLiftData f primeData).k

namespace CanonicalRecoveryInputs

/-- Constructor for `CanonicalRecoveryInputs` that discharges the two
unconditional support-partition shape facts (`class_nonempty`,
`class_bounds`) internally, keeping caller obligations focused on the
genuinely mathematical inputs. -/
def ofExpectedFactors
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData))
    (trueSupports : Set (Set (Fin (projectedRowsOfLiftData
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
    (projected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (classes_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (expectedFactors : Array Hex.ZPoly)
    (expected_true_factors :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (product_congr :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    CanonicalRecoveryInputs f primeData where
  rows_pos := rows_pos
  trueSupports := trueSupports
  lattice_eq_indicators := lattice_eq_indicators
  projected_nonempty := projected_nonempty
  classes_two := classes_two
  class_nonempty :=
    ForwardRecoveryInputs.supportPartitionByMinColumn_class_nonempty trueSupports
  class_bounds :=
    ForwardRecoveryInputs.supportPartitionByMinColumn_class_lt trueSupports
  hf_ne_zero := hf_ne_zero
  expectedFactors := expectedFactors
  expected_true_factors := expected_true_factors
  product_congr := product_congr

end CanonicalRecoveryInputs

set_option maxHeartbeats 1000000 in
/--
Canonical-support recovery inputs after cap separation has supplied the
`L' = W` lattice identification.

This is the tail package for the actual-cap `BadVectorBridgeData` assembly:
callers still provide the support-partition shape facts, expected true-factor
package, and per-indicator Mignotte product congruences, while the
cap-separation wrapper below derives `lattice_eq_indicators` from bridge data.
-/
structure CanonicalRecoveryTailInputs
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData))
    (trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))) where
  /-- Projected rows are nonempty. -/
  projected_nonempty :
    (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).projectedRows.isEmpty = false
  /-- The support-equivalence partition has at least two classes. -/
  classes_two :
    2 ≤ (supportPartitionByMinColumn trueSupports).length
  /-- Every support class is nonempty. -/
  class_nonempty :
    ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
      ∃ j, j ∈ members
  /-- Members of each support class lie inside the lifted-factor array. -/
  class_bounds :
    ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
      ∀ j, j ∈ members →
        j < (factorFastCapLiftData f primeData).liftedFactors.size
  /-- Nonzero square-free core. -/
  hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0
  /-- The expected true-factor integer array. -/
  expectedFactors : Array Hex.ZPoly
  /-- The expected true-factor package backing the canonical indicator array. -/
  expected_true_factors :
    ForwardRecoveryInputs.ExpectedTrueFactors
      (Hex.normalizeForFactor f).squareFreeCore
      (expectedIndicatorArrayOfSupports trueSupports) expectedFactors
  /-- Per-indicator Mignotte product congruence. -/
  product_congr :
    ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
      Hex.ZPoly.reduceModPow
          (Hex.DensePoly.scale
            (Hex.DensePoly.leadingCoeff
              (Hex.normalizeForFactor f).squareFreeCore)
            (Array.polyProduct
              ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                (factorFastCapLiftData f primeData).liftedFactors
                trueSupports).getD i #[])))
          (factorFastCapLiftData f primeData).p
          (factorFastCapLiftData f primeData).k =
        Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
          (factorFastCapLiftData f primeData).p
          (factorFastCapLiftData f primeData).k

namespace CanonicalRecoveryTailInputs

/-- Constructor for `CanonicalRecoveryTailInputs` that discharges the two
unconditional support-partition shape facts internally. -/
def ofExpectedFactors
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (projected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (classes_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (expectedFactors : Array Hex.ZPoly)
    (expected_true_factors :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (product_congr :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    CanonicalRecoveryTailInputs f primeData rows_pos trueSupports where
  projected_nonempty := projected_nonempty
  classes_two := classes_two
  class_nonempty :=
    ForwardRecoveryInputs.supportPartitionByMinColumn_class_nonempty trueSupports
  class_bounds :=
    ForwardRecoveryInputs.supportPartitionByMinColumn_class_lt trueSupports
  hf_ne_zero := hf_ne_zero
  expectedFactors := expectedFactors
  expected_true_factors := expected_true_factors
  product_congr := product_congr

/--
Closed `CanonicalRecoveryTailInputs` constructor at the actual `factorFast`
cap lift from per-canonical-class `RepresentsIntegerFactorAtLift` certificates.

Composes
`ForwardRecoveryInputs.productCongruencesOfCanonicalSupportMemberRepresentations`
with the unconditional canonical selector-product equality
`ForwardRecoveryInputs.selectedFactorArraysOfSupports_polyProduct` so the
caller only supplies the support-partition shape facts (`projected_nonempty`,
`classes_two`), the nonzero core fact, the expected true-factor package, and
one `RepresentsIntegerFactorAtLift` certificate per canonical support class.
The per-class Mignotte product congruence is derived from those certificates,
and the unconditional `class_nonempty` / `class_bounds` shape facts are
discharged via `ofExpectedFactors`.
-/
def ofCanonicalSupportRepresentations
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (projected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (classes_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (expectedFactors : Array Hex.ZPoly)
    (expected_true_factors :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hrep :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        RepresentsIntegerFactorAtLift
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          (expectedFactors.getD i 0)
          ((ForwardRecoveryInputs.liftedFactorSubsetsOfSupports
            (factorFastCapLiftData f primeData) trueSupports).getD i ∅)) :
    CanonicalRecoveryTailInputs f primeData rows_pos trueSupports :=
  ofExpectedFactors projected_nonempty classes_two hf_ne_zero
    expectedFactors expected_true_factors
    (ForwardRecoveryInputs.productCongruencesOfCanonicalSupportMemberRepresentations
      trueSupports expectedFactors
      (ForwardRecoveryInputs.selectedFactorArraysOfSupports_polyProduct
        (factorFastCapLiftData f primeData) trueSupports)
      hrep)

/--
Actual-cap recovery-tail constructor from a closed `ForwardRecoveryInputs`
package.

This is the `factorFastCapLiftData`-specialised wrapper around
`ForwardRecoveryInputs.bhksIndicatorCandidates?_canonicalRepresentations`.
The square-free core monicness, lifted-factor monicness, and strict
`2 < p^k` precision side condition stay explicit: the current normalization
API does not expose an unconditional monic theorem for
`(Hex.normalizeForFactor f).squareFreeCore`, and callers that have a stronger
normalization surface can discharge those hypotheses before using this
constructor.
-/
def ofForwardRecoveryInputsCanonicalRepresentations
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (h :
      ForwardRecoveryInputs
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      h.rows_pos).factorCount)))
    (hindicators :
      h.expectedIndicators = expectedIndicatorArrayOfSupports trueSupports)
    (projected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        h.rows_pos).projectedRows.isEmpty = false)
    (classes_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hf_monic : Hex.DensePoly.Monic (Hex.normalizeForFactor f).squareFreeCore)
    (hliftedFactor_monic :
      ∀ i, i < (factorFastCapLiftData f primeData).liftedFactors.size →
        Hex.DensePoly.Monic
          ((factorFastCapLiftData f primeData).liftedFactors.getD i 0))
    (hp_two_lt :
      2 < (factorFastCapLiftData f primeData).p ^
        (factorFastCapLiftData f primeData).k) :
    CanonicalRecoveryTailInputs f primeData h.rows_pos trueSupports :=
  ofCanonicalSupportRepresentations projected_nonempty classes_two hf_ne_zero
    h.expectedFactors
    (by
      simpa [hindicators] using
        ForwardRecoveryInputs.expectedTrueFactors_of_monic hf_monic h)
    (ForwardRecoveryInputs.bhksIndicatorCandidates?_canonicalRepresentations
      h trueSupports hindicators hf_monic hliftedFactor_monic hp_two_lt)

end CanonicalRecoveryTailInputs

set_option maxHeartbeats 1000000 in
/--
Cap-separation side inputs for the actual `factorFast` cap lift.

This bundles the bridge/cut/comparison facts and the two remaining
precision/prime-choice equations used by the conditional HO-4 assembly.  The
recovery-side facts live separately in `CanonicalRecoveryTailInputs`, so the
current executable theorem can consume one cap-separation package and one
recovery package while keeping the prime-search success witness explicit.
-/
structure FactorFastCapSeparationInputs
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData))
    (trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))) where
  /-- Selected local factor index for the bad-vector witness. -/
  localFactorIndex : Nat
  /-- Selected local factor degree for the bad-vector witness. -/
  localFactorDegree : Nat
  /-- Auxiliary polynomial used by the bad-vector witness. -/
  H : Hex.ZPoly
  /-- The executable lift precision dominates the normalized-core cap. -/
  cap_le :
    Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
      (factorFastCapLiftData f primeData).k
  /-- BHKS cut constant. -/
  C : ℝ
  /-- The BHKS cut constant is nonnegative. -/
  C_nonneg : 0 ≤ C
  /-- The BHKS cut constant is bounded by the project LLL constant. -/
  C_le_two : C ≤ 2
  /-- Cut-projection hypotheses for the actual cap lift. -/
  cut :
    CutProjectionHypotheses
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos)
      trueSupports
  /-- Executable bad-vector bridge data for the actual cap-lift witness. -/
  bridge :
    ExecutableBadVectorWitness.BadVectorBridgeData
      (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H)
      trueSupports
  /-- Analytic comparison for the actual cap-lift witness. -/
  comparison :
    FactorFastCapLiftAnalyticComparison
      f primeData rows_pos localFactorIndex localFactorDegree H
  /-- Prime-choice equation from the public fast path. -/
  choose_eq :
    Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData
  /-- Stored cap-lift precision equation for the normalized core. -/
  precision_eq :
    (factorFastCapLiftData f primeData).k =
      Hex.precisionForCoeffBound
        (Hex.factorFastPrecisionCap
          (Hex.normalizeForFactor f).squareFreeCore)
        (factorFastCapLiftData f primeData).p

namespace FactorFastCapSeparationInputs

/--
Actual-cap package constructor from the named cap-lift components.

This is the closed record producer for callers that already have the
`BadVectorBridgeData`, cut hypotheses, analytic comparison, cap dominance,
prime-choice equation, and stored normalized-core precision equation at
`factorFastCapLiftData f primeData`.
-/
def ofBridgeDataWithComparison
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (comparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports where
  localFactorIndex := localFactorIndex
  localFactorDegree := localFactorDegree
  H := H
  cap_le := cap_le
  C := C
  C_nonneg := C_nonneg
  C_le_two := C_le_two
  cut := cut
  bridge := bridge
  comparison := comparison
  choose_eq := choose_eq
  precision_eq := precision_eq

/--
Actual-cap package constructor from raw bridge data and the strict analytic
Hadamard/l2norm comparison.

The prime-choice equation supplies the prime positivity needed by
`FactorFastCapLiftAnalyticComparison.ofBridgeData`; the stored precision
equation is threaded into `ofBridgeDataWithComparison`.
-/
def ofBridgeData
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (hlt :
      (HexPolyZMathlib.l2norm
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial) ^
          (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm
            (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial) ^
          (badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ)) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataWithComparison localFactorIndex localFactorDegree H cap_le
    C C_nonneg C_le_two cut bridge
    (FactorFastCapLiftAnalyticComparison.ofBridgeData
      f primeData rows_pos localFactorIndex localFactorDegree H trueSupports
      cut bridge
      (by
        have h2 : 2 ≤ (factorFastCapLiftData f primeData).p :=
          (Hex.choosePrimeData?_prime _ _ choose_eq).two_le
        omega)
      hlt)
    choose_eq precision_eq

/--
Build the cap-separation input package from the corrected auxiliary-polynomial
squared-l2 estimate.

This is the actual-cap producer surface for the corrected `BadVectorBridgeData`
path: callers provide the bridge data, one projected vector in `L' \ W`, the
CLD column bounds, a bound on the corrected auxiliary RHS (including the
explicit diagonal-correction sum), and the remaining strict cap-arithmetic
comparison.  The constructor then instantiates
`FactorFastCapLiftAnalyticComparison.ofBridgeDataCorrectedAuxiliaryL2normSq`
internally, so downstream final assembly consumes a single
`FactorFastCapSeparationInputs` record rather than re-threading the corrected
l2norm plumbing.
-/
def ofBridgeDataCorrectedAuxiliaryL2normSq
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (hstrict :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ))
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports where
  localFactorIndex := localFactorIndex
  localFactorDegree := localFactorDegree
  H := H
  cap_le := hcap_le
  C := C
  C_nonneg := hC_nonneg
  C_le_two := hC
  cut := hcut
  bridge := bridge
  comparison :=
    FactorFastCapLiftAnalyticComparison.ofBridgeDataCorrectedAuxiliaryL2normSq
      f primeData rows_pos localFactorIndex localFactorDegree H trueSupports
      bridge v hin hnot hcld hauxiliaryBound_nonneg hauxiliary_sq_bound hstrict
  choose_eq := hchoose
  precision_eq := hprecision

/--
Canonical projected-vector pointwise bound for the cap-lift bad-vector bridge.

Choosing `vectorSquareBound := cutRadiusSq4`, the `hvectorSquareBound` shape
consumed by `ofBridgeDataPointwiseAuxiliaryBounds*` follows from a bound on the
projected squared-norm sum (the cut-radius membership condition for a bad
vector), since each stored coordinate's square is at most the full sum.
-/
theorem projectedVector_sq_le_cutRadiusSq4
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hnorm_le :
      (∑ i : Fin (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos).factorCount, ((v i : ℝ)) ^ 2) ≤
        ((projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos).cutRadiusSq4 : ℝ)) :
    ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
      ((((badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
          i.val 0 : ℝ) ^ 2) ≤
        ((projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos).cutRadiusSq4 : ℝ) :=
  fun i =>
    (badVectorWitnessOfFactorFastCapLiftData
        f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray_sq_le_of_sum_le
      v _ (Nat.cast_nonneg _) hnorm_le i

/--
Canonical weighted-correction pointwise bound for the cap-lift bad-vector
bridge.

Choosing `correctionWeightedBound := D * p ^ (2k)`, the `hcorrectionWeightedBound`
shape consumed by `ofBridgeDataPointwiseAuxiliaryBounds*` follows from a
coordinate square bound `D` on the diagonal-row corrections, since the
cut-threshold weight `p ^ (2 (k − ℓ_j))` is at most `p ^ (2k)`.
-/
theorem correctionWeighted_le_mul_pow
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hp : 1 ≤ (factorFastCapLiftData f primeData).p)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (D : ℝ)
    (hD :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ)) ^ 2 ≤ D) :
    ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
      (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
        (((factorFastCapLiftData f primeData).p : ℝ) ^
          (2 *
            ((factorFastCapLiftData f primeData).k -
              Hex.bhksCoeffCutThreshold
                (factorFastCapLiftData f primeData).p
                (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
        D * ((factorFastCapLiftData f primeData).p : ℝ) ^
          (2 * (factorFastCapLiftData f primeData).k) :=
  fun j hj =>
    BHKS.correctionWeighted_sq_le_of_coeff_sq_le
      (Hex.normalizeForFactor f).squareFreeCore (factorFastCapLiftData f primeData)
      (bridge.auxiliaryCorrections v hin hnot) D hp hD j hj

/--
Build the cap-separation input package from pointwise auxiliary-coordinate
bounds.

This packages the corrected-auxiliary squared-l2 RHS bound as two pointwise
ingredients — a pointwise bound on the projected-vector squared coordinates
and a pointwise bound on the weighted correction coordinates — together with
the resulting bound on `auxiliaryBound ^ 2`. Internally it uses
`BHKS.projectedVectorSquareSum_le_factorCount_mul` and
`BHKS.correctionWeightedSum_le_degree_mul` to combine the pointwise estimates
into the explicit finite sum required by
`ofBridgeDataCorrectedAuxiliaryL2normSq`.
-/
def ofBridgeDataPointwiseAuxiliaryBounds
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (hstrict :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
      ((factorFastCapLiftData f primeData).p ^
        ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ))
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataCorrectedAuxiliaryL2normSq localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    hauxiliaryBound_nonneg
    (by
      have hvectorSquareSum :
          (∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
            ((((badVectorWitnessOfFactorFastCapLiftData
                  f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                i.val 0 : ℝ) ^ 2)) ≤
            ((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound :=
        BHKS.projectedVectorSquareSum_le_factorCount_mul
          ((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v)
          vectorSquareBound hvectorSquareBound
      have hcorrectionWeightedSum :
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
              (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                (((factorFastCapLiftData f primeData).p : ℝ) ^
                  (2 *
                    ((factorFastCapLiftData f primeData).k -
                      Hex.bhksCoeffCutThreshold
                        (factorFastCapLiftData f primeData).p
                        (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
            ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
              correctionWeightedBound :=
        BHKS.correctionWeightedSum_le_degree_mul
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          (bridge.auxiliaryCorrections v hin hnot) correctionWeightedBound
          hcorrectionWeightedBound
      have hcldNonneg :
          (0 : ℝ) ≤
            ((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ) :=
        mul_nonneg
          (by exact_mod_cast Nat.zero_le _)
          (by exact_mod_cast Nat.zero_le _)
      have hfirstTerm :
          (∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
              (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                (BHKS.cldColumnNormBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (factorFastCapLiftData f primeData).p : ℝ)) ≤
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                vectorSquareBound) *
              (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                (BHKS.cldColumnNormBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (factorFastCapLiftData f primeData).p : ℝ)) :=
        mul_le_mul_of_nonneg_right hvectorSquareSum hcldNonneg
      have hsum_le :
          2 *
              ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                  ((((badVectorWitnessOfFactorFastCapLiftData
                        f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                      i.val 0 : ℝ) ^ 2)) *
                (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                  (BHKS.cldColumnNormBound
                    (Hex.normalizeForFactor f).squareFreeCore
                    (factorFastCapLiftData f primeData).p : ℝ))) +
            2 *
              (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                  (((factorFastCapLiftData f primeData).p : ℝ) ^
                    (2 *
                      ((factorFastCapLiftData f primeData).k -
                        Hex.bhksCoeffCutThreshold
                          (factorFastCapLiftData f primeData).p
                          (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
            2 *
                (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                  vectorSquareBound) *
                (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                  (BHKS.cldColumnNormBound
                    (Hex.normalizeForFactor f).squareFreeCore
                    (factorFastCapLiftData f primeData).p : ℝ)) +
              2 *
                (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
                  correctionWeightedBound) := by
        have hfirst :
            2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) ≤
              2 *
                (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                  vectorSquareBound) *
                (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                  (BHKS.cldColumnNormBound
                    (Hex.normalizeForFactor f).squareFreeCore
                    (factorFastCapLiftData f primeData).p : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hfirstTerm (by norm_num : (0 : ℝ) ≤ 2)
          linarith [this]
        have hsecond :
            2 *
              (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                  (((factorFastCapLiftData f primeData).p : ℝ) ^
                    (2 *
                      ((factorFastCapLiftData f primeData).k -
                        Hex.bhksCoeffCutThreshold
                          (factorFastCapLiftData f primeData).p
                          (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
            2 *
              (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
                correctionWeightedBound) :=
          mul_le_mul_of_nonneg_left hcorrectionWeightedSum (by norm_num : (0 : ℝ) ≤ 2)
        linarith [hfirst, hsecond]
      exact hsum_le.trans hauxiliaryBound_sq)
    hstrict hchoose hprecision

/--
Cap-arithmetic discharge of the strict comparison required by
`ofBridgeDataPointwiseAuxiliaryBounds`, given a paper-threshold-shape bound
on the `coeffL2NormBound ^ aux.natDegree * auxiliaryBound ^ input.natDegree`
product.

This composes the chain `paper-threshold ≤ factorFastPrecisionCap` (from
`bhksPaperThresholdReal_le_factorFastPrecisionCap`) with the strict
`2 * factorFastPrecisionCap f < p ^ k` from `precisionForCoeffBound_spec`
(applied via `precision_eq`), and with `p ^ k ≤ p ^ (k * localFactorDegree)`
for `0 < localFactorDegree`.  The prime lower bound is discharged from
`choose_eq` via `Hex.choosePrimeData?_prime`.
-/
theorem bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {auxiliaryBound : ℝ}
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    (Hex.ZPoly.coeffL2NormBound
          (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      auxiliaryBound ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ) := by
  have hp_two_le : 2 ≤ (factorFastCapLiftData f primeData).p :=
    (Hex.choosePrimeData?_prime _ _ hchoose).two_le
  have h_paper_le_cap :
      bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C ≤
        (Hex.factorFastPrecisionCap
          (Hex.normalizeForFactor f).squareFreeCore : ℝ) :=
    bhksPaperThresholdReal_le_factorFastPrecisionCap
      (Hex.normalizeForFactor f).squareFreeCore C hC_nonneg hC
  have h_spec :
      2 * Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore <
        (factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k := by
    rw [hprecision]
    exact Hex.precisionForCoeffBound_spec hp_two_le _
  have h_cap_lt_pk_nat :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore <
        (factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k := by
    omega
  have h_cap_lt_pk :
      (Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore : ℝ) <
        (((factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k : Nat) : ℝ) := by
    exact_mod_cast h_cap_lt_pk_nat
  have hp_one_nat : 1 ≤ (factorFastCapLiftData f primeData).p := by omega
  have hp_one : (1 : ℝ) ≤ ((factorFastCapLiftData f primeData).p : ℝ) := by
    exact_mod_cast hp_one_nat
  have h_kd :
      (factorFastCapLiftData f primeData).k ≤
        (factorFastCapLiftData f primeData).k * localFactorDegree :=
    Nat.le_mul_of_pos_right _ hlocalFactorDegree_pos
  have h_pk_le_pkd :
      ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k ≤
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          ((factorFastCapLiftData f primeData).k * localFactorDegree) :=
    pow_le_pow_right₀ hp_one h_kd
  have h_pk_cast :
      (((factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k : Nat) : ℝ) =
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k := by
    push_cast; rfl
  have step1 :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        (Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore : ℝ) :=
    hpaper.trans h_paper_le_cap
  have step2 :
      (Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore : ℝ) <
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k := by
    have := h_cap_lt_pk
    rw [h_pk_cast] at this
    exact this
  have step3 :
      ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k ≤
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          ((factorFastCapLiftData f primeData).k * localFactorDegree) :=
    h_pk_le_pkd
  exact (step1.trans_lt step2).trans_le step3

/--
Factored variant of `bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree`:
the caller supplies separate bounds on the two LHS factors of the BHKS
Theorem 5.2 paper-threshold inequality
(`coeffL2NormBound^aux.natDegree ≤ bhksPaperCoeffNormFactorReal core` and
`auxiliaryBound^input.natDegree ≤
bhksPaperDegreeFactorReal core * bhksPaperConstantFactorReal core C *
bhksPaperLogFactorReal core`), and the strict cap-arithmetic comparison is
discharged via `bhksPaperThresholdReal_ge_of_factored_bounds` composed with
the unfactored chain.

This lets a caller break down the genuine BHKS §5 inequality content into the
coefficient-power sub-bound against `‖core‖₂^(2n-1)` and the auxiliary-power
sub-bound against `n · (2C)^(n²) · (log ‖core‖₂)^n`, each of which is a
tractable analytic step.
-/
theorem bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    (Hex.ZPoly.coeffL2NormBound
          (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      auxiliaryBound ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ) := by
  have h_auxPow_nn :
      0 ≤ auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree :=
    pow_nonneg hauxiliaryBound_nonneg _
  have hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C :=
    bhksPaperThresholdReal_ge_of_factored_bounds
      (Hex.normalizeForFactor f).squareFreeCore C h_auxPow_nn h_coeff h_aux
  exact
    bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C hC_nonneg hC hpaper hchoose hprecision

/--
L2-norm-LHS sibling of
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree`: the LHS coefficient
factor is `‖core‖₂^aux.natDegree` (the real Euclidean norm of the source
polynomial) rather than `coeffL2NormBound^aux.natDegree` (the integer ceiling).
This matches the natural direction of the BHKS paper threshold factor
`bhksPaperCoeffNormFactorReal core = ‖core‖₂^(2n-1)`.

Callers who have the input l2-norm bound in real form (rather than via the
integer ceiling) consume the strict comparison via
`FactorFastCapLiftAnalyticComparison.ofL2normBounds` with the input bound
`inputBound := ‖core‖₂` and `hinput := le_refl _`.
-/
theorem bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_l2norm
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {auxiliaryBound : ℝ}
    (hpaper :
      (HexPolyZMathlib.l2norm
            (HexPolyZMathlib.toPolynomial
              (Hex.normalizeForFactor f).squareFreeCore)) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    (HexPolyZMathlib.l2norm
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      auxiliaryBound ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ) := by
  have hp_two_le : 2 ≤ (factorFastCapLiftData f primeData).p :=
    (Hex.choosePrimeData?_prime _ _ hchoose).two_le
  have h_paper_le_cap :
      bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C ≤
        (Hex.factorFastPrecisionCap
          (Hex.normalizeForFactor f).squareFreeCore : ℝ) :=
    bhksPaperThresholdReal_le_factorFastPrecisionCap
      (Hex.normalizeForFactor f).squareFreeCore C hC_nonneg hC
  have h_spec :
      2 * Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore <
        (factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k := by
    rw [hprecision]
    exact Hex.precisionForCoeffBound_spec hp_two_le _
  have h_cap_lt_pk_nat :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore <
        (factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k := by
    omega
  have h_cap_lt_pk :
      (Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore : ℝ) <
        (((factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k : Nat) : ℝ) := by
    exact_mod_cast h_cap_lt_pk_nat
  have hp_one_nat : 1 ≤ (factorFastCapLiftData f primeData).p := by omega
  have hp_one : (1 : ℝ) ≤ ((factorFastCapLiftData f primeData).p : ℝ) := by
    exact_mod_cast hp_one_nat
  have h_kd :
      (factorFastCapLiftData f primeData).k ≤
        (factorFastCapLiftData f primeData).k * localFactorDegree :=
    Nat.le_mul_of_pos_right _ hlocalFactorDegree_pos
  have h_pk_le_pkd :
      ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k ≤
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          ((factorFastCapLiftData f primeData).k * localFactorDegree) :=
    pow_le_pow_right₀ hp_one h_kd
  have h_pk_cast :
      (((factorFastCapLiftData f primeData).p ^
          (factorFastCapLiftData f primeData).k : Nat) : ℝ) =
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k := by
    push_cast; rfl
  have step1 :
      (HexPolyZMathlib.l2norm
            (HexPolyZMathlib.toPolynomial
              (Hex.normalizeForFactor f).squareFreeCore)) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        (Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore : ℝ) :=
    hpaper.trans h_paper_le_cap
  have step2 :
      (Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore : ℝ) <
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k := by
    have := h_cap_lt_pk
    rw [h_pk_cast] at this
    exact this
  have step3 :
      ((factorFastCapLiftData f primeData).p : ℝ) ^
          (factorFastCapLiftData f primeData).k ≤
        ((factorFastCapLiftData f primeData).p : ℝ) ^
          ((factorFastCapLiftData f primeData).k * localFactorDegree) :=
    h_pk_le_pkd
  exact (step1.trans_lt step2).trans_le step3

/--
L2-norm-LHS factored sibling of
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`: the LHS
coefficient factor is `‖core‖₂^aux.natDegree` rather than
`coeffL2NormBound^aux.natDegree`.

Combined with
`l2norm_pow_auxiliaryPolynomialWithCorrections_natDegree_le_bhksPaperCoeffNormFactorReal`
(which discharges the `h_coeff` hypothesis outright for any nonzero source
polynomial), the only remaining analytic content is the genuine BHKS Lemma 3.2
auxiliary-power sub-bound supplied through `h_aux`.
-/
theorem bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_l2norm_factored
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (h_coeff :
      (HexPolyZMathlib.l2norm
            (HexPolyZMathlib.toPolynomial
              (Hex.normalizeForFactor f).squareFreeCore)) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    (HexPolyZMathlib.l2norm
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      auxiliaryBound ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ) := by
  have h_auxPow_nn :
      0 ≤ auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree :=
    pow_nonneg hauxiliaryBound_nonneg _
  have hpaper :
      (HexPolyZMathlib.l2norm
            (HexPolyZMathlib.toPolynomial
              (Hex.normalizeForFactor f).squareFreeCore)) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C :=
    bhksPaperThresholdReal_ge_of_factored_bounds
      (Hex.normalizeForFactor f).squareFreeCore C h_auxPow_nn h_coeff h_aux
  exact
    bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_l2norm
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C hC_nonneg hC hpaper hchoose hprecision

/--
Named-auxiliary sibling of
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`: the
auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product `bhksPaperDegreeFactorReal core * bhksPaperConstantFactorReal core C *
bhksPaperLogFactorReal core`.

Implementation is a one-step shim that unfolds the named target and dispatches
to the unprimed `_factored` variant.  Callers proving the BHKS Theorem 5.2
auxiliary-power sub-bound directly against the packaged
`bhksPaperAuxiliaryFactorReal` definition can hit this RHS without unfolding.
-/
theorem bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored'
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (rows_pos :
      HasPositiveDimension
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData))
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    (Hex.ZPoly.coeffL2NormBound
          (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
      auxiliaryBound ^
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
    ((factorFastCapLiftData f primeData).p ^
      ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ) :=
  bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored
    f primeData rows_pos localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos C hC_nonneg hC hauxiliaryBound_nonneg h_coeff
    (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux) hchoose hprecision

/--
Build the cap-separation input package from a paper-threshold-shape bound on
the `coeffL2NormBound ^ aux.natDegree * auxiliaryBound ^ input.natDegree`
product.

This packages deliverables (2) and (3) of #6445: once the canonical
`coeffL2NormBound ^ aux.natDegree * auxiliaryBound ^ input.natDegree` is
bounded by `bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C`
(deliverable (1), the BHKS Theorem 5.2 inequality content), the strict
cap-arithmetic comparison required by `ofBridgeDataPointwiseAuxiliaryBounds` is
dispatched via `bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree`, and
the constructor returns the `FactorFastCapSeparationInputs` package consumed by
`factorFast_terminates`.

The remaining analytical content — bounding the canonical
`coeffL2NormBound ^ aux.natDegree * auxiliaryBound ^ input.natDegree` against
`bhksPaperThresholdReal` for the actual cap-lift bad-vector bridge — is left
as the `hpaper` hypothesis here.
-/
def ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataPointwiseAuxiliaryBounds localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    vectorSquareBound hvectorSquareBound correctionWeightedBound
    hcorrectionWeightedBound hauxiliaryBound_nonneg hauxiliaryBound_sq
    (bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C hC_nonneg hC hpaper hchoose hprecision)
    hchoose hprecision

/--
Factored sibling of `ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold`: the
caller supplies the two independent sub-bounds on the BHKS Theorem 5.2 LHS
factors (`coeffL2NormBound ^ aux.natDegree ≤ bhksPaperCoeffNormFactorReal core`
and `auxiliaryBound ^ input.natDegree ≤ bhksPaperDegreeFactorReal core *
bhksPaperConstantFactorReal core C * bhksPaperLogFactorReal core`) in place of
the combined paper-threshold inequality.

Composes `ofBridgeDataPointwiseAuxiliaryBounds` with the factored cap-arithmetic
chain `bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`; the
`auxiliaryBound`-nonneg hypothesis is the same one already required by the
pointwise constructor.
-/
def ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataPointwiseAuxiliaryBounds localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    vectorSquareBound hvectorSquareBound correctionWeightedBound
    hcorrectionWeightedBound hauxiliaryBound_nonneg hauxiliaryBound_sq
    (bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C hC_nonneg hC
      hauxiliaryBound_nonneg h_coeff h_aux hchoose hprecision)
    hchoose hprecision

/--
Named-auxiliary sibling of
`ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold`: the
auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
def ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold'
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold
    localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
    C hC_nonneg hC hcut bridge v hin hnot hcld
    vectorSquareBound hvectorSquareBound correctionWeightedBound
    hcorrectionWeightedBound hauxiliaryBound_nonneg hauxiliaryBound_sq
    h_coeff (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)
    hchoose hprecision

/--
Build the cap-separation input package from the structured corrected
auxiliary-l2-norm-squared bound combined with a paper-threshold-shape inequality
on the canonical
`coeffL2NormBound ^ aux.natDegree * auxiliaryBound ^ input.natDegree` product.

Composes `ofBridgeDataCorrectedAuxiliaryL2normSq` with
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree`, so the strict
cap-arithmetic comparison is dispatched internally once the caller supplies the
paper-threshold inequality (the BHKS Theorem 5.2 inequality content).  Compared
to `ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold`, this sibling
consumes the structured corrected RHS sum directly rather than deriving it from
pointwise vector/correction estimates; compared to
`ofBridgeDataAuxiliaryL2normAndPaperThreshold`, it keeps the structured
corrected-l2-norm-squared form rather than a direct `‖aux‖ ≤ auxiliaryBound`
bound.
-/
def ofBridgeDataCorrectedAuxiliaryL2normSqAndPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataCorrectedAuxiliaryL2normSq localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    hauxiliaryBound_nonneg hauxiliary_sq_bound
    (bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C hC_nonneg hC hpaper hchoose hprecision)
    hchoose hprecision

/--
Factored sibling of `ofBridgeDataCorrectedAuxiliaryL2normSqAndPaperThreshold`:
the caller supplies the two independent sub-bounds on the BHKS Theorem 5.2 LHS
factors (`coeffL2NormBound ^ aux.natDegree ≤ bhksPaperCoeffNormFactorReal core`
and `auxiliaryBound ^ input.natDegree ≤ bhksPaperDegreeFactorReal core *
bhksPaperConstantFactorReal core C * bhksPaperLogFactorReal core`) in place of
the combined paper-threshold inequality.

Composes `ofBridgeDataCorrectedAuxiliaryL2normSq` with the factored
cap-arithmetic chain
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`; the
`auxiliaryBound`-nonneg hypothesis is the same one already required by the
structured-corrected-l2-norm-squared constructor.
-/
def ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataCorrectedAuxiliaryL2normSq localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    hauxiliaryBound_nonneg hauxiliary_sq_bound
    (bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C hC_nonneg hC
      hauxiliaryBound_nonneg h_coeff h_aux hchoose hprecision)
    hchoose hprecision

/--
Named-auxiliary sibling of
`ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold`: the
auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
def ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold'
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold
    localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
    C hC_nonneg hC hcut bridge v hin hnot hcld
    hauxiliaryBound_nonneg hauxiliary_sq_bound
    h_coeff (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)
    hchoose hprecision

/--
Build the cap-separation input package from a direct `‖aux‖ ≤ auxiliaryBound`
estimate.

This is a thinner sibling of `ofBridgeDataCorrectedAuxiliaryL2normSq`: rather
than asking the caller to bound the structured corrected-RHS sum, it takes the
already-derived l2norm bound directly and routes through `ofBridgeData` after
upgrading the bound via
`factorFastCapLift_l2norm_product_lt_divisor_of_auxiliary_bound`. The
input-side `coeffL2NormBound` bound is discharged automatically.
-/
def ofBridgeDataAuxiliaryL2norm
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (hstrict :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree <
        ((factorFastCapLiftData f primeData).p ^
          ((factorFastCapLiftData f primeData).k * localFactorDegree) : ℝ))
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeData localFactorIndex localFactorDegree H cap_le C C_nonneg C_le_two
    cut bridge choose_eq precision_eq
    (factorFastCapLift_l2norm_product_lt_divisor_of_auxiliary_bound
      f primeData rows_pos localFactorIndex localFactorDegree H hauxiliary hstrict)

/--
Build the cap-separation input package from a direct `‖aux‖ ≤ auxiliaryBound`
estimate combined with a paper-threshold-shape bound on the
`coeffL2NormBound ^ aux.natDegree * auxiliaryBound ^ input.natDegree` product.

Composes `ofBridgeDataAuxiliaryL2norm` with the cap-arithmetic chain
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree`, so the strict
cap-arithmetic comparison is dispatched internally once the caller supplies the
paper-threshold inequality (the BHKS Theorem 5.2 inequality content).
-/
def ofBridgeDataAuxiliaryL2normAndPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataAuxiliaryL2norm localFactorIndex localFactorDegree H cap_le
    C C_nonneg C_le_two cut bridge hauxiliary
    (bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C C_nonneg C_le_two hpaper choose_eq precision_eq)
    choose_eq precision_eq

/--
Factored sibling of `ofBridgeDataAuxiliaryL2normAndPaperThreshold`: the caller
supplies the two independent sub-bounds on the BHKS Theorem 5.2 LHS factors
(`coeffL2NormBound ^ aux.natDegree ≤ bhksPaperCoeffNormFactorReal core` and
`auxiliaryBound ^ input.natDegree ≤ bhksPaperDegreeFactorReal core *
bhksPaperConstantFactorReal core C * bhksPaperLogFactorReal core`) in place of
the combined paper-threshold inequality.

Composes `ofBridgeDataAuxiliaryL2norm` with the factored cap-arithmetic chain
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`.  The
`auxiliaryBound`-nonneg hypothesis required by the factored chain is derived
internally from `hauxiliary` via the non-negativity of `l2norm`.

This lets a caller break the BHKS §5 inequality content into the
coefficient-power sub-bound against `‖core‖₂^(2n-1)` and the auxiliary-power
sub-bound against `n · (2C)^(n²) · (log ‖core‖₂)^n` without re-deriving the
combined product inequality.
-/
def ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  have hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound :=
    le_trans (by unfold HexPolyZMathlib.l2norm; exact Real.sqrt_nonneg _) hauxiliary
  ofBridgeDataAuxiliaryL2norm localFactorIndex localFactorDegree H cap_le
    C C_nonneg C_le_two cut bridge hauxiliary
    (bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored
      f primeData rows_pos localFactorIndex localFactorDegree H
      hlocalFactorDegree_pos C C_nonneg C_le_two
      hauxiliaryBound_nonneg h_coeff h_aux choose_eq precision_eq)
    choose_eq precision_eq

/--
Named-auxiliary sibling of `ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold`:
the auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
def ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold'
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold
    localFactorIndex localFactorDegree H hlocalFactorDegree_pos cap_le
    C C_nonneg C_le_two cut bridge hauxiliary
    h_coeff (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)
    choose_eq precision_eq

/--
Build the cap-separation input package from the bridge data alone, taking the
auxiliary-l2 bound directly from the bridge-derived
`Real.sqrt` of the structured corrected RHS sum, plus the paper-threshold-shape
inequality on `coeffL2NormBound ^ aux.natDegree * Real.sqrt RHS ^ input.natDegree`.

Compared to `ofBridgeDataAuxiliaryL2normAndPaperThreshold`, the caller no
longer supplies an `auxiliaryBound` parameter or a separate `‖aux‖ ≤
auxiliaryBound` hypothesis: both are derived internally from the bridge via
`BadVectorBridgeData.auxiliaryPolynomial_l2norm_le_sqrt_of_bridge_data`. The
caller still supplies the CLD-coefficient bound `hcld`, the projected vector
`v` together with `hin`/`hnot`, and the paper-threshold inequality.
-/
noncomputable def ofBridgeDataAndPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        Real.sqrt
            (2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) +
              2 *
                (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                  (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                    (((factorFastCapLiftData f primeData).p : ℝ) ^
                      (2 *
                        ((factorFastCapLiftData f primeData).k -
                          Hex.bhksCoeffCutThreshold
                            (factorFastCapLiftData f primeData).p
                            (Hex.normalizeForFactor f).squareFreeCore j)))))) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataAuxiliaryL2normAndPaperThreshold localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos cap_le C C_nonneg C_le_two cut bridge
    (auxiliaryBound := Real.sqrt _)
    (bridge.auxiliaryPolynomial_l2norm_le_sqrt_of_bridge_data v hin hnot hcld)
    hpaper choose_eq precision_eq

/--
Factored sibling of `ofBridgeDataAndPaperThreshold`: the caller supplies the two
independent sub-bounds on the BHKS Theorem 5.2 LHS factors
(`coeffL2NormBound ^ aux.natDegree ≤ bhksPaperCoeffNormFactorReal core` and
`(Real.sqrt RHS) ^ input.natDegree ≤ bhksPaperDegreeFactorReal core *
bhksPaperConstantFactorReal core C * bhksPaperLogFactorReal core`, where `RHS`
is the structured corrected RHS sum derived from the bridge) in place of the
combined paper-threshold inequality.

Composes `ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold` by routing the
bridge-derived `‖aux‖ ≤ Real.sqrt RHS` bound through the factored cap-arithmetic
chain `bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`.  The
caller no longer supplies an `auxiliaryBound` parameter or a separate `‖aux‖ ≤
auxiliaryBound` hypothesis: both are derived internally from the bridge.
-/
noncomputable def ofBridgeDataAndFactoredPaperThreshold
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      Real.sqrt
            (2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) +
              2 *
                (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                  (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                    (((factorFastCapLiftData f primeData).p : ℝ) ^
                      (2 *
                        ((factorFastCapLiftData f primeData).k -
                          Hex.bhksCoeffCutThreshold
                            (factorFastCapLiftData f primeData).p
                            (Hex.normalizeForFactor f).squareFreeCore j)))))) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos cap_le C C_nonneg C_le_two cut bridge
    (auxiliaryBound := Real.sqrt _)
    (bridge.auxiliaryPolynomial_l2norm_le_sqrt_of_bridge_data v hin hnot hcld)
    h_coeff h_aux choose_eq precision_eq

/--
Named-auxiliary sibling of `ofBridgeDataAndFactoredPaperThreshold`: the
auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
noncomputable def ofBridgeDataAndFactoredPaperThreshold'
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (localFactorIndex localFactorDegree : Nat) (H : Hex.ZPoly)
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (cap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (C_nonneg : 0 ≤ C) (C_le_two : C ≤ 2)
    (cut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      Real.sqrt
            (2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) +
              2 *
                (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                  (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                    (((factorFastCapLiftData f primeData).p : ℝ) ^
                      (2 *
                        ((factorFastCapLiftData f primeData).k -
                          Hex.bhksCoeffCutThreshold
                            (factorFastCapLiftData f primeData).p
                            (Hex.normalizeForFactor f).squareFreeCore j)))))) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (choose_eq :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (precision_eq :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p) :
    FactorFastCapSeparationInputs f primeData rows_pos trueSupports :=
  ofBridgeDataAndFactoredPaperThreshold
    localFactorIndex localFactorDegree H hlocalFactorDegree_pos cap_le
    C C_nonneg C_le_two cut bridge v hin hnot hcld
    h_coeff
    (bhksPaperAuxiliaryFactorReal_eq_product
      (Hex.normalizeForFactor f).squareFreeCore C ▸ h_aux)
    choose_eq precision_eq

/--
Closed actual-cap `L' = W` identification at `factorFastCapLiftData f primeData`.

This is the lattice-identification accessor produced by the
`FactorFastCapSeparationInputs` package: the packaged `BadVectorBridgeData`,
cut hypotheses, analytic comparison, and cap-precision dominance are composed
with `projectedRowSpan_eq_trueFactorIndicatorLattice_of_factorFastCapLift_bridge`
to expose the BHKS `L' = W` conclusion for the canonical true-factor supports
without asking the caller to re-thread the bridge fields. The prime-lower bound
`0 < (factorFastCapLiftData f primeData).p` required by the bridge derivation is
discharged internally from `choose_eq` via `Hex.choosePrimeData?_prime`.
-/
theorem latticeIdentification
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (capInputs : FactorFastCapSeparationInputs f primeData rows_pos trueSupports) :
    BHKS.projectedRowSpanInt
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos) =
      BHKS.trueFactorIndicatorLattice trueSupports :=
  projectedRowSpan_eq_trueFactorIndicatorLattice_of_factorFastCapLift_bridge
    f primeData rows_pos capInputs.localFactorIndex capInputs.localFactorDegree
    capInputs.H trueSupports capInputs.cap_le capInputs.C capInputs.C_nonneg
    capInputs.C_le_two capInputs.cut capInputs.bridge
    (by
      have h2 : 2 ≤ (factorFastCapLiftData f primeData).p :=
        (Hex.choosePrimeData?_prime _ _ capInputs.choose_eq).two_le
      omega)
    capInputs.comparison

end FactorFastCapSeparationInputs

namespace CanonicalRecoveryInputs

/--
Closed `CanonicalRecoveryInputs` constructor from the actual `factorFast` cap
branch.

Combines `FactorFastCapSeparationInputs` (which supplies the cap-side
`BadVectorBridgeData`, cut/comparison data, and the prime-choice/precision
equations) with `CanonicalRecoveryTailInputs` (which supplies the recovery-side
canonical-support shape facts, the expected true-factor package, and the
per-class Mignotte product congruences). The `lattice_eq_indicators` field is
derived internally via `FactorFastCapSeparationInputs.latticeIdentification`,
so the caller does not have to re-thread the bridge-data composition.

The resulting record feeds directly into
`factorFast_ne_none_of_canonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound`,
matching the canonical final-theorem consumer shape.
-/
def ofFactorFastCapSeparationInputsAndCanonicalRecoveryTailInputs
    {f : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {rows_pos : HasPositiveDimension
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)}
    {trueSupports : Set (Set (Fin (projectedRowsOfLiftData
      (Hex.normalizeForFactor f).squareFreeCore
      (factorFastCapLiftData f primeData)
      rows_pos).factorCount))}
    (capInputs : FactorFastCapSeparationInputs f primeData rows_pos trueSupports)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    CanonicalRecoveryInputs f primeData where
  rows_pos := rows_pos
  trueSupports := trueSupports
  lattice_eq_indicators := capInputs.latticeIdentification
  projected_nonempty := recoveryInputs.projected_nonempty
  classes_two := recoveryInputs.classes_two
  class_nonempty := recoveryInputs.class_nonempty
  class_bounds := recoveryInputs.class_bounds
  hf_ne_zero := recoveryInputs.hf_ne_zero
  expectedFactors := recoveryInputs.expectedFactors
  expected_true_factors := recoveryInputs.expected_true_factors
  product_congr := recoveryInputs.product_congr

end CanonicalRecoveryInputs

/-- Final canonical-supports recovery wrapper at the `factorFast` cap lift.

Composes
`factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`
with a packaged `CanonicalRecoveryInputs` record, hiding the canonical
input plumbing behind a single bundle. -/
theorem factorFast_ne_none_of_canonicalRecoveryInputs
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hp : 2 ≤ (factorFastCapLiftData f primeData).p)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (inputs : CanonicalRecoveryInputs f primeData) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound
    f primeData inputs.rows_pos inputs.trueSupports inputs.lattice_eq_indicators
    hB_pos hchoose hp hk inputs.projected_nonempty inputs.classes_two
    inputs.class_nonempty inputs.class_bounds inputs.expectedFactors
    inputs.hf_ne_zero inputs.expected_true_factors inputs.product_congr

/--
Variant of `factorFast_ne_none_of_canonicalRecoveryInputs` that internalizes
the two easy executable side conditions: cap positivity and the selected
prime lower bound.  This is the narrowest packaged canonical-recovery surface
for the current executable final assembly: callers provide the prime-choice
equation, the executable precision equation, and the mathematical
`CanonicalRecoveryInputs` package.
-/
theorem factorFast_ne_none_of_canonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound
    (f : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (inputs : CanonicalRecoveryInputs f primeData) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_canonicalRecoveryInputs
    f primeData
    (one_le_factorFastPrecisionCap f)
    hchoose
    (Hex.choosePrimeData?_prime _ _ hchoose).two_le
    hk inputs

/--
Variant of
`factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`
that internalizes the `1 ≤ Hex.factorFastPrecisionCap f` side condition via
`HexBerlekampZassenhausMathlib.one_le_factorFastPrecisionCap`, which holds
unconditionally for every `f`. Removing this argument trims the conditional
final assembly surface.
-/
theorem factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalCapPositive
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
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hp : 2 ≤ (factorFastCapLiftData f primeData).p)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (hprojected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (hclasses_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hclass_nonempty :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∃ j, j ∈ members)
    (hclass_bounds :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∀ j, j ∈ members →
          j < (factorFastCapLiftData f primeData).liftedFactors.size)
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (htrue :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports lattice_eq_indicators
    (one_le_factorFastPrecisionCap f)
    hchoose hp hk hprojected_nonempty hclasses_two
    hclass_nonempty hclass_bounds expectedFactors hf_ne_zero htrue hproduct

/--
Bridge-data form of
`factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`.

This wrapper composes the cap-lift cap-separation packaging supplied by
`projectedRowSpan_eq_trueFactorIndicatorLattice_of_factorFastCapLift_bridge`
with the canonical-support recovery wrapper: callers provide the
`BadVectorBridgeData` plus the cut and analytic-comparison side conditions,
and the theorem assembles the `lattice_eq_indicators` field internally rather
than asking the caller to instantiate the projected-row-span equality
themselves.

The remaining recovery facts -- support partition shape, `ExpectedTrueFactors`
package, and the per-class Mignotte product congruences -- are passed through
unchanged from the canonical-support wrapper. These are the genuinely
mathematical inputs still produced by the open D1 prerequisites (#6344,
#6345); this wrapper only narrows the cap-separation side of the assembly so
that the eventual final theorem call site needs one fewer manual lattice
identification step.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hp : 2 ≤ (factorFastCapLiftData f primeData).p)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (hprojected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (hclasses_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hclass_nonempty :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∃ j, j ∈ members)
    (hclass_bounds :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∀ j, j ∈ members →
          j < (factorFastCapLiftData f primeData).liftedFactors.size)
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (htrue :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_mignottePrecisionCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports
    (projectedRowSpan_eq_trueFactorIndicatorLattice_of_factorFastCapLift_bridge
      f primeData rows_pos localFactorIndex localFactorDegree H trueSupports
      hcap_le C hC_nonneg hC hcut bridge (by omega) hcomparison)
    hB_pos hchoose hp hk hprojected_nonempty hclasses_two hclass_nonempty
    hclass_bounds expectedFactors hf_ne_zero htrue hproduct

/--
Variant of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`
that internalises the `2 ≤ (factorFastCapLiftData f primeData).p` side
condition.

The lower bound is derived from `hchoose` via `Hex.choosePrimeData?_prime`
and `Nat.Prime.two_le`, exploiting that `(factorFastCapLiftData f primeData).p`
unfolds definitionally to `primeData.p`. All other hypotheses are passed
through unchanged.

This narrows the caller obligations on the cap-separation side of the HO-4
final assembly: once #6344/#6345 land the genuine mathematical recovery
inputs, the conditional `factorFast` success composition needs one fewer
trivially-derivable prime-lower-bound discharge step.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalPrimeLowerBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hB_pos : 1 ≤ Hex.factorFastPrecisionCap f)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (hprojected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (hclasses_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hclass_nonempty :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∃ j, j ∈ members)
    (hclass_bounds :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∀ j, j ∈ members →
          j < (factorFastCapLiftData f primeData).liftedFactors.size)
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (htrue :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge hcomparison hB_pos hchoose
    (Hex.choosePrimeData?_prime _ _ hchoose).two_le
    hk hprojected_nonempty hclasses_two hclass_nonempty hclass_bounds
    expectedFactors hf_ne_zero htrue hproduct

/--
Variant of
`factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound`
that internalises both easy executable-cap side conditions:
`1 ≤ factorFastPrecisionCap f` and
`2 ≤ (factorFastCapLiftData f primeData).p`.

This is the canonical-support counterpart to the indicator-side
`_internalCapPositiveAndPrimeLowerBound` wrapper above.  It keeps the final
assembly surface focused on the support partition facts, expected true-factor
package, and per-class Mignotte product congruences.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (hprojected_nonempty :
      (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).projectedRows.isEmpty = false)
    (hclasses_two :
      2 ≤ (supportPartitionByMinColumn trueSupports).length)
    (hclass_nonempty :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∃ j, j ∈ members)
    (hclass_bounds :
      ∀ members, members ∈ supportPartitionByMinColumn trueSupports →
        ∀ j, j ∈ members →
          j < (factorFastCapLiftData f primeData).liftedFactors.size)
    (expectedFactors : Array Hex.ZPoly)
    (hf_ne_zero : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (htrue :
      ForwardRecoveryInputs.ExpectedTrueFactors
        (Hex.normalizeForFactor f).squareFreeCore
        (expectedIndicatorArrayOfSupports trueSupports) expectedFactors)
    (hproduct :
      ∀ i, i < (expectedIndicatorArrayOfSupports trueSupports).size →
        Hex.ZPoly.reduceModPow
            (Hex.DensePoly.scale
              (Hex.DensePoly.leadingCoeff
                (Hex.normalizeForFactor f).squareFreeCore)
              (Array.polyProduct
                ((ForwardRecoveryInputs.selectedFactorArraysOfSupports
                  (factorFastCapLiftData f primeData).liftedFactors
                  trueSupports).getD i #[])))
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k =
          Hex.ZPoly.reduceModPow (expectedFactors.getD i 0)
            (factorFastCapLiftData f primeData).p
            (factorFastCapLiftData f primeData).k) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalPrimeLowerBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge hcomparison
    (one_le_factorFastPrecisionCap f) hchoose hk hprojected_nonempty
    hclasses_two hclass_nonempty hclass_bounds expectedFactors hf_ne_zero
    htrue hproduct

/--
Packaged canonical-support tail-input wrapper for the actual-cap
`BadVectorBridgeData` assembly.

This theorem is the support-side analogue of the earlier packaged
`CanonicalRecoveryInputs` wrapper, but leaves the lattice identification to
cap separation: `BadVectorBridgeData` plus the cut and analytic comparison
derive `L' = W`, while `CanonicalRecoveryTailInputs` carries exactly the
remaining recovery facts.
-/
theorem factorFast_ne_none_of_capSeparationBridgeDataCanonicalRecoveryTailInputs_internalCapPositiveAndPrimeLowerBound
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
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (hcomparison :
      FactorFastCapLiftAnalyticComparison
        f primeData rows_pos localFactorIndex localFactorDegree H)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hk :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (inputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalSupportsExpectedFactorsAtPrecisionForCoeffBound_internalCapPositiveAndPrimeLowerBound
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hcap_le C hC_nonneg hC hcut bridge hcomparison hchoose hk
    inputs.projected_nonempty inputs.classes_two inputs.class_nonempty
    inputs.class_bounds inputs.expectedFactors inputs.hf_ne_zero
    inputs.expected_true_factors inputs.product_congr

/--
Fully packaged actual-cap wrapper for the current HO-4 assembly surface.

`FactorFastCapSeparationInputs` carries the cap-separation producer side, and
`CanonicalRecoveryTailInputs` carries the canonical-support recovery tail.  The
wrapper is intentionally additive: it does not prove the remaining
mathematical providers, but fixes their final call shape for the conditional
public success theorem under the packaged `choosePrimeData?` witness.
-/
theorem factorFast_ne_none_of_factorFastCapSeparationInputsCanonicalRecoveryTailInputs
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
    (capInputs :
      FactorFastCapSeparationInputs f primeData rows_pos trueSupports)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_capSeparationBridgeDataCanonicalRecoveryTailInputs_internalCapPositiveAndPrimeLowerBound
    f primeData rows_pos trueSupports capInputs.localFactorIndex
    capInputs.localFactorDegree capInputs.H capInputs.cap_le capInputs.C
    capInputs.C_nonneg capInputs.C_le_two capInputs.cut capInputs.bridge
    capInputs.comparison capInputs.choose_eq capInputs.precision_eq
    recoveryInputs

/--
Final fast-branch wrapper threading the closed `CanonicalRecoveryInputs`
constructor.

`CanonicalRecoveryInputs.ofFactorFastCapSeparationInputsAndCanonicalRecoveryTailInputs`
assembles the canonical-support recovery inputs from `FactorFastCapSeparationInputs`
plus `CanonicalRecoveryTailInputs`; this wrapper feeds that record directly into
`factorFast_ne_none_of_canonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound`,
which exposes the `factorFast f ≠ none` conclusion via the
`CanonicalRecoveryInputs` consumer shape.

This is the canonical-input-package counterpart of
`factorFast_ne_none_of_factorFastCapSeparationInputsCanonicalRecoveryTailInputs`,
which routes through the disparate cap-separation / recovery-tail arguments
without ever materialising a `CanonicalRecoveryInputs` value. Both wrappers
have the same conclusion and consume the same two packaged input records.
-/
theorem factorFast_ne_none_of_factorFastCapSeparationInputsAndCanonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound
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
    (capInputs :
      FactorFastCapSeparationInputs f primeData rows_pos trueSupports)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_canonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound
    f primeData capInputs.choose_eq capInputs.precision_eq
    (CanonicalRecoveryInputs.ofFactorFastCapSeparationInputsAndCanonicalRecoveryTailInputs
      capInputs recoveryInputs)

/--
Final BHKS D1 assembly target: the public fast path returns `some _` whenever
the prime-search-safe preconditions packaged as `FactorFastCapSeparationInputs`
(cap-separation producer side) and `CanonicalRecoveryTailInputs`
(canonical-support recovery tail) are available.

This is the prime-search-safe bridge toward the hypothesis-free
`∀ f, Hex.factorFast f ≠ none` target named in
`SPEC/Libraries/hex-berlekamp-zassenhaus.md` Group D / D1. The required
`Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData`
witness is stored in `capInputs.choose_eq`; together with the cap-separation
and canonical-recovery tail packages, it proves the public
`Hex.factorFast f ≠ none` conclusion for that selected prime. The remaining D2
leaf theorem removes this explicit prime-search witness on primitive
square-free inputs.

The proof composes the existing assembly chain: routing through
`factorFast_ne_none_of_factorFastCapSeparationInputsAndCanonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound`
discharges the BHKS branch by deriving the closed `CanonicalRecoveryInputs`
package and then handing off to
`factorFast_ne_none_of_canonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound`,
which threads through `factorFast_ne_none_of_core_recovery_on_schedule`.
That inner case-split on `factorFastFactorsWithBound` at
`Hex.factorFastPrecisionCap f` discharges the constant, small-mod-singleton,
and quadratic short-circuit branches by their unconditional `some _`
returns, and the nontrivial BHKS branch by the recovery-on-schedule witness
extracted from the closed packages.
-/
theorem factorFast_terminates
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
    (capInputs :
      FactorFastCapSeparationInputs f primeData rows_pos trueSupports)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_ne_none_of_factorFastCapSeparationInputsAndCanonicalRecoveryInputs_internalCapPositiveAndPrimeLowerBound
    f primeData rows_pos trueSupports capInputs recoveryInputs

/--
SPEC D1 named wrapper: once the executable prime search succeeds, select its
`PrimeChoiceData` witness and apply the packaged BHKS/recovery assembly for
that witness.

The remaining arguments are provider functions for the selected executable
prime. They are exactly the mathematical packages consumed by
`factorFast_terminates`; this wrapper only aligns the final surface with the
`choosePrimeData? ≠ none → factorFast ≠ none` entry point.
-/
theorem factorFast_terminates_of_choosePrimeData
    (f : Hex.ZPoly)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore ≠ none)
    (rows_pos :
      ∀ primeData,
        Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
            some primeData →
          HasPositiveDimension
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData))
    (trueSupports :
      ∀ primeData
        (hselected :
          Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
            some primeData),
        Set (Set (Fin (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          (rows_pos primeData hselected)).factorCount)))
    (capInputs :
      ∀ primeData
        (hselected :
          Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
            some primeData),
        FactorFastCapSeparationInputs f primeData
          (rows_pos primeData hselected)
          (trueSupports primeData hselected))
    (recoveryInputs :
      ∀ primeData
        (hselected :
          Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
            some primeData),
        CanonicalRecoveryTailInputs f primeData
          (rows_pos primeData hselected)
          (trueSupports primeData hselected)) :
    Hex.factorFast f ≠ none := by
  cases hselected :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore with
  | none =>
      exact False.elim (hchoose hselected)
  | some primeData =>
      exact
        factorFast_terminates f primeData
          (rows_pos primeData hselected)
          (trueSupports primeData hselected)
          (capInputs primeData hselected)
          (recoveryInputs primeData hselected)

/--
Final HO-4 wrapper threading the pointwise auxiliary bounds plus paper-threshold
ingredients directly to the public success conclusion.

This composes `FactorFastCapSeparationInputs.ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold`
(which packages the BHKS pointwise vector/correction bounds, paper-threshold
shape hypothesis, prime-choice equation, and stored precision equation into the
cap-separation input record) with `factorFast_terminates` (which combines the
cap-separation record with the canonical-support recovery tail).  Callers thus
provide only the bridge data, the projected vector in `L' \ W`, the CLD column
bounds, the pointwise vector/correction estimates, the `auxiliaryBound`
squared-sum bound, the paper-threshold-shape estimate, the executable
precision/prime-choice equations, and the canonical-recovery tail package.
-/
theorem factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge v hin hnot hcld
      vectorSquareBound hvectorSquareBound correctionWeightedBound
      hcorrectionWeightedBound hauxiliaryBound_nonneg hauxiliaryBound_sq
      hpaper hchoose hprecision)
    recoveryInputs

/--
Final HO-4 wrapper threading pointwise vector/correction estimates plus the
two factored BHKS Theorem 5.2 LHS sub-bounds straight to
`Hex.factorFast f ≠ none`.

This composes
`FactorFastCapSeparationInputs.ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold`
(which builds the cap-separation record from pointwise vector/correction
bounds and the factored paper-threshold sub-bounds, dispatching the
cap-arithmetic chain internally via
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`) with
`factorFast_terminates`.  Compared to
`factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold`,
the caller supplies the two independent BHKS Theorem 5.2 sub-bounds
(`coeffL2NormBound ^ aux.natDegree ≤ bhksPaperCoeffNormFactorReal core` and
`auxiliaryBound ^ input.natDegree ≤ bhksPaperDegreeFactorReal core *
bhksPaperConstantFactorReal core C * bhksPaperLogFactorReal core`) rather than
the combined product inequality.
-/
theorem factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge v hin hnot hcld
      vectorSquareBound hvectorSquareBound correctionWeightedBound
      hcorrectionWeightedBound hauxiliaryBound_nonneg hauxiliaryBound_sq
      h_coeff h_aux hchoose hprecision)
    recoveryInputs

/--
Named-auxiliary sibling of
`factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold`:
the auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
theorem factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold'
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (vectorSquareBound : ℝ)
    (hvectorSquareBound :
      ∀ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
        ((((badVectorWitnessOfFactorFastCapLiftData
              f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
            i.val 0 : ℝ) ^ 2) ≤ vectorSquareBound)
    (correctionWeightedBound : ℝ)
    (hcorrectionWeightedBound :
      ∀ j, j < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 →
        (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
          (((factorFastCapLiftData f primeData).p : ℝ) ^
            (2 *
              ((factorFastCapLiftData f primeData).k -
                Hex.bhksCoeffCutThreshold
                  (factorFastCapLiftData f primeData).p
                  (Hex.normalizeForFactor f).squareFreeCore j)))) ≤
          correctionWeightedBound)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliaryBound_sq :
      2 *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              vectorSquareBound) *
          (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
            (BHKS.cldColumnNormBound
              (Hex.normalizeForFactor f).squareFreeCore
              (factorFastCapLiftData f primeData).p : ℝ)) +
        2 *
          (((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 : ℝ) *
            correctionWeightedBound) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndFactoredPaperThreshold
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    vectorSquareBound hvectorSquareBound correctionWeightedBound
    hcorrectionWeightedBound hauxiliaryBound_nonneg hauxiliaryBound_sq
    h_coeff (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)
    hchoose hprecision recoveryInputs

/--
Final HO-4 wrapper threading the structured corrected auxiliary-l2-norm-squared
bound plus the paper-threshold-shape inequality straight to
`Hex.factorFast f ≠ none`.

This composes
`FactorFastCapSeparationInputs.ofBridgeDataCorrectedAuxiliaryL2normSqAndPaperThreshold`
(which builds the cap-separation record from the structured corrected RHS sum
bound and the paper-threshold inequality, dispatching the cap-arithmetic chain
internally) with `factorFast_terminates` (which combines the cap-separation
record with the canonical-support recovery tail).  Compared to
`factorFast_terminates_ofBridgeDataPointwiseAuxiliaryBoundsAndPaperThreshold`,
the caller supplies the structured corrected RHS sum directly rather than
pointwise vector/correction estimates; compared to
`factorFast_terminates_ofBridgeDataAuxiliaryL2normAndPaperThreshold`, the
caller stays in the structured corrected-l2-norm-squared form rather than
collapsing to a direct `‖aux‖ ≤ auxiliaryBound` bound.
-/
theorem factorFast_terminates_ofBridgeDataCorrectedAuxiliaryL2normSqAndPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataCorrectedAuxiliaryL2normSqAndPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge v hin hnot hcld
      hauxiliaryBound_nonneg hauxiliary_sq_bound hpaper hchoose hprecision)
    recoveryInputs

/--
Final HO-4 wrapper threading the structured corrected auxiliary-l2-norm-squared
bound plus the two factored BHKS Theorem 5.2 LHS sub-bounds straight to
`Hex.factorFast f ≠ none`.

This composes
`FactorFastCapSeparationInputs.ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold`
(which builds the cap-separation record from the structured corrected RHS sum
bound and the factored paper-threshold sub-bounds, dispatching the
cap-arithmetic chain internally via
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`) with
`factorFast_terminates`.  Compared to
`factorFast_terminates_ofBridgeDataCorrectedAuxiliaryL2normSqAndPaperThreshold`,
the caller supplies the two independent BHKS Theorem 5.2 sub-bounds rather
than the combined product inequality.
-/
theorem factorFast_terminates_ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge v hin hnot hcld
      hauxiliaryBound_nonneg hauxiliary_sq_bound h_coeff h_aux hchoose hprecision)
    recoveryInputs

/--
Named-auxiliary sibling of
`factorFast_terminates_ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold`:
the auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
theorem factorFast_terminates_ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold'
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    {auxiliaryBound : ℝ}
    (hauxiliaryBound_nonneg : 0 ≤ auxiliaryBound)
    (hauxiliary_sq_bound :
      2 *
          ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
              ((((badVectorWitnessOfFactorFastCapLiftData
                    f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                  i.val 0 : ℝ) ^ 2)) *
            (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
              (BHKS.cldColumnNormBound
                (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p : ℝ))) +
        2 *
          (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
            (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
              (((factorFastCapLiftData f primeData).p : ℝ) ^
                (2 *
                  ((factorFastCapLiftData f primeData).k -
                    Hex.bhksCoeffCutThreshold
                      (factorFastCapLiftData f primeData).p
                      (Hex.normalizeForFactor f).squareFreeCore j))))) ≤
        auxiliaryBound ^ 2)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates_ofBridgeDataCorrectedAuxiliaryL2normSqAndFactoredPaperThreshold
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    hauxiliaryBound_nonneg hauxiliary_sq_bound
    h_coeff (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)
    hchoose hprecision recoveryInputs

/--
Final HO-4 wrapper threading a direct `‖aux‖ ≤ auxiliaryBound` estimate plus
the paper-threshold-shape inequality straight to `Hex.factorFast f ≠ none`.

This composes
`FactorFastCapSeparationInputs.ofBridgeDataAuxiliaryL2normAndPaperThreshold`
(which builds the cap-separation record from the direct l2norm bound and the
paper-threshold inequality, dispatching the cap-arithmetic chain internally)
with `factorFast_terminates` (which combines the cap-separation record with
the canonical-support recovery tail). Callers therefore supply only the
bridge data, the direct auxiliary l2norm bound, the paper-threshold
inequality, the executable precision/prime-choice equations, and the
canonical-recovery tail package, without exposing the intermediate
`FactorFastCapSeparationInputs` record or the structured corrected-RHS sum
hypotheses required by the pointwise wrapper.
-/
theorem factorFast_terminates_ofBridgeDataAuxiliaryL2normAndPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataAuxiliaryL2normAndPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge hauxiliary hpaper hchoose hprecision)
    recoveryInputs

/--
Final HO-4 wrapper threading a direct `‖aux‖ ≤ auxiliaryBound` estimate plus
the two factored sub-bounds on the BHKS Theorem 5.2 LHS factors straight to
`Hex.factorFast f ≠ none`.

This composes
`FactorFastCapSeparationInputs.ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold`
(which builds the cap-separation record from the direct l2norm bound and the
factored paper-threshold sub-bounds, dispatching the cap-arithmetic chain
internally via `bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`)
with `factorFast_terminates`.  Compared to
`factorFast_terminates_ofBridgeDataAuxiliaryL2normAndPaperThreshold`, the
caller supplies the two independent BHKS Theorem 5.2 sub-bounds
(`coeffL2NormBound ^ aux.natDegree ≤ bhksPaperCoeffNormFactorReal core` and
`auxiliaryBound ^ input.natDegree ≤ bhksPaperDegreeFactorReal core *
bhksPaperConstantFactorReal core C * bhksPaperLogFactorReal core`) rather than
the combined product inequality.
-/
theorem factorFast_terminates_ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge hauxiliary h_coeff h_aux hchoose hprecision)
    recoveryInputs

/--
Named-auxiliary sibling of
`factorFast_terminates_ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold`:
the auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
theorem factorFast_terminates_ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold'
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    {auxiliaryBound : ℝ}
    (hauxiliary :
      HexPolyZMathlib.l2norm
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial ≤
        auxiliaryBound)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      auxiliaryBound ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates_ofBridgeDataAuxiliaryL2normAndFactoredPaperThreshold
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos hcap_le C hC_nonneg hC hcut bridge hauxiliary
    h_coeff (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)
    hchoose hprecision recoveryInputs

/--
Final HO-4 wrapper threading just the bridge data plus the paper-threshold-shape
inequality on the bridge-derived `Real.sqrt` auxiliary bound straight to
`Hex.factorFast f ≠ none`.

This composes `FactorFastCapSeparationInputs.ofBridgeDataAndPaperThreshold`
(which builds the cap-separation record from the bridge data alone, deriving
the auxiliary l2 bound via the structured corrected-RHS sqrt) with
`factorFast_terminates`.  Compared to
`factorFast_terminates_ofBridgeDataAuxiliaryL2normAndPaperThreshold`, the
caller no longer invents an `auxiliaryBound` parameter or proves an
auxiliary-l2 upper bound: both are derived internally from the bridge.
-/
theorem factorFast_terminates_ofBridgeDataAndPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (hpaper :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree *
        Real.sqrt
            (2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) +
              2 *
                (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                  (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                    (((factorFastCapLiftData f primeData).p : ℝ) ^
                      (2 *
                        ((factorFastCapLiftData f primeData).k -
                          Hex.bhksCoeffCutThreshold
                            (factorFastCapLiftData f primeData).p
                            (Hex.normalizeForFactor f).squareFreeCore j)))))) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperThresholdReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataAndPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge v hin hnot hcld hpaper hchoose hprecision)
    recoveryInputs

/--
Final HO-4 wrapper threading just the bridge data plus the two factored BHKS
Theorem 5.2 LHS sub-bounds on the bridge-derived `Real.sqrt` auxiliary bound
straight to `Hex.factorFast f ≠ none`.

This composes `FactorFastCapSeparationInputs.ofBridgeDataAndFactoredPaperThreshold`
(which builds the cap-separation record from the bridge data alone, deriving
the auxiliary l2 bound via the structured corrected-RHS sqrt and dispatching
the cap-arithmetic chain internally via
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored`) with
`factorFast_terminates`.  Compared to
`factorFast_terminates_ofBridgeDataAndPaperThreshold`, the caller supplies the
two independent BHKS Theorem 5.2 sub-bounds rather than the combined product
inequality.
-/
theorem factorFast_terminates_ofBridgeDataAndFactoredPaperThreshold
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      Real.sqrt
            (2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) +
              2 *
                (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                  (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                    (((factorFastCapLiftData f primeData).p : ℝ) ^
                      (2 *
                        ((factorFastCapLiftData f primeData).k -
                          Hex.bhksCoeffCutThreshold
                            (factorFastCapLiftData f primeData).p
                            (Hex.normalizeForFactor f).squareFreeCore j)))))) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperDegreeFactorReal (Hex.normalizeForFactor f).squareFreeCore *
            bhksPaperConstantFactorReal (Hex.normalizeForFactor f).squareFreeCore C *
          bhksPaperLogFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates f primeData rows_pos trueSupports
    (FactorFastCapSeparationInputs.ofBridgeDataAndFactoredPaperThreshold
      localFactorIndex localFactorDegree H hlocalFactorDegree_pos hcap_le
      C hC_nonneg hC hcut bridge v hin hnot hcld h_coeff h_aux hchoose hprecision)
    recoveryInputs

/--
Named-auxiliary sibling of
`factorFast_terminates_ofBridgeDataAndFactoredPaperThreshold`: the
auxiliary-power sub-bound is stated against the named
`bhksPaperAuxiliaryFactorReal core C` target instead of the unfolded three-way
product.  One-step shim that unfolds the named target and dispatches to the
unprimed variant.
-/
theorem factorFast_terminates_ofBridgeDataAndFactoredPaperThreshold'
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
    (hlocalFactorDegree_pos : 0 < localFactorDegree)
    (hcap_le :
      Hex.factorFastPrecisionCap (Hex.normalizeForFactor f).squareFreeCore ≤
        (factorFastCapLiftData f primeData).k)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut :
      CutProjectionHypotheses
        (projectedRowsOfLiftData
          (Hex.normalizeForFactor f).squareFreeCore
          (factorFastCapLiftData f primeData)
          rows_pos)
        trueSupports)
    (bridge :
      ExecutableBadVectorWitness.BadVectorBridgeData
        (badVectorWitnessOfFactorFastCapLiftData
          f primeData rows_pos localFactorIndex localFactorDegree H)
        trueSupports)
    (v :
      Fin (projectedRowsOfLiftData
        (Hex.normalizeForFactor f).squareFreeCore
        (factorFastCapLiftData f primeData)
        rows_pos).factorCount → ℤ)
    (hin :
      v ∈
        BHKS.projectedRowSpanInt
          (projectedRowsOfLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (factorFastCapLiftData f primeData)
            rows_pos))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hcld :
      ∀ (i : Nat),
        i < (factorFastCapLiftData f primeData).liftedFactors.size →
          ∀ (j : Nat),
            ((Hex.cldCoeffs (Hex.normalizeForFactor f).squareFreeCore
                (factorFastCapLiftData f primeData).p
                (factorFastCapLiftData f primeData).k
                ((factorFastCapLiftData f primeData).liftedFactors.getD i 0)).getD j 0).natAbs ≤
              Hex.bhksCoeffBound (Hex.normalizeForFactor f).squareFreeCore j)
    (h_coeff :
      (Hex.ZPoly.coeffL2NormBound
            (Hex.normalizeForFactor f).squareFreeCore : ℝ) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).auxiliaryPolynomial.natDegree ≤
        bhksPaperCoeffNormFactorReal (Hex.normalizeForFactor f).squareFreeCore)
    (h_aux :
      Real.sqrt
            (2 *
                ((∑ i : Fin (factorFastCapLiftData f primeData).liftedFactors.size,
                    ((((badVectorWitnessOfFactorFastCapLiftData
                          f primeData rows_pos localFactorIndex localFactorDegree H).projectedVectorArray v).getD
                        i.val 0 : ℝ) ^ 2)) *
                  (((factorFastCapLiftData f primeData).liftedFactors.size : ℝ) *
                    (BHKS.cldColumnNormBound
                      (Hex.normalizeForFactor f).squareFreeCore
                      (factorFastCapLiftData f primeData).p : ℝ))) +
              2 *
                (∑ j ∈ Finset.range ((Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0),
                  (((bridge.auxiliaryCorrections v hin hnot).getD j 0 : ℝ) ^ 2 *
                    (((factorFastCapLiftData f primeData).p : ℝ) ^
                      (2 *
                        ((factorFastCapLiftData f primeData).k -
                          Hex.bhksCoeffCutThreshold
                            (factorFastCapLiftData f primeData).p
                            (Hex.normalizeForFactor f).squareFreeCore j)))))) ^
          (badVectorWitnessOfFactorFastCapLiftData
            f primeData rows_pos localFactorIndex localFactorDegree H).inputPolynomial.natDegree ≤
        bhksPaperAuxiliaryFactorReal (Hex.normalizeForFactor f).squareFreeCore C)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData)
    (hprecision :
      (factorFastCapLiftData f primeData).k =
        Hex.precisionForCoeffBound
          (Hex.factorFastPrecisionCap
            (Hex.normalizeForFactor f).squareFreeCore)
          (factorFastCapLiftData f primeData).p)
    (recoveryInputs :
      CanonicalRecoveryTailInputs f primeData rows_pos trueSupports) :
    Hex.factorFast f ≠ none :=
  factorFast_terminates_ofBridgeDataAndFactoredPaperThreshold
    f primeData rows_pos trueSupports localFactorIndex localFactorDegree H
    hlocalFactorDegree_pos hcap_le C hC_nonneg hC hcut bridge v hin hnot hcld
    h_coeff
    (bhksPaperAuxiliaryFactorReal_eq_product
      (Hex.normalizeForFactor f).squareFreeCore C ▸ h_aux)
    hchoose hprecision recoveryInputs

end BHKS

end HexBerlekampZassenhausMathlib
