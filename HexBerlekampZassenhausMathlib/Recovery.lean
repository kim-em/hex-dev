import HexBerlekampZassenhausMathlib.Lattice
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
    (Hex.bhksLatticeBasis_independent _)

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
indicator list; this is the residual obligation B7 in the SPEC, which
depends on still-open executable RREF correctness and is intentionally left
abstract here.
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
            hrows (Hex.bhksLatticeBasis_independent _))
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (Hex.bhksLatticeBasis_independent _))) = false :=
    h.nondegenerate
  have hcand :
      Hex.bhksIndicatorCandidates? f d
          (Hex.bhksEquivalenceClassIndicators
            (Hex.bhksProjectedRows
              (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
              hrows (Hex.bhksLatticeBasis_independent _))) =
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

end BHKS

end HexBerlekampZassenhausMathlib
