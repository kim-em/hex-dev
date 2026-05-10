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
  unfold Hex.bhksRecover?
  simp only [dif_pos hrows, hnondeg, hcand, Bool.false_eq_true, if_false, hprod,
    BEq.refl, if_true]

end BHKS

end HexBerlekampZassenhausMathlib
