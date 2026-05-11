import HexBerlekampZassenhausMathlib.BadVector
import HexBerlekampZassenhausMathlib.BHKSBound

/-!
BHKS termination-bound packaging.

This module combines the executable fast-path precision cap with the
proof-facing bad-vector contradiction, so later termination work can consume a
single interface instead of restating the cap algebra at each leaf.
-/

namespace HexBerlekampZassenhausMathlib

open Polynomial

/--
Any precision at least `factorFastPrecisionCap f` also dominates the executable
BHKS bound, in the real-valued form used by the analytic separation lemmas.
-/
theorem bhksBound_real_le_of_factorFastPrecisionCap_le
    (f : Hex.ZPoly) {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a) :
    (Hex.bhksBound f : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast (le_trans (bhksBound_le_factorFastPrecisionCap f) ha)

/--
Any precision at least `factorFastPrecisionCap f` also dominates the executable
Mignotte coefficient bound, in the real-valued form used by reconstruction
lemmas.
-/
theorem defaultFactorCoeffBound_real_le_of_factorFastPrecisionCap_le
    (f : Hex.ZPoly) {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a) :
    (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast (le_trans (defaultFactorCoeffBound_le_factorFastPrecisionCap f) ha)

/--
Any precision at least `factorFastPrecisionCap f` dominates both executable
integer bounds needed by the fast-path termination proof.
-/
theorem factorFastPrecisionCap_real_dominates
    (f : Hex.ZPoly) {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a) :
    (Hex.bhksBound f : ℝ) ≤ (a : ℝ) ∧
      (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤ (a : ℝ) := by
  exact ⟨bhksBound_real_le_of_factorFastPrecisionCap_le f ha,
    defaultFactorCoeffBound_real_le_of_factorFastPrecisionCap_le f ha⟩

/--
Arithmetic helper: `2 * n + 1 ≤ 2 ^ (n + 1)` for every `n : Nat`.

Used to discharge the Mignotte precision side condition: chained with
`Nat.pow_le_pow_right` and `Nat.pow_le_pow_left` it yields
`2 * n < p ^ k` whenever `n + 1 ≤ k` and `2 ≤ p`.
-/
private theorem two_mul_add_one_le_two_pow_succ (n : Nat) :
    2 * n + 1 ≤ 2 ^ (n + 1) := by
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hsucc : n + 1 ≤ 2 ^ n := hlt
  calc
    2 * n + 1 ≤ 2 * (n + 1) := by omega
    _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 hsucc
    _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/--
Mignotte-precision discharge at any precision strictly exceeding the
executable fast-path cap `factorFastPrecisionCap`.  Once `k` is strictly
greater than the cap, any prime modulus `p ≥ 2` gives
`2 * defaultFactorCoeffBound f < p ^ k`, populating the
`mignotte_precision` side condition consumed by
`ForwardRecoveryInputs`.

The strict cap hypothesis is necessary: at the boundary `cap = k = 1` with
`p = 2` the inequality fails (`f` a unit-coefficient constant has
`defaultFactorCoeffBound f = 1`, so `2 * 1 = 2 = 2 ^ 1`).  Consumers needing
the conclusion at the cap itself should bump the precision by one, e.g.
work with `cap + 1` rather than `cap`.
-/
theorem mignotte_precision_of_factorFastPrecisionCap_lt
    (f : Hex.ZPoly) {p k : Nat} (hp : 2 ≤ p)
    (hcap : Hex.factorFastPrecisionCap f < k) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f < p ^ k := by
  set B := Hex.ZPoly.defaultFactorCoeffBound f
  have hB_cap : B ≤ Hex.factorFastPrecisionCap f :=
    defaultFactorCoeffBound_le_factorFastPrecisionCap f
  have hBk : B + 1 ≤ k := by omega
  have hstep1 : 2 * B + 1 ≤ 2 ^ (B + 1) :=
    two_mul_add_one_le_two_pow_succ B
  have hstep2 : (2 : Nat) ^ (B + 1) ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by decide) hBk
  have hstep3 : (2 : Nat) ^ k ≤ p ^ k := Nat.pow_le_pow_left hp k
  have hchain : 2 * B + 1 ≤ p ^ k := hstep1.trans (hstep2.trans hstep3)
  omega

/--
Unconditional cap-successor form: at precision `factorFastPrecisionCap f + 1`,
the Mignotte precision side condition holds for any modulus `p ≥ 2`.

This is the canonical consumer-facing way to obtain `2 * B < p ^ k`: pick
`k = factorFastPrecisionCap f + 1` and apply this lemma directly.  Larger
`k` reduce via
`mignotte_precision_of_factorFastPrecisionCap_lt`.
-/
theorem mignotte_precision_at_factorFastPrecisionCap_succ
    (f : Hex.ZPoly) {p : Nat} (hp : 2 ≤ p) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f <
      p ^ (Hex.factorFastPrecisionCap f + 1) :=
  mignotte_precision_of_factorFastPrecisionCap_lt f hp (Nat.lt_succ_self _)

/--
At any precision at least `factorFastPrecisionCap f`, the BHKS paper threshold
is bounded by that precision, under the project `0 ≤ C ≤ 2` constant
assumption.
-/
theorem bhksPaperThresholdReal_le_of_factorFastPrecisionCap_le
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a) :
    bhksPaperThresholdReal f C ≤ (a : ℝ) :=
  (bhksPaperThresholdReal_le_bhksBound f C hC_nonneg hC).trans
    (bhksBound_real_le_of_factorFastPrecisionCap_le f ha)

namespace ExecutableBadVectorWitness

/--
Packaged BHKS bad-vector contradiction at a precision bounded below by
`factorFastPrecisionCap`.

The remaining analytic leaf is the explicit `hlt` hypothesis: once the
Hadamard/l2norm upper bound drops below the modular divisor, the existing
bad-vector contradiction applies. The conclusion also packages the paper
threshold dominance provided by the same cap hypothesis, so downstream
termination work can carry both facts through one theorem.
-/
theorem bhksPaperThreshold_and_no_bad_setup_of_factorFastPrecisionCap_le
    (W : ExecutableBadVectorWitness) {a : Nat}
    (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree <
      (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    bhksPaperThresholdReal W.input C ≤ (a : ℝ) ∧ False := by
  exact
    ⟨bhksPaperThresholdReal_le_of_factorFastPrecisionCap_le
        W.input C hC_nonneg hC ha,
      no_bhks_bad_setup_of_l2norm_upper_lt_divisor W h_bad hp hlt⟩

/--
Contradiction-only wrapper for callers that have already consumed the packaged
paper-threshold dominance.
-/
theorem no_bhks_bad_setup_of_factorFastPrecisionCap_le
    (W : ExecutableBadVectorWitness) {a : Nat}
    (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree <
      (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    False :=
  (bhksPaperThreshold_and_no_bad_setup_of_factorFastPrecisionCap_le
    W ha C hC_nonneg hC h_bad hp hlt).2

end ExecutableBadVectorWitness

namespace BHKS

/--
Proof-facing hypotheses for the executable-cap BHKS separation step.

The `bad_setup_of_projected_not_indicator` field is the remaining bridge from
a projected lattice vector outside the true-factor indicator lattice to the
bad-vector setup consumed by the resultant contradiction.  This structure lets
the cap/resultant layer expose the final `L' = W` theorem without depending on
the later failed-recovery construction.
-/
structure ExecutableCapSeparationHypotheses
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount))) where
  cut : CutProjectionHypotheses W.projectedRows trueSupports
  bad_setup_of_projected_not_indicator :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ projectedRowSpanInt W.projectedRows →
        v ∉ trueFactorIndicatorLattice trueSupports →
          ExecutableBadVectorWitness.IsBhksBadVectorSetup W
  hp : 0 < W.liftData.p
  l2norm_upper_lt_divisor :
    (HexPolyZMathlib.l2norm W.inputPolynomial) ^
        W.auxiliaryPolynomial.natDegree *
      (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
        W.inputPolynomial.natDegree <
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)

/--
At any executable fast-path precision cap, the cap-level bad-vector
contradiction excludes every vector in `L' \ W`.
-/
theorem no_projected_not_indicator_of_factorFastPrecisionCap_le
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    {a : Nat} (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap : ExecutableCapSeparationHypotheses W trueSupports) :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ projectedRowSpanInt W.projectedRows →
        v ∉ trueFactorIndicatorLattice trueSupports →
          False := by
  intro v hv hnot
  let h_bad := hcap.bad_setup_of_projected_not_indicator v hv hnot
  exact
    ExecutableBadVectorWitness.no_bhks_bad_setup_of_factorFastPrecisionCap_le
      W ha C hC_nonneg hC h_bad hcap.hp
      hcap.l2norm_upper_lt_divisor

/--
Executable-cap BHKS separation: at any precision meeting
`factorFastPrecisionCap`, the projected row span equals the true-factor
indicator lattice, assuming the remaining failed-recovery-to-bad-vector bridge.
-/
theorem projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    {a : Nat} (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap : ExecutableCapSeparationHypotheses W trueSupports) :
    projectedRowSpanInt W.projectedRows =
      trueFactorIndicatorLattice trueSupports := by
  exact projectedRowSpan_eq_trueFactorIndicatorLattice
    W.projectedRows trueSupports
    { cut := hcap.cut
      no_projected_not_indicator :=
        no_projected_not_indicator_of_factorFastPrecisionCap_le
          W trueSupports ha C hC_nonneg hC hcap }

end BHKS

end HexBerlekampZassenhausMathlib
