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

end HexBerlekampZassenhausMathlib
