import HexBerlekampZassenhausMathlib.Basic

/-!
Stable unpacking lemmas for the executable BHKS precision cap.

The executable `Hex.bhksBound` is intentionally pure `Nat` arithmetic.  This
file gives the Mathlib bridge layer named components for the SPEC Group-D
integer expression so later BHKS termination work can refer to those
components without repeatedly unfolding the executable definition.
-/

namespace HexBerlekampZassenhausMathlib

/-- Executable degree parameter used by the BHKS precision cap. -/
def bhksDegree (f : Hex.ZPoly) : Nat :=
  f.degree?.getD 0

/-- Squared coefficient norm parameter used by the BHKS precision cap. -/
def bhksSumSquared (f : Hex.ZPoly) : Nat :=
  Hex.ZPoly.coeffNormSq f

/-- The direct degree factor in the SPEC Group-D integer cap. -/
def bhksDegreeFactor (f : Hex.ZPoly) : Nat :=
  bhksDegree f

/-- The `4^(n*n)` factor in the SPEC Group-D integer cap. -/
def bhksFourPowFactor (f : Hex.ZPoly) : Nat :=
  4 ^ (bhksDegree f * bhksDegree f)

/-- The `(sumSquared + 1)^n` coefficient-norm factor in the SPEC Group-D cap. -/
def bhksCoeffNormFactor (f : Hex.ZPoly) : Nat :=
  (bhksSumSquared f + 1) ^ bhksDegree f

/-- The `(log2 (sumSquared + 1))^n` logarithmic factor in the SPEC Group-D cap. -/
def bhksLog2Factor (f : Hex.ZPoly) : Nat :=
  (Nat.log2 (bhksSumSquared f + 1)) ^ bhksDegree f

/--
The SPEC Group-D integer upper-bound expression for the BHKS threshold.

This is the expression documented in
`SPEC/Libraries/hex-berlekamp-zassenhaus.md`: `1 + n * 4^(n*n) *
(sumSquared + 1)^n * log2(sumSquared + 1)^n`.
-/
def bhksThresholdNatBound (f : Hex.ZPoly) : Nat :=
  1 + bhksDegreeFactor f * bhksFourPowFactor f *
    bhksCoeffNormFactor f * bhksLog2Factor f

theorem bhksDegreeFactor_eq (f : Hex.ZPoly) :
    bhksDegreeFactor f = f.degree?.getD 0 := by
  rfl

theorem bhksFourPowFactor_eq (f : Hex.ZPoly) :
    bhksFourPowFactor f = 4 ^ (f.degree?.getD 0 * f.degree?.getD 0) := by
  rfl

theorem bhksCoeffNormFactor_eq (f : Hex.ZPoly) :
    bhksCoeffNormFactor f =
      (Hex.ZPoly.coeffNormSq f + 1) ^ f.degree?.getD 0 := by
  rfl

theorem bhksLog2Factor_eq (f : Hex.ZPoly) :
    bhksLog2Factor f =
      (Nat.log2 (Hex.ZPoly.coeffNormSq f + 1)) ^ f.degree?.getD 0 := by
  rfl

/-- The named BHKS cap components multiply to the documented integer cap. -/
theorem bhksThresholdNatBound_eq (f : Hex.ZPoly) :
    bhksThresholdNatBound f =
      1 + f.degree?.getD 0 * 4 ^ (f.degree?.getD 0 * f.degree?.getD 0) *
        (Hex.ZPoly.coeffNormSq f + 1) ^ f.degree?.getD 0 *
        (Nat.log2 (Hex.ZPoly.coeffNormSq f + 1)) ^ f.degree?.getD 0 := by
  rfl

/--
The executable `Hex.bhksBound` is exactly the packaged SPEC Group-D integer
bound.  Later proofs should use this theorem instead of unfolding
`Hex.bhksBound` directly.
-/
theorem bhksBound_eq_thresholdNatBound (f : Hex.ZPoly) :
    Hex.bhksBound f = bhksThresholdNatBound f := by
  rfl

/-- Nat-valued dominance form of the BHKS cap over the packaged threshold. -/
theorem bhksThresholdNatBound_le_bhksBound (f : Hex.ZPoly) :
    bhksThresholdNatBound f ≤ Hex.bhksBound f := by
  rw [bhksBound_eq_thresholdNatBound]

/-- Real-valued dominance form for analytic BHKS threshold comparisons. -/
theorem bhksThresholdNatBound_real_le_bhksBound (f : Hex.ZPoly) :
    (bhksThresholdNatBound f : ℝ) ≤ (Hex.bhksBound f : ℝ) := by
  exact_mod_cast bhksThresholdNatBound_le_bhksBound f

/-- Real-valued degree factor appearing in the BHKS paper threshold. -/
def bhksPaperDegreeFactorReal (f : Hex.ZPoly) : ℝ :=
  bhksDegree f

/-- Real-valued `(2C)^(n^2)` factor appearing in the BHKS paper threshold. -/
def bhksPaperConstantFactorReal (f : Hex.ZPoly) (C : ℝ) : ℝ :=
  (2 * C) ^ (bhksDegree f * bhksDegree f)

/-- Real-valued coefficient-norm factor `‖f‖₂^(2n-1)` from BHKS. -/
noncomputable def bhksPaperCoeffNormFactorReal (f : Hex.ZPoly) : ℝ :=
  (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ (2 * bhksDegree f - 1)

/-- Real-valued logarithmic factor `(log ‖f‖₂)^n` from BHKS. -/
noncomputable def bhksPaperLogFactorReal (f : Hex.ZPoly) : ℝ :=
  (Real.log (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f))) ^ bhksDegree f

/-- Product-shaped real BHKS paper threshold, with the project constant explicit. -/
noncomputable def bhksPaperThresholdReal (f : Hex.ZPoly) (C : ℝ) : ℝ :=
  bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
    bhksPaperCoeffNormFactorReal f * bhksPaperLogFactorReal f

/-- The packaged Nat degree factor is exactly the paper degree factor after cast. -/
theorem bhksPaperDegreeFactorReal_eq_natCast (f : Hex.ZPoly) :
    bhksPaperDegreeFactorReal f = (bhksDegreeFactor f : ℝ) := by
  rfl

/--
The project `C ≤ 2` convention makes the paper `(2C)^(n^2)` factor no larger
than the packaged `4^(n^2)` factor.
-/
theorem bhksPaperConstantFactorReal_le_fourPowFactor
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2) :
    bhksPaperConstantFactorReal f C ≤ (bhksFourPowFactor f : ℝ) := by
  have hbase_nonneg : 0 ≤ 2 * C := by nlinarith
  have hbase_le : 2 * C ≤ (4 : ℝ) := by nlinarith
  simpa [bhksPaperConstantFactorReal, bhksFourPowFactor] using
    pow_le_pow_left₀ hbase_nonneg hbase_le (bhksDegree f * bhksDegree f)

/--
Named analytic target for bounding the BHKS coefficient-norm factor by the
packaged integer coefficient-norm factor.
-/
theorem bhksPaperCoeffNormFactorReal_le_coeffNormFactor (f : Hex.ZPoly) :
    bhksPaperCoeffNormFactorReal f ≤ (bhksCoeffNormFactor f : ℝ) := by
  sorry

/--
Named analytic target for bounding the BHKS logarithmic factor by the packaged
`Nat.log2` factor.
-/
theorem bhksPaperLogFactorReal_le_log2Factor (f : Hex.ZPoly) :
    bhksPaperLogFactorReal f ≤ (bhksLog2Factor f : ℝ) := by
  sorry

/--
The packaged BHKS cap remains available alongside the executable Mignotte
coefficient bound through a single max expression.  This lightweight bridge is
useful for later proofs that need one precision dominating both reconstruction
and BHKS separation requirements.
-/
theorem bhksBound_le_max_bhksBound_defaultFactorCoeffBound (f : Hex.ZPoly) :
    Hex.bhksBound f ≤ max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) :=
  Nat.le_max_left _ _

theorem defaultFactorCoeffBound_le_max_bhksBound_defaultFactorCoeffBound (f : Hex.ZPoly) :
    Hex.ZPoly.defaultFactorCoeffBound f ≤
      max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) :=
  Nat.le_max_right _ _

theorem bhksBound_real_le_max_bhksBound_defaultFactorCoeffBound (f : Hex.ZPoly) :
    (Hex.bhksBound f : ℝ) ≤
      (max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) : ℝ) := by
  exact_mod_cast bhksBound_le_max_bhksBound_defaultFactorCoeffBound f

theorem defaultFactorCoeffBound_real_le_max_bhksBound_defaultFactorCoeffBound (f : Hex.ZPoly) :
    (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤
      (max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) : ℝ) := by
  exact_mod_cast defaultFactorCoeffBound_le_max_bhksBound_defaultFactorCoeffBound f

theorem bhksBound_real_le_of_max_bhksBound_defaultFactorCoeffBound_le
    (f : Hex.ZPoly) {a : Nat}
    (ha : max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) ≤ a) :
    (Hex.bhksBound f : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast
    (le_trans (bhksBound_le_max_bhksBound_defaultFactorCoeffBound f) ha)

theorem defaultFactorCoeffBound_real_le_of_max_bhksBound_defaultFactorCoeffBound_le
    (f : Hex.ZPoly) {a : Nat}
    (ha : max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) ≤ a) :
    (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤ (a : ℝ) := by
  exact_mod_cast
    (le_trans (defaultFactorCoeffBound_le_max_bhksBound_defaultFactorCoeffBound f) ha)

/--
The public fast path uses exactly the combined precision cap needed by the
Group-D termination proof: one bound dominates BHKS separation and Mignotte
reconstruction.
-/
theorem factorFastPrecisionCap_eq_max_bhksBound_defaultFactorCoeffBound
    (f : Hex.ZPoly) :
    Hex.factorFastPrecisionCap f =
      max (Hex.bhksBound f) (Hex.ZPoly.defaultFactorCoeffBound f) := by
  rfl

theorem bhksBound_le_factorFastPrecisionCap (f : Hex.ZPoly) :
    Hex.bhksBound f ≤ Hex.factorFastPrecisionCap f := by
  rw [factorFastPrecisionCap_eq_max_bhksBound_defaultFactorCoeffBound]
  exact bhksBound_le_max_bhksBound_defaultFactorCoeffBound f

theorem defaultFactorCoeffBound_le_factorFastPrecisionCap (f : Hex.ZPoly) :
    Hex.ZPoly.defaultFactorCoeffBound f ≤ Hex.factorFastPrecisionCap f := by
  rw [factorFastPrecisionCap_eq_max_bhksBound_defaultFactorCoeffBound]
  exact defaultFactorCoeffBound_le_max_bhksBound_defaultFactorCoeffBound f

theorem bhksBound_real_le_factorFastPrecisionCap (f : Hex.ZPoly) :
    (Hex.bhksBound f : ℝ) ≤ (Hex.factorFastPrecisionCap f : ℝ) := by
  exact_mod_cast bhksBound_le_factorFastPrecisionCap f

theorem defaultFactorCoeffBound_real_le_factorFastPrecisionCap (f : Hex.ZPoly) :
    (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤
      (Hex.factorFastPrecisionCap f : ℝ) := by
  exact_mod_cast defaultFactorCoeffBound_le_factorFastPrecisionCap f

end HexBerlekampZassenhausMathlib
