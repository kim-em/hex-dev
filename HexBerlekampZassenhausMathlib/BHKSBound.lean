import HexBerlekampZassenhausMathlib.Basic

/-!
Stable unpacking lemmas for the executable BHKS precision cap.

The executable `Hex.bhksBound` is intentionally pure `Nat` arithmetic.  This
file gives the Mathlib bridge layer named components for the SPEC Group-D
integer expression so later BHKS termination work can refer to those
components without repeatedly unfolding the executable definition.
-/

namespace HexBerlekampZassenhausMathlib

open scoped BigOperators

private theorem range_foldl_add_eq_finset_sum_nat (g : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => acc + g i) 0 = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

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
The Mathlib coefficient-vector norm squared is bounded by the executable
squared coefficient norm.
-/
theorem l2norm_toPolynomial_sq_le_coeffNormSq (f : Hex.ZPoly) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2 ≤
      (Hex.ZPoly.coeffNormSq f : ℝ) := by
  let p := HexPolyZMathlib.toPolynomial f
  have hsupport_subset : p.support ⊆ Finset.range f.size := by
    intro i hi
    by_contra hi_range
    have hsize : f.size ≤ i := Nat.le_of_not_gt (by
      simpa using hi_range)
    have hcoeff_zero : p.coeff i = 0 := by
      change (HexPolyZMathlib.toPolynomial f).coeff i = 0
      rw [HexPolyZMathlib.coeff_toPolynomial]
      exact Hex.DensePoly.coeff_eq_zero_of_size_le f hsize
    exact (Polynomial.mem_support_iff.mp hi) hcoeff_zero
  have hsqrt :
      (HexPolyZMathlib.l2norm p) ^ 2 =
        ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := by
    unfold HexPolyZMathlib.l2norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hsum_le :
      ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 ≤
        ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsupport_subset
      (fun i hi_range hi_support => sq_nonneg _)
  have hnorm_sum :
      (Hex.ZPoly.coeffNormSq f : ℝ) =
        ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := by
    have hnat :
        Hex.ZPoly.coeffNormSq f =
          ∑ i ∈ Finset.range f.size, (f.coeff i).natAbs ^ 2 := by
      rw [Hex.ZPoly.coeffNormSq_eq_sum, range_foldl_add_eq_finset_sum_nat]
    rw [hnat]
    calc
      ((∑ i ∈ Finset.range f.size, (f.coeff i).natAbs ^ 2 : Nat) : ℝ) =
          ∑ i ∈ Finset.range f.size, ((f.coeff i).natAbs : ℝ) ^ 2 := by
        norm_cast
      _ = ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [p, sq_abs, Nat.cast_natAbs]
  calc
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2 =
        (HexPolyZMathlib.l2norm p) ^ 2 := rfl
    _ = ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := hsqrt
    _ ≤ ∑ i ∈ Finset.range f.size, (p.coeff i : ℝ) ^ 2 := hsum_le
    _ = (Hex.ZPoly.coeffNormSq f : ℝ) := hnorm_sum.symm

/--
The same squared-norm bridge with the `+ 1` slack used by the executable BHKS
coefficient factor.
-/
theorem l2norm_toPolynomial_sq_le_coeffNormSq_add_one (f : Hex.ZPoly) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2 ≤
      (Hex.ZPoly.coeffNormSq f + 1 : ℝ) := by
  exact le_trans (l2norm_toPolynomial_sq_le_coeffNormSq f) (by norm_num)

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

end HexBerlekampZassenhausMathlib
