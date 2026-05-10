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

private theorem range_foldl_add_eq_finset_sum_nat (g : Nat → Nat) (m : Nat) :
    (List.range m).foldl (fun acc i => acc + g i) 0 =
      ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

private theorem toPolynomial_support_subset_range_size (f : Hex.ZPoly) :
    (HexPolyZMathlib.toPolynomial f).support ⊆ Finset.range f.size := by
  intro i hi
  rw [Finset.mem_range]
  by_contra hlt
  have hcoeff : f.coeff i = 0 :=
    Hex.DensePoly.coeff_eq_zero_of_size_le f (Nat.le_of_not_gt hlt)
  have hne : (HexPolyZMathlib.toPolynomial f).coeff i ≠ 0 :=
    (Polynomial.mem_support_iff).mp hi
  exact hne (by simpa using hcoeff)

private theorem int_natAbs_sq_cast_eq_sq (z : Int) :
    ((z.natAbs : ℝ) ^ 2) = ((z : ℝ) ^ 2) := by
  norm_num [sq]

private theorem l2norm_toPolynomial_sq_le_sumSquared_succ (f : Hex.ZPoly) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2 ≤
      (bhksSumSquared f + 1 : ℝ) := by
  have hsum_nonneg :
      0 ≤ ∑ i ∈ (HexPolyZMathlib.toPolynomial f).support,
        ((HexPolyZMathlib.toPolynomial f).coeff i : ℝ) ^ 2 := by
    exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hl2_sq :
      (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2 =
        ∑ i ∈ (HexPolyZMathlib.toPolynomial f).support,
          ((HexPolyZMathlib.toPolynomial f).coeff i : ℝ) ^ 2 := by
    unfold HexPolyZMathlib.l2norm
    exact Real.sq_sqrt hsum_nonneg
  have hsupport := toPolynomial_support_subset_range_size f
  have hsum_le :
      ∑ i ∈ (HexPolyZMathlib.toPolynomial f).support,
          ((HexPolyZMathlib.toPolynomial f).coeff i : ℝ) ^ 2
        ≤ ∑ i ∈ Finset.range f.size, ((f.coeff i).natAbs : ℝ) ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsupport ?_).trans_eq ?_
    · intro i hi_range hi_not_support
      exact sq_nonneg _
    · apply Finset.sum_congr rfl
      intro i hi
      simp
  have hcoeff_eq :
      (bhksSumSquared f : ℝ) =
        ∑ i ∈ Finset.range f.size, ((f.coeff i).natAbs : ℝ) ^ 2 := by
    rw [bhksSumSquared, Hex.ZPoly.coeffNormSq_eq_sum,
      range_foldl_add_eq_finset_sum_nat]
    norm_cast
  calc
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2
        = ∑ i ∈ (HexPolyZMathlib.toPolynomial f).support,
            ((HexPolyZMathlib.toPolynomial f).coeff i : ℝ) ^ 2 := hl2_sq
    _ ≤ ∑ i ∈ Finset.range f.size, ((f.coeff i).natAbs : ℝ) ^ 2 := hsum_le
    _ = (bhksSumSquared f : ℝ) := hcoeff_eq.symm
    _ ≤ (bhksSumSquared f + 1 : ℝ) := by norm_num

private theorem nonneg_pow_two_sub_one_le_pow_of_sq_le
    {x A : ℝ} {n : Nat} (hx : 0 ≤ x) (hA1 : 1 ≤ A) (hsq : x ^ 2 ≤ A) :
    x ^ (2 * n - 1) ≤ A ^ n := by
  cases n with
  | zero =>
      simp
  | succ k =>
      have hA0 : 0 ≤ A := le_trans zero_le_one hA1
      have hx_le_A : x ≤ A := by
        by_cases hx1 : x ≤ 1
        · exact hx1.trans hA1
        · have h1x : 1 ≤ x := le_of_not_ge hx1
          have hx_le_sq : x ≤ x ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left h1x hx]
          exact hx_le_sq.trans hsq
      have hpowsq : (x ^ 2) ^ k ≤ A ^ k :=
        pow_le_pow_left₀ (sq_nonneg x) hsq k
      have hmain : x * (x ^ 2) ^ k ≤ A * A ^ k :=
        mul_le_mul hx_le_A hpowsq (pow_nonneg (sq_nonneg x) k) hA0
      calc
        x ^ (2 * (k + 1) - 1) = x * (x ^ 2) ^ k := by
          rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
          rw [pow_succ, pow_mul]
          ring
        _ ≤ A * A ^ k := hmain
        _ = A ^ (k + 1) := by rw [pow_succ]; ring

private theorem log_l2norm_le_log2_sumSquared_succ (f : Hex.ZPoly) :
    Real.log (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ≤
      (Nat.log2 (bhksSumSquared f + 1) : ℝ) := by
  let x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)
  let A := bhksSumSquared f + 1
  have hx_nonneg : 0 ≤ x := by
    unfold x HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  have hsq : x ^ 2 ≤ (A : ℝ) := by
    simpa [x, A] using l2norm_toPolynomial_sq_le_sumSquared_succ f
  by_cases hx_zero : x = 0
  · simp [x, hx_zero]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_zero)
  have hlog_sq :
      Real.log x ≤ Real.log (A : ℝ) / 2 := by
    have hA_pos : 0 < (A : ℝ) := by positivity
    have hlog_le : Real.log (x ^ 2) ≤ Real.log (A : ℝ) :=
      Real.log_le_log (sq_pos_of_pos hx_pos) hsq
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hlog_pow : Real.log (x ^ 2) = 2 * Real.log x := by
      simp [Real.log_pow]
    nlinarith [hlog_le, hlog_pow]
  have hlogA_le :
      Real.log (A : ℝ) / 2 ≤ (Nat.log2 A : ℝ) := by
    by_cases hA_one : A = 1
    · simp [hA_one]
    have hA_ge_two : 2 ≤ A := by omega
    rw [Nat.log2_eq_log_two]
    let k := Nat.log 2 A
    change Real.log (A : ℝ) / 2 ≤ (k : ℝ)
    have hk_pos : 1 ≤ k := by
      exact Nat.le_log_of_pow_le (by decide : 1 < 2) (by simpa [k] using hA_ge_two)
    have hA_lt_pow : (A : ℝ) < (2 : ℝ) ^ (k + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) A
    have hlogA_lt : Real.log (A : ℝ) < (k + 1 : ℝ) * Real.log 2 := by
      calc
        Real.log (A : ℝ) < Real.log ((2 : ℝ) ^ (k + 1)) :=
          Real.log_lt_log (by positivity) hA_lt_pow
        _ = (k + 1 : ℝ) * Real.log 2 := by
          rw [Real.log_pow]
          norm_num
    have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) :=
      by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
    have hsucc_le : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by
      have hk_bound_nat : k + 1 ≤ 2 * k := by omega
      exact_mod_cast hk_bound_nat
    have hlogA_le_succ : Real.log (A : ℝ) ≤ (k + 1 : ℝ) := by
      have hmul_le : (k + 1 : ℝ) * Real.log 2 ≤ (k + 1 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2_le_one (by positivity)
      nlinarith [hlogA_lt.le, hmul_le]
    nlinarith [hlogA_le_succ, hsucc_le]
  exact hlog_sq.trans hlogA_le

private theorem l2norm_log_nonneg (f : Hex.ZPoly) :
    0 ≤ Real.log (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) := by
  let x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)
  have hx_nonneg : 0 ≤ x := by
    unfold x HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  by_cases hx_zero : x = 0
  · simp [x, hx_zero]
  let P := HexPolyZMathlib.toPolynomial f
  have hx_sq :
      x ^ 2 = ∑ i ∈ P.support, ((P.coeff i : ℝ) ^ 2) := by
    have hsum_nonneg : 0 ≤ ∑ i ∈ P.support, ((P.coeff i : ℝ) ^ 2) :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    unfold x HexPolyZMathlib.l2norm P
    exact Real.sq_sqrt hsum_nonneg
  have hP_ne : P ≠ 0 := by
    intro hP
    apply hx_zero
    unfold x HexPolyZMathlib.l2norm P at *
    simp [hP]
  rcases (Polynomial.support_nonempty).mpr hP_ne with ⟨i, hi⟩
  have hcoeff_ne : P.coeff i ≠ 0 := (Polynomial.mem_support_iff).mp hi
  have hcoeff_sq_one : (1 : ℝ) ≤ (P.coeff i : ℝ) ^ 2 := by
    have hnat_pos : 0 < (P.coeff i).natAbs := Int.natAbs_pos.mpr hcoeff_ne
    have hnat_one : (1 : ℝ) ≤ ((P.coeff i).natAbs : ℝ) := by
      exact_mod_cast hnat_pos
    rw [← int_natAbs_sq_cast_eq_sq]
    nlinarith [hnat_one]
  have hsingle :
      (P.coeff i : ℝ) ^ 2 ≤ ∑ j ∈ P.support, ((P.coeff j : ℝ) ^ 2) :=
    Finset.single_le_sum
      (s := P.support) (f := fun j => ((P.coeff j : ℝ) ^ 2))
      (fun j hj => sq_nonneg _) hi
  have hx_sq_ge_one : (1 : ℝ) ≤ x ^ 2 := by
    rw [hx_sq]
    exact hcoeff_sq_one.trans hsingle
  have hx_ge_one : 1 ≤ x := by
    have h_abs : |(1 : ℝ)| ≤ |x| := (sq_le_sq).mp (by simpa using hx_sq_ge_one)
    simpa [abs_of_nonneg hx_nonneg] using h_abs
  exact Real.log_nonneg hx_ge_one

/--
Named analytic target for bounding the BHKS coefficient-norm factor by the
packaged integer coefficient-norm factor.
-/
theorem bhksPaperCoeffNormFactorReal_le_coeffNormFactor (f : Hex.ZPoly) :
    bhksPaperCoeffNormFactorReal f ≤ (bhksCoeffNormFactor f : ℝ) := by
  have hx_nonneg :
      0 ≤ HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) := by
    unfold HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  have hsq := l2norm_toPolynomial_sq_le_sumSquared_succ f
  have hA1 : (1 : ℝ) ≤ (bhksSumSquared f + 1 : ℝ) := by norm_num
  simpa [bhksPaperCoeffNormFactorReal, bhksCoeffNormFactor] using
    nonneg_pow_two_sub_one_le_pow_of_sq_le
      (x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f))
      (A := (bhksSumSquared f + 1 : ℝ))
      (n := bhksDegree f) hx_nonneg hA1 hsq

/--
Named analytic target for bounding the BHKS logarithmic factor by the packaged
`Nat.log2` factor.
-/
theorem bhksPaperLogFactorReal_le_log2Factor (f : Hex.ZPoly) :
    bhksPaperLogFactorReal f ≤ (bhksLog2Factor f : ℝ) := by
  have hlog_nonneg := l2norm_log_nonneg f
  have hlog_le := log_l2norm_le_log2_sumSquared_succ f
  simpa [bhksPaperLogFactorReal, bhksLog2Factor] using
    pow_le_pow_left₀ hlog_nonneg hlog_le (bhksDegree f)

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
