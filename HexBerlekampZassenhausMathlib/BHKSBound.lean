import HexBerlekampZassenhausMathlib.Basic

/-!
Stable unpacking lemmas for the executable BHKS precision cap.

The executable `Hex.bhksBound` is intentionally pure `Nat` arithmetic.  This
file gives the Mathlib-side layer named components for the SPEC Group-D
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

/-- The `4^(n*n)` factor is at least one (since `4 ≥ 1`). -/
theorem one_le_bhksFourPowFactor (f : Hex.ZPoly) :
    1 ≤ bhksFourPowFactor f := by
  unfold bhksFourPowFactor
  exact Nat.one_le_pow _ _ (by decide)

/--
The `(sumSquared + 1)^n` coefficient-norm factor is at least one (the base
`sumSquared + 1` is positive).
-/
theorem one_le_bhksCoeffNormFactor (f : Hex.ZPoly) :
    1 ≤ bhksCoeffNormFactor f := by
  unfold bhksCoeffNormFactor
  exact Nat.one_le_pow _ _ (Nat.succ_pos _)

/-- The packaged BHKS threshold expression is at least one. -/
theorem one_le_bhksThresholdNatBound (f : Hex.ZPoly) :
    1 ≤ bhksThresholdNatBound f := by
  unfold bhksThresholdNatBound; omega

/-- The executable BHKS precision cap is at least one. -/
theorem one_le_bhksBound (f : Hex.ZPoly) :
    1 ≤ Hex.bhksBound f := by
  rw [bhksBound_eq_thresholdNatBound]
  exact one_le_bhksThresholdNatBound f

/--
The executable BHKS cap dominates the product of the four SPEC Group-D
integer-cap component factors.  The `+ 1` slack in `bhksBound` absorbs the
product, so this dominance holds without any hypothesis on the polynomial.

This is the bundled Nat-valued component-bound packaging targeted by BHKS
Group-D step 4: each integer-cap factor (`n`, `4^(n*n)`, `(sumSquared + 1)^n`,
`(log2 (sumSquared + 1))^n`) appears explicitly on the left-hand side, and the
executable `Hex.bhksBound` appears on the right.
-/
theorem bhksBound_dominates_spec_components (f : Hex.ZPoly) :
    bhksDegreeFactor f * bhksFourPowFactor f *
        bhksCoeffNormFactor f * bhksLog2Factor f ≤
      Hex.bhksBound f := by
  rw [bhksBound_eq_thresholdNatBound]
  unfold bhksThresholdNatBound
  omega

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

/--
The Euclidean norm of a nonzero integer polynomial is at least one: the
support contains at least one integer coefficient of absolute value `≥ 1`,
contributing `≥ 1` to the squared sum, so `‖P‖₂ ≥ 1`.

Used by `l2norm_log_nonneg` and monotonicity arguments comparing `‖core‖₂^k`
across exponents (where `‖core‖₂ ≥ 1` lets `pow_le_pow_right_of_le_one` apply
in the increasing direction).
-/
theorem one_le_l2norm_toPolynomial_of_ne_zero
    {f : Hex.ZPoly} (hf : HexPolyZMathlib.toPolynomial f ≠ 0) :
    1 ≤ HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) := by
  let x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)
  let P := HexPolyZMathlib.toPolynomial f
  have hx_nonneg : 0 ≤ x := by
    unfold x HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  have hx_sq :
      x ^ 2 = ∑ i ∈ P.support, ((P.coeff i : ℝ) ^ 2) := by
    have hsum_nonneg : 0 ≤ ∑ i ∈ P.support, ((P.coeff i : ℝ) ^ 2) :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    unfold x HexPolyZMathlib.l2norm P
    exact Real.sq_sqrt hsum_nonneg
  have hP_ne : P ≠ 0 := hf
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
  have h_abs : |(1 : ℝ)| ≤ |x| := (sq_le_sq).mp (by simpa using hx_sq_ge_one)
  simpa [abs_of_nonneg hx_nonneg] using h_abs

/--
An integer polynomial with at least two nonzero coefficients has Euclidean
norm strictly above one: each support coordinate is a nonzero integer, so its
square contributes `≥ 1`, and two such terms give `‖P‖₂² ≥ 2`, hence
`‖P‖₂ ≥ √2 > 1`.

This is the C-independent analytic core of the BHKS §5 "‖core‖₂ lower bound"
sub-piece: combined with the reachability fact that a normalized square-free
core has both a nonzero constant term and a nonzero leading term (x-power
stripping happens before `squareFreeCore`), it yields `1 < ‖core‖₂` for every
reachable core, strengthening `one_le_l2norm_toPolynomial_of_ne_zero` from `≤`
to strict and feeding `Real.log_pos` in the auxiliary-factor positivity below.
-/
theorem one_lt_l2norm_toPolynomial_of_two_le_support
    {f : Hex.ZPoly}
    (hcard : 2 ≤ (HexPolyZMathlib.toPolynomial f).support.card) :
    1 < HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) := by
  let P := HexPolyZMathlib.toPolynomial f
  have hterm : ∀ i ∈ P.support, (1 : ℝ) ≤ (P.coeff i : ℝ) ^ 2 := by
    intro i hi
    have hne : P.coeff i ≠ 0 := (Polynomial.mem_support_iff).mp hi
    have hnat_pos : 0 < (P.coeff i).natAbs := Int.natAbs_pos.mpr hne
    have hnat_one : (1 : ℝ) ≤ ((P.coeff i).natAbs : ℝ) := by exact_mod_cast hnat_pos
    rw [← int_natAbs_sq_cast_eq_sq]
    nlinarith [hnat_one]
  have hsum_ge : (2 : ℝ) ≤ ∑ i ∈ P.support, (P.coeff i : ℝ) ^ 2 :=
    calc (2 : ℝ) ≤ (P.support.card : ℝ) := by exact_mod_cast hcard
      _ = ∑ _i ∈ P.support, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ P.support, (P.coeff i : ℝ) ^ 2 := Finset.sum_le_sum hterm
  have hlt : Real.sqrt 1 <
      Real.sqrt (∑ i ∈ P.support, (P.coeff i : ℝ) ^ 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  simpa [HexPolyZMathlib.l2norm, P, Real.sqrt_one] using hlt

/-- A nonzero constant coefficient and positive executable degree give at
least two support entries after transport to `Polynomial ℤ`. -/
theorem two_le_support_card_of_const_degree
    {f : Hex.ZPoly}
    (hconst : f.coeff 0 ≠ 0)
    (hdeg : 1 ≤ bhksDegree f) :
    2 ≤ (HexPolyZMathlib.toPolynomial f).support.card := by
  let d := bhksDegree f
  let P := HexPolyZMathlib.toPolynomial f
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hconst
    rw [hf]
    rfl
  have hd_pos : 0 < d := hdeg
  have hsize_pos : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero f hf_ne
  have hd_eq : d = f.size - 1 := by
    simpa [d, bhksDegree] using (degree?_getD_of_ne_zero f hf_ne)
  have htop_ne : f.coeff d ≠ 0 := by
    have hlead_ne := Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero f hf_ne
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last f hsize_pos] at hlead_ne
    rwa [hd_eq]
  have hzero_mem : 0 ∈ P.support := by
    rw [Polynomial.mem_support_iff]
    change (HexPolyZMathlib.toPolynomial f).coeff 0 ≠ 0
    rw [HexPolyZMathlib.coeff_toPolynomial]
    exact hconst
  have htop_mem : d ∈ P.support := by
    rw [Polynomial.mem_support_iff]
    change (HexPolyZMathlib.toPolynomial f).coeff d ≠ 0
    rw [HexPolyZMathlib.coeff_toPolynomial]
    exact htop_ne
  have hpair_subset : ({0, d} : Finset Nat) ⊆ P.support := by
    intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hzero_mem
    · exact htop_mem
  have hpair_card : ({0, d} : Finset Nat).card = 2 := by
    have hne : 0 ≠ d := Nat.ne_of_lt hd_pos
    simp [hne]
  calc
    2 = ({0, d} : Finset Nat).card := hpair_card.symm
    _ ≤ P.support.card := Finset.card_le_card hpair_subset

/-- Constant-term and degree reachability facts imply the strict `‖f‖₂`
lower bound used by the BHKS auxiliary-factor positivity argument. -/
theorem one_lt_l2norm_toPolynomial_of_const_degree
    {f : Hex.ZPoly}
    (hconst : f.coeff 0 ≠ 0)
    (hdeg : 1 ≤ bhksDegree f) :
    1 < HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) :=
  one_lt_l2norm_toPolynomial_of_two_le_support
    (two_le_support_card_of_const_degree hconst hdeg)

/-- The BHKS degree parameter agrees with the canonical lift degree
`(Hex.ZPoly.toMonic core).degree`.  Both unfold to `core.degree?.getD 0`, so the
positive-degree premise threaded by the Hensel-lift pipeline (`toMonicLiftData`,
`toMonic_monic_isMonic_of_pos_degree`) is the same `Nat` as `1 ≤ bhksDegree core`. -/
theorem bhksDegree_eq_toMonic_degree (core : Hex.ZPoly) :
    bhksDegree core = (Hex.ZPoly.toMonic core).degree :=
  (Hex.ZPoly.toMonic_degree core).symm

/-- Positive `bhksDegree` for the reachable square-free core, sourced from the
lift pipeline's own positive-degree premise on `core := (normalizeForFactor f).squareFreeCore`.

The minimal sound hypothesis is `0 < (Hex.ZPoly.toMonic core).degree` — exactly the
`hdeg` premise already threaded by `toMonicLiftData_represents_lifted_of_modP` and the
cap-lift surfaces.  It is **not** derivable from `HasPositiveDimension`
(`1 ≤ liftedFactors.size + f.degree?.getD 0`): for `f = X^5` the visible `X`-power is
stripped by `extractXPower`, so `squareFreeCore = 1` and `bhksDegree squareFreeCore = 0`,
yet `HasPositiveDimension` holds via `f.degree?.getD 0 = 5`.  Consumers must therefore
thread the reachable-core degree premise, not the lattice-dimension surface. -/
theorem one_le_bhksDegree_squareFreeCore_of_toMonic_degree
    (f : Hex.ZPoly)
    (hdeg : 0 < (Hex.ZPoly.toMonic (Hex.normalizeForFactor f).squareFreeCore).degree) :
    1 ≤ bhksDegree (Hex.normalizeForFactor f).squareFreeCore := by
  rw [bhksDegree_eq_toMonic_degree]
  exact hdeg

/-- Reachable-core strict `l2norm` lower bound: the normalized square-free core has a
nonzero constant term (`squareFreeCore_coeff_zero_ne_zero`), so a positive `bhksDegree`
gives at least two support entries and hence `1 < ‖core‖₂`.  This is the reachability
discharge feeding `bhksPaperAuxiliaryFactorReal_pos`. -/
theorem one_lt_l2norm_squareFreeCore
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hdeg : 1 ≤ bhksDegree (Hex.normalizeForFactor f).squareFreeCore) :
    1 < HexPolyZMathlib.l2norm
      (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore) :=
  one_lt_l2norm_toPolynomial_of_const_degree
    (Hex.squareFreeCore_coeff_zero_ne_zero f hf) hdeg

/-- The reachable-core strict `l2norm` lower bound, stated directly from the lift
pipeline's positive-degree premise on the reachable core. -/
theorem one_lt_l2norm_squareFreeCore_of_toMonic_degree
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hdeg : 0 < (Hex.ZPoly.toMonic (Hex.normalizeForFactor f).squareFreeCore).degree) :
    1 < HexPolyZMathlib.l2norm
      (HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).squareFreeCore) :=
  one_lt_l2norm_squareFreeCore f hf
    (one_le_bhksDegree_squareFreeCore_of_toMonic_degree f hdeg)

/-!
### BHKS §5 small-degree side condition

The joint BHKS §5 auxiliary-domination path (`bhksPaperThresholdReal_chain_*`,
parent #7506) is *not* valid from `HasPositiveDimension` alone: at `n = 1` the
reduced obligation `L ≤ 4·N·log N` fails (the `core = x+1` instance has
`N = √2`, `L = 2`, `RHS ≈ 1.96`).  The gating fact the path actually needs is
`2 ≤ bhksDegree core`.

This is a genuine reachability fact, not a free hypothesis: the recombination /
cap-lift surface is only entered with at least two lifted local factors (the
executable guard `2 ≤ primeData.factorsModP.size`, mirrored by
`d.liftedFactors.size = primeData.factorsModP.size`).  Each lifted factor has
positive transported degree, and the full recovered candidate over *all* lifted
factors reconstructs `core`, so its degree is the sum of at least two positive
local-factor degrees.  A linear core has a single local factor and never reaches
recombination — so the `n = 1` failure case is unreachable, exactly as the
parent issue's boundary caveat predicted. -/

/-- The full recovered candidate over *all* lifted local factors has degree at
least two whenever there are at least two factors, each of positive transported
degree.  This is the combinatorial core of the BHKS §5 small-degree side
condition: its degree is the sum over `Finset.univ` of the per-factor degrees
(`natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum`), a sum of at least two
strictly positive terms. -/
theorem two_le_natDegree_liftedRecoveryCandidate_univ
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hpos : ∀ i : LiftedFactorIndex d,
        0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hsize : 2 ≤ d.liftedFactors.size) :
    2 ≤ (HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core d
            (Finset.univ : LiftedFactorSubset d))).natDegree := by
  rw [natDegree_toPolynomial_liftedRecoveryCandidate_eq_sum
        hcore_lc_pos hd_modulus hd_liftedFactor_monic Finset.univ]
  have hcard : 2 ≤ (Finset.univ : LiftedFactorSubset d).card := by
    rw [Finset.card_univ, Fintype.card_fin]; exact hsize
  calc
    2 ≤ (Finset.univ : LiftedFactorSubset d).card := hcard
    _ = ∑ _i ∈ (Finset.univ : LiftedFactorSubset d), 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ (Finset.univ : LiftedFactorSubset d),
          (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree :=
        Finset.sum_le_sum (fun i _ => hpos i)

/-- **BHKS §5 small-degree side condition.**  Given the degree-preserving full
recovery `hrecover` (the recombination of all lifted factors reconstructs the
core's degree) together with the recombination reachability data — at least two
lifted local factors, each monic of positive transported degree — the core has
`2 ≤ bhksDegree core`.

`hrecover`, `hsize`, `hpos` and the monicity premise are the reachable facts the
cap-lift wrapper threads (the executable recombination guard supplies `hsize`;
`toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData` and
`toMonicLiftData_liftedFactor_monic` supply `hpos`/monicity; the precision-gated
full recovery supplies `hrecover`).  This is the fact the joint
`bhksPaperThresholdReal_chain_*_joint` path consumes in place of the unsound
`HasPositiveDimension` premise. -/
theorem two_le_bhksDegree_of_liftedRecoveryCandidate_univ
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hrecover :
      (HexPolyZMathlib.toPolynomial
          (liftedRecoveryCandidate core d
            (Finset.univ : LiftedFactorSubset d))).natDegree =
        bhksDegree core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hpos : ∀ i : LiftedFactorIndex d,
        0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hsize : 2 ≤ d.liftedFactors.size) :
    2 ≤ bhksDegree core := by
  rw [← hrecover]
  exact two_le_natDegree_liftedRecoveryCandidate_univ
    hcore_lc_pos hd_modulus hd_liftedFactor_monic hpos hsize

private theorem l2norm_log_nonneg (f : Hex.ZPoly) :
    0 ≤ Real.log (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) := by
  let x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)
  have hx_nonneg : 0 ≤ x := by
    unfold x HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  by_cases hx_zero : x = 0
  · simp [x, hx_zero]
  have hP_ne : HexPolyZMathlib.toPolynomial f ≠ 0 := by
    intro hP
    apply hx_zero
    unfold x HexPolyZMathlib.l2norm
    simp [hP]
  exact Real.log_nonneg (one_le_l2norm_toPolynomial_of_ne_zero hP_ne)

/-- The paper degree factor `n` is non-negative as a real. -/
theorem bhksPaperDegreeFactorReal_nonneg (f : Hex.ZPoly) :
    0 ≤ bhksPaperDegreeFactorReal f := by
  unfold bhksPaperDegreeFactorReal
  exact_mod_cast Nat.zero_le (bhksDegree f)

/--
The paper `(2C)^(n^2)` factor is non-negative whenever the project constant
`C` is non-negative.
-/
theorem bhksPaperConstantFactorReal_nonneg
    (f : Hex.ZPoly) {C : ℝ} (hC_nonneg : 0 ≤ C) :
    0 ≤ bhksPaperConstantFactorReal f C := by
  unfold bhksPaperConstantFactorReal
  exact pow_nonneg (by nlinarith) _

/-- The paper `‖f‖₂^(2n-1)` factor is non-negative. -/
theorem bhksPaperCoeffNormFactorReal_nonneg (f : Hex.ZPoly) :
    0 ≤ bhksPaperCoeffNormFactorReal f := by
  unfold bhksPaperCoeffNormFactorReal HexPolyZMathlib.l2norm
  exact pow_nonneg (Real.sqrt_nonneg _) _

/-- The paper `(log ‖f‖₂)^n` factor is non-negative. -/
theorem bhksPaperLogFactorReal_nonneg (f : Hex.ZPoly) :
    0 ≤ bhksPaperLogFactorReal f := by
  unfold bhksPaperLogFactorReal
  exact pow_nonneg (l2norm_log_nonneg f) _

/--
The product-shaped BHKS paper threshold is non-negative under the project
`0 ≤ C` convention.
-/
theorem bhksPaperThresholdReal_nonneg
    (f : Hex.ZPoly) {C : ℝ} (hC_nonneg : 0 ≤ C) :
    0 ≤ bhksPaperThresholdReal f C := by
  unfold bhksPaperThresholdReal
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (bhksPaperDegreeFactorReal_nonneg f)
        (bhksPaperConstantFactorReal_nonneg f hC_nonneg))
      (bhksPaperCoeffNormFactorReal_nonneg f))
    (bhksPaperLogFactorReal_nonneg f)

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
The same squared-norm bound with the `+ 1` slack used by the executable BHKS
coefficient factor.
-/
theorem l2norm_toPolynomial_sq_le_coeffNormSq_add_one (f : Hex.ZPoly) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ 2 ≤
      (Hex.ZPoly.coeffNormSq f + 1 : ℝ) := by
  exact le_trans (l2norm_toPolynomial_sq_le_coeffNormSq f) (by norm_num)

private theorem log_l2norm_le_log2_coeffNormSq_add_one (f : Hex.ZPoly) :
    Real.log (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ≤
      (Nat.log2 (Hex.ZPoly.coeffNormSq f + 1) : ℝ) := by
  let x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)
  let A := Hex.ZPoly.coeffNormSq f + 1
  have hx_nonneg : 0 ≤ x := by
    unfold x HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  have hsq : x ^ 2 ≤ (A : ℝ) := by
    simpa [x, A] using l2norm_toPolynomial_sq_le_coeffNormSq_add_one f
  by_cases hx_zero : x = 0
  · simp [x, hx_zero]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_zero)
  have hlog_sq :
      Real.log x ≤ Real.log (A : ℝ) / 2 := by
    have hlog_le : Real.log (x ^ 2) ≤ Real.log (A : ℝ) :=
      Real.log_le_log (sq_pos_of_pos hx_pos) hsq
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
    have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) := by
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
  have hsq := l2norm_toPolynomial_sq_le_coeffNormSq_add_one f
  have hA1 : (1 : ℝ) ≤ (bhksSumSquared f + 1 : ℝ) := by norm_num
  simpa [bhksPaperCoeffNormFactorReal, bhksCoeffNormFactor] using
    nonneg_pow_two_sub_one_le_pow_of_sq_le
      (x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f))
      (A := (bhksSumSquared f + 1 : ℝ))
      (n := bhksDegree f) hx_nonneg hA1 hsq

/--
Real-l2-norm monotonicity feeding the BHKS coefficient-norm factor: for a
nonzero polynomial whose Euclidean norm is at least one, raising to any
exponent at most `2n − 1` (with `n = bhksDegree f`) lands inside
`bhksPaperCoeffNormFactorReal f = ‖f‖₂^(2n−1)`.

Concretely combines `one_le_l2norm_toPolynomial_of_ne_zero` with
`pow_le_pow_right₀` and the definition of `bhksPaperCoeffNormFactorReal`.
The intended caller has already bounded an auxiliary polynomial's `natDegree`
by `2n − 1` via the BadVectorAuxiliary degree bounds and now wants to convert
`‖f‖₂^aux.natDegree` to the paper-threshold factor on the RHS.
-/
theorem l2norm_pow_le_bhksPaperCoeffNormFactorReal
    {f : Hex.ZPoly} (hf : HexPolyZMathlib.toPolynomial f ≠ 0)
    {k : Nat} (hk : k ≤ 2 * bhksDegree f - 1) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) ^ k ≤
      bhksPaperCoeffNormFactorReal f := by
  unfold bhksPaperCoeffNormFactorReal
  exact pow_le_pow_right₀ (one_le_l2norm_toPolynomial_of_ne_zero hf) hk

/--
The executable coefficient L2 bound raised to any exponent below the BHKS degree
is absorbed by the paper coefficient-norm factor.
-/
theorem coeffL2NormBound_pow_le_bhksPaperCoeffNormFactorReal
    {f : Hex.ZPoly} (hf : HexPolyZMathlib.toPolynomial f ≠ 0)
    {k : Nat} (hk : k + 1 ≤ bhksDegree f) :
    (Hex.ZPoly.coeffL2NormBound f : ℝ) ^ k ≤
      bhksPaperCoeffNormFactorReal f := by
  let c := Hex.ZPoly.coeffL2NormBound f
  let x := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)
  let M := Hex.ZPoly.coeffNormSq f
  have hx_one : 1 ≤ x := by
    simpa [x] using one_le_l2norm_toPolynomial_of_ne_zero hf
  have hx_sq : x ^ 2 = (M : ℝ) := by
    simpa [x, M] using HexPolyZMathlib.l2norm_toPolynomial_sq_eq_coeffNormSq f
  by_cases hM_small : M ≤ 1
  · have hc_sq_nat : c ^ 2 ≤ 2 := by
      have h : c ^ 2 ≤ 2 * M := by
        simpa [c, M] using Hex.ZPoly.coeffL2NormBound_sq_le_two_mul_coeffNormSq f
      omega
    have hc_le_one_nat : c ≤ 1 := by
      rw [Nat.pow_two] at hc_sq_nat
      nlinarith
    have hc_pow_le_one : (c : ℝ) ^ k ≤ 1 := by
      simpa using
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (c : ℝ))
          (by exact_mod_cast hc_le_one_nat : (c : ℝ) ≤ 1) k)
    have hone_le_factor : (1 : ℝ) ≤ bhksPaperCoeffNormFactorReal f := by
      unfold bhksPaperCoeffNormFactorReal
      simpa [x] using
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx_one (2 * bhksDegree f - 1))
    exact hc_pow_le_one.trans hone_le_factor
  · have hM_ge_two : 2 ≤ M := by omega
    have hc_sq_real : (c : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
      have h := Hex.ZPoly.coeffL2NormBound_sq_le_two_mul_coeffNormSq f
      change (c ^ 2 : Nat) ≤ 2 * M at h
      exact_mod_cast h
    have htwoM_le_Msq : 2 * (M : ℝ) ≤ (M : ℝ) * (M : ℝ) := by
      have hM_ge_two_real : (2 : ℝ) ≤ M := by exact_mod_cast hM_ge_two
      nlinarith
    have hc_sq_le_x_four : (c : ℝ) ^ 2 ≤ (x ^ 2) ^ 2 := by
      calc
        (c : ℝ) ^ 2 ≤ 2 * (M : ℝ) := hc_sq_real
        _ ≤ (M : ℝ) * (M : ℝ) := htwoM_le_Msq
        _ = (x ^ 2) ^ 2 := by rw [hx_sq]; ring
    have hc_le_x_sq : (c : ℝ) ≤ x ^ 2 := by
      have h_abs := (sq_le_sq).mp hc_sq_le_x_four
      simpa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ)),
        abs_of_nonneg (sq_nonneg x)] using h_abs
    have hc_pow_le_x_pow :
        (c : ℝ) ^ k ≤ x ^ (2 * k) := by
      calc
        (c : ℝ) ^ k ≤ (x ^ 2) ^ k :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (c : ℝ)) hc_le_x_sq k
        _ = x ^ (2 * k) := by rw [pow_mul]
    have hk_exp : 2 * k ≤ 2 * bhksDegree f - 1 := by omega
    exact hc_pow_le_x_pow.trans
      (l2norm_pow_le_bhksPaperCoeffNormFactorReal (f := f) hf hk_exp)

/--
Named analytic target for bounding the BHKS logarithmic factor by the packaged
`Nat.log2` factor.
-/
theorem bhksPaperLogFactorReal_le_log2Factor (f : Hex.ZPoly) :
    bhksPaperLogFactorReal f ≤ (bhksLog2Factor f : ℝ) := by
  have hlog_nonneg := l2norm_log_nonneg f
  have hlog_le := log_l2norm_le_log2_coeffNormSq_add_one f
  simpa [bhksPaperLogFactorReal, bhksLog2Factor] using
    pow_le_pow_left₀ hlog_nonneg hlog_le (bhksDegree f)

/--
The product-shaped BHKS paper threshold is bounded by the packaged integer
threshold expression used by the executable cap.
-/
theorem bhksPaperThresholdReal_le_thresholdNatBound
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2) :
    bhksPaperThresholdReal f C ≤ (bhksThresholdNatBound f : ℝ) := by
  have hdegree :
      bhksPaperDegreeFactorReal f ≤ (bhksDegreeFactor f : ℝ) := by
    rw [bhksPaperDegreeFactorReal_eq_natCast]
  have hconstant :=
    bhksPaperConstantFactorReal_le_fourPowFactor f C hC_nonneg hC
  have hcoeff := bhksPaperCoeffNormFactorReal_le_coeffNormFactor f
  have hlog := bhksPaperLogFactorReal_le_log2Factor f
  have hconstant_nonneg : 0 ≤ bhksPaperConstantFactorReal f C :=
    bhksPaperConstantFactorReal_nonneg f hC_nonneg
  have hcoeff_nonneg : 0 ≤ bhksPaperCoeffNormFactorReal f :=
    bhksPaperCoeffNormFactorReal_nonneg f
  have hlog_nonneg : 0 ≤ bhksPaperLogFactorReal f :=
    bhksPaperLogFactorReal_nonneg f
  have hdegree_bound_nonneg : 0 ≤ (bhksDegreeFactor f : ℝ) := by
    exact_mod_cast Nat.zero_le (bhksDegreeFactor f)
  have hdegree_constant_bound_nonneg :
      0 ≤ (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) :=
    mul_nonneg hdegree_bound_nonneg (by exact_mod_cast Nat.zero_le (bhksFourPowFactor f))
  have hdegree_constant_coeff_bound_nonneg :
      0 ≤ (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) *
        (bhksCoeffNormFactor f : ℝ) :=
    mul_nonneg hdegree_constant_bound_nonneg
      (by exact_mod_cast Nat.zero_le (bhksCoeffNormFactor f))
  have hdegree_constant :
      bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C ≤
        (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) :=
    mul_le_mul hdegree hconstant hconstant_nonneg hdegree_bound_nonneg
  have hdegree_constant_coeff :
      bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
          bhksPaperCoeffNormFactorReal f ≤
        (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) *
          (bhksCoeffNormFactor f : ℝ) :=
    mul_le_mul hdegree_constant hcoeff hcoeff_nonneg hdegree_constant_bound_nonneg
  have hproduct :
      bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
          bhksPaperCoeffNormFactorReal f * bhksPaperLogFactorReal f ≤
        (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) *
          (bhksCoeffNormFactor f : ℝ) * (bhksLog2Factor f : ℝ) :=
    mul_le_mul hdegree_constant_coeff hlog hlog_nonneg
      hdegree_constant_coeff_bound_nonneg
  have hproduct_le_bound :
      (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) *
          (bhksCoeffNormFactor f : ℝ) * (bhksLog2Factor f : ℝ) ≤
        (bhksThresholdNatBound f : ℝ) := by
    simp [bhksThresholdNatBound]
  exact hproduct.trans hproduct_le_bound

/--
The executable BHKS cap dominates the product-shaped BHKS paper threshold.
-/
theorem bhksPaperThresholdReal_le_bhksBound
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2) :
    bhksPaperThresholdReal f C ≤ (Hex.bhksBound f : ℝ) :=
  (bhksPaperThresholdReal_le_thresholdNatBound f C hC_nonneg hC).trans
    (bhksThresholdNatBound_real_le_bhksBound f)

/--
Factored discharge of the paper-threshold inequality
`coeffPow * auxPow ≤ bhksPaperThresholdReal f C`.

Given separate bounds on the two LHS factors against complementary RHS partial
products — `coeffPow` bounded by `bhksPaperCoeffNormFactorReal f` and `auxPow`
bounded by the product of the remaining three paper factors
(`bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
bhksPaperLogFactorReal f`) — `mul_le_mul` combines them into the full
paper-threshold inequality.

This is the structural piece a caller needs to decompose the BHKS Theorem 5.2
`coeffL2NormBound^aux.natDegree * auxiliaryBound^input.natDegree ≤
bhksPaperThresholdReal core C` obligation into two tractable sub-bounds:
the coefficient-power piece against `‖f‖₂^(2n-1)`, and the
auxiliary-power piece against `n · (2C)^(n²) · (log ‖f‖₂)^n`.
-/
theorem bhksPaperThresholdReal_ge_of_factored_bounds
    (f : Hex.ZPoly) (C : ℝ)
    {coeffPow auxPow : ℝ}
    (h_aux_nn : 0 ≤ auxPow)
    (h_coeff : coeffPow ≤ bhksPaperCoeffNormFactorReal f)
    (h_aux :
      auxPow ≤
        bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
          bhksPaperLogFactorReal f) :
    coeffPow * auxPow ≤ bhksPaperThresholdReal f C := by
  have h_paperCoeff_nn : 0 ≤ bhksPaperCoeffNormFactorReal f := by
    unfold bhksPaperCoeffNormFactorReal
    exact pow_nonneg (by unfold HexPolyZMathlib.l2norm; exact Real.sqrt_nonneg _) _
  have hmul :
      coeffPow * auxPow ≤
        bhksPaperCoeffNormFactorReal f *
          (bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
            bhksPaperLogFactorReal f) :=
    mul_le_mul h_coeff h_aux h_aux_nn h_paperCoeff_nn
  calc coeffPow * auxPow
      ≤ bhksPaperCoeffNormFactorReal f *
          (bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
            bhksPaperLogFactorReal f) := hmul
    _ = bhksPaperThresholdReal f C := by
        unfold bhksPaperThresholdReal; ring

/--
Named auxiliary-side product of the BHKS Theorem 5.2 paper threshold:
`n · (2C)^(n²) · (log ‖f‖₂)^n`.

This packages the three paper factors that the auxiliary-power sub-bound
(`auxiliaryBound^input.natDegree ≤ ...`) must dominate, leaving the
coefficient-norm factor `‖f‖₂^(2n-1)` as the separate sub-bound target.
-/
noncomputable def bhksPaperAuxiliaryFactorReal (f : Hex.ZPoly) (C : ℝ) : ℝ :=
  bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
    bhksPaperLogFactorReal f

/--
Named-target unfold for `bhksPaperAuxiliaryFactorReal`.

Lets callers using the unfolded three-way product `bhksPaperDegreeFactorReal f *
bhksPaperConstantFactorReal f C * bhksPaperLogFactorReal f` rewrite to the named
target (or vice versa) without unfolding the definition manually.  Useful for
adapting hypotheses to whichever sibling of
`bhksPaperThresholdReal_chain_lt_p_pow_kLocalFactorDegree_factored` /
`_factored'` is in scope at the call site.
-/
theorem bhksPaperAuxiliaryFactorReal_eq_product (f : Hex.ZPoly) (C : ℝ) :
    bhksPaperAuxiliaryFactorReal f C =
      bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
        bhksPaperLogFactorReal f := rfl

/-- The full paper threshold splits into coefficient and auxiliary factors. -/
theorem bhksPaperThresholdReal_eq_coeffNorm_mul_auxiliary
    (f : Hex.ZPoly) (C : ℝ) :
    bhksPaperThresholdReal f C =
      bhksPaperCoeffNormFactorReal f * bhksPaperAuxiliaryFactorReal f C := by
  unfold bhksPaperThresholdReal bhksPaperAuxiliaryFactorReal
  ring

/--
The auxiliary-side product is non-negative under the project `0 ≤ C`
convention.
-/
theorem bhksPaperAuxiliaryFactorReal_nonneg
    (f : Hex.ZPoly) {C : ℝ} (hC_nonneg : 0 ≤ C) :
    0 ≤ bhksPaperAuxiliaryFactorReal f C := by
  unfold bhksPaperAuxiliaryFactorReal
  exact mul_nonneg
    (mul_nonneg
      (bhksPaperDegreeFactorReal_nonneg f)
      (bhksPaperConstantFactorReal_nonneg f hC_nonneg))
    (bhksPaperLogFactorReal_nonneg f)

/--
The auxiliary-side product `n · (2C)^(n²) · (log ‖f‖₂)^n` is strictly positive
once the threshold degeneracies are excluded: `0 < C` makes the `(2C)^(n²)`
factor positive, `1 ≤ n` makes the degree factor positive, and `1 < ‖f‖₂`
makes `log ‖f‖₂ > 0` (via `Real.log_pos`) so its `n`-th power is positive.

This is the BHKS §5 "log-factor positivity" sub-piece. On the cap-lift surface
the three hypotheses are discharged from reachability: `1 ≤ bhksDegree f` from
`HasPositiveDimension` and the good-prime choice, and `1 < ‖f‖₂` from
`one_lt_l2norm_toPolynomial_of_two_le_support` applied to the x-stripped core.
It certifies that the auxiliary RHS the domination must clear never vanishes,
which is what makes fixing `C := 2` sound rather than degenerate.
-/
theorem bhksPaperAuxiliaryFactorReal_pos
    (f : Hex.ZPoly) {C : ℝ} (hC : 0 < C)
    (hdeg : 1 ≤ bhksDegree f)
    (hnorm : 1 < HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)) :
    0 < bhksPaperAuxiliaryFactorReal f C := by
  unfold bhksPaperAuxiliaryFactorReal bhksPaperDegreeFactorReal
    bhksPaperConstantFactorReal bhksPaperLogFactorReal
  have hdeg_pos : 0 < (bhksDegree f : ℝ) := by exact_mod_cast hdeg
  have hconst_pos : 0 < (2 * C) ^ (bhksDegree f * bhksDegree f) :=
    pow_pos (by linarith) _
  have hlog_pos :
      0 < (Real.log (HexPolyZMathlib.l2norm
        (HexPolyZMathlib.toPolynomial f))) ^ bhksDegree f :=
    pow_pos (Real.log_pos hnorm) _
  exact mul_pos (mul_pos hdeg_pos hconst_pos) hlog_pos

/--
The auxiliary-side paper product is bounded by the packaged integer
auxiliary-side product (`n · 4^(n²) · (log2 (sumSquared + 1))^n`) under the
project `0 ≤ C ≤ 2` convention.
-/
theorem bhksPaperAuxiliaryFactorReal_le_natCast
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2) :
    bhksPaperAuxiliaryFactorReal f C ≤
      ((bhksDegreeFactor f * bhksFourPowFactor f * bhksLog2Factor f : Nat) : ℝ) := by
  unfold bhksPaperAuxiliaryFactorReal
  have hdegree :
      bhksPaperDegreeFactorReal f ≤ (bhksDegreeFactor f : ℝ) := by
    rw [bhksPaperDegreeFactorReal_eq_natCast]
  have hconstant :=
    bhksPaperConstantFactorReal_le_fourPowFactor f C hC_nonneg hC
  have hlog := bhksPaperLogFactorReal_le_log2Factor f
  have hconstant_nonneg : 0 ≤ bhksPaperConstantFactorReal f C :=
    bhksPaperConstantFactorReal_nonneg f hC_nonneg
  have hlog_nonneg : 0 ≤ bhksPaperLogFactorReal f :=
    bhksPaperLogFactorReal_nonneg f
  have hdegree_bound_nonneg : 0 ≤ (bhksDegreeFactor f : ℝ) := by
    exact_mod_cast Nat.zero_le (bhksDegreeFactor f)
  have hdegree_constant_bound_nonneg :
      0 ≤ (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) :=
    mul_nonneg hdegree_bound_nonneg
      (by exact_mod_cast Nat.zero_le (bhksFourPowFactor f))
  have hdegree_constant :
      bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C ≤
        (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) :=
    mul_le_mul hdegree hconstant hconstant_nonneg hdegree_bound_nonneg
  have hproduct :
      bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
          bhksPaperLogFactorReal f ≤
        (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) *
          (bhksLog2Factor f : ℝ) :=
    mul_le_mul hdegree_constant hlog hlog_nonneg
      hdegree_constant_bound_nonneg
  calc
    bhksPaperDegreeFactorReal f * bhksPaperConstantFactorReal f C *
        bhksPaperLogFactorReal f
      ≤ (bhksDegreeFactor f : ℝ) * (bhksFourPowFactor f : ℝ) *
          (bhksLog2Factor f : ℝ) := hproduct
    _ = ((bhksDegreeFactor f * bhksFourPowFactor f * bhksLog2Factor f : Nat) : ℝ) := by
        push_cast; ring

/--
Restatement of `bhksPaperThresholdReal_ge_of_factored_bounds` against the
named `bhksPaperAuxiliaryFactorReal` target.  Callers proving the BHKS
Theorem 5.2 sub-bounds can hit this RHS directly instead of unfolding the
three-way product.
-/
theorem bhksPaperThresholdReal_ge_of_factored_bounds'
    (f : Hex.ZPoly) (C : ℝ)
    {coeffPow auxPow : ℝ}
    (h_aux_nn : 0 ≤ auxPow)
    (h_coeff : coeffPow ≤ bhksPaperCoeffNormFactorReal f)
    (h_aux : auxPow ≤ bhksPaperAuxiliaryFactorReal f C) :
    coeffPow * auxPow ≤ bhksPaperThresholdReal f C :=
  bhksPaperThresholdReal_ge_of_factored_bounds f C h_aux_nn h_coeff
    (by simpa [bhksPaperAuxiliaryFactorReal] using h_aux)

/--
The packaged BHKS cap remains available alongside the executable Mignotte
coefficient bound through a single max expression.  This lightweight lemma is
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

/-- The combined executable `factorFast` precision cap is at least one. -/
theorem one_le_factorFastPrecisionCap (f : Hex.ZPoly) :
    1 ≤ Hex.factorFastPrecisionCap f :=
  le_trans (one_le_bhksBound f) (bhksBound_le_factorFastPrecisionCap f)

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

/--
Single-hypothesis dominance bundle for HO-4 termination callers.

At any precision `a` with `factorFastPrecisionCap f ≤ a`, all three real-valued
BHKS quantities are dominated by `(a : ℝ)`:

* the product-shaped BHKS paper threshold `bhksPaperThresholdReal f C`
  (under the project `0 ≤ C ≤ 2` constant convention from
  `bhksPaperConstantFactorReal_le_fourPowFactor`),
* the executable BHKS precision cap `Hex.bhksBound f`,
* the executable Mignotte coefficient bound `Hex.ZPoly.defaultFactorCoeffBound f`.

This packages the BHKS Theorem 5.2 separation precondition and the Mignotte
reconstruction precondition into a single hypothesis, so leaf-theorem proofs
do not have to thread three independent dominance lemmas at every use site.
-/
theorem factorFastPrecisionCap_real_dominates_bhksPaperThreshold
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a) :
    bhksPaperThresholdReal f C ≤ (a : ℝ) ∧
      (Hex.bhksBound f : ℝ) ≤ (a : ℝ) ∧
        (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤ (a : ℝ) := by
  have hbhks : (Hex.bhksBound f : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (le_trans (bhksBound_le_factorFastPrecisionCap f) ha)
  have hmignotte : (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (le_trans (defaultFactorCoeffBound_le_factorFastPrecisionCap f) ha)
  exact ⟨(bhksPaperThresholdReal_le_bhksBound f C hC_nonneg hC).trans hbhks,
    hbhks, hmignotte⟩

end HexBerlekampZassenhausMathlib
