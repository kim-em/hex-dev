module

public import HexBerlekampZassenhausMathlib.BadVector
public import HexBerlekampZassenhausMathlib.BadVectorAuxiliary
public import HexBerlekampZassenhausMathlib.BHKSBound

public section

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
theorem factorFastPrecisionCap_dominates
    (f : Hex.ZPoly) {a : Nat} (ha : Hex.factorFastPrecisionCap f ≤ a) :
    Hex.bhksBound f ≤ a ∧
      Hex.ZPoly.defaultFactorCoeffBound f ≤ a := by
  exact ⟨le_trans (bhksBound_le_factorFastPrecisionCap f) ha,
    le_trans (defaultFactorCoeffBound_le_factorFastPrecisionCap f) ha⟩

/--
Any precision at least `factorFastPrecisionCap f` dominates both executable
bounds needed by the fast-path termination proof, in the real-valued form used
by the analytic separation and reconstruction lemmas.
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
`defaultFactorCoeffBound f = 1`, so `2 * 1 = 2 = 2 ^ 1`).  Callers needing
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
`LiftData`-shaped wrapper for the Mignotte precision side condition consumed
by `BHKS.ForwardRecoveryInputs`: if the lift precision strictly exceeds the
fast-path cap, then the stored modulus `d.p ^ d.k` exceeds twice the executable
Mignotte coefficient bound.
-/
theorem mignotte_precision_of_liftData_factorFastPrecisionCap_lt
    (f : Hex.ZPoly) (d : Hex.LiftData) (hp : 2 ≤ d.p)
    (hcap : Hex.factorFastPrecisionCap f < d.k) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k :=
  mignotte_precision_of_factorFastPrecisionCap_lt f hp hcap

/--
Unconditional cap-successor form: at precision `factorFastPrecisionCap f + 1`,
the Mignotte precision side condition holds for any modulus `p ≥ 2`.

This is the canonical caller-facing way to obtain `2 * B < p ^ k`: pick
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
`LiftData`-shaped successor form for cap-loop callers whose stored precision is
exactly `factorFastPrecisionCap f + 1`.
-/
theorem mignotte_precision_of_liftData_factorFastPrecisionCap_succ
    (f : Hex.ZPoly) (d : Hex.LiftData) (hp : 2 ≤ d.p)
    (hk : d.k = Hex.factorFastPrecisionCap f + 1) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k := by
  rw [hk]
  exact mignotte_precision_at_factorFastPrecisionCap_succ f hp

/--
Mignotte-precision discharge at the executable precision returned by
`precisionForCoeffBound (defaultFactorCoeffBound f) p`.  This is the cleanest
call shape for `ForwardRecoveryInputs` constructors that lift to exactly the
Mignotte bound: the stored precision is `precisionForCoeffBound B p` for
`B = defaultFactorCoeffBound f`, and the Mignotte side condition follows
directly from `Hex.precisionForCoeffBound_spec`.
-/
theorem mignotte_precision_at_precisionForCoeffBound_defaultFactorCoeffBound
    (f : Hex.ZPoly) {p : Nat} (hp : 2 ≤ p) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f <
      p ^ Hex.precisionForCoeffBound (Hex.ZPoly.defaultFactorCoeffBound f) p :=
  Hex.precisionForCoeffBound_spec hp (Hex.ZPoly.defaultFactorCoeffBound f)

/--
Mignotte-precision discharge at the executable precision returned by
`precisionForCoeffBound (factorFastPrecisionCap f) p`.  This is the call shape
used by the public `factorFast` path: the stored precision is
`precisionForCoeffBound B p` for `B = factorFastPrecisionCap f`, and the
Mignotte side condition follows from `Hex.precisionForCoeffBound_spec` chained
with `defaultFactorCoeffBound_le_factorFastPrecisionCap`.
-/
theorem mignotte_precision_at_precisionForCoeffBound_factorFastPrecisionCap
    (f : Hex.ZPoly) {p : Nat} (hp : 2 ≤ p) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f <
      p ^ Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) p := by
  have h_cap :
      2 * Hex.factorFastPrecisionCap f <
        p ^ Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) p :=
    Hex.precisionForCoeffBound_spec hp (Hex.factorFastPrecisionCap f)
  have h_bound :
      Hex.ZPoly.defaultFactorCoeffBound f ≤ Hex.factorFastPrecisionCap f :=
    Hex.defaultFactorCoeffBound_le_factorFastPrecisionCap f
  omega

/--
`LiftData`-shaped wrapper for the Mignotte precision side condition consumed by
`BHKS.ForwardRecoveryInputs`, instantiated at the executable precision returned
by `henselLiftData f (precisionForCoeffBound (defaultFactorCoeffBound f) p) primeData`.
The stored precision matches `precisionForCoeffBound (defaultFactorCoeffBound f) d.p`,
and the Mignotte side condition follows directly from
`mignotte_precision_at_precisionForCoeffBound_defaultFactorCoeffBound`.
-/
theorem mignotte_precision_of_liftData_precisionForCoeffBound_defaultFactorCoeffBound
    (f : Hex.ZPoly) (d : Hex.LiftData) (hp : 2 ≤ d.p)
    (hk : d.k =
      Hex.precisionForCoeffBound (Hex.ZPoly.defaultFactorCoeffBound f) d.p) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k := by
  rw [hk]
  exact mignotte_precision_at_precisionForCoeffBound_defaultFactorCoeffBound f hp

/--
`LiftData`-shaped wrapper for the Mignotte precision side condition consumed by
`BHKS.ForwardRecoveryInputs`, instantiated at the executable precision returned
by `henselLiftData f (precisionForCoeffBound (factorFastPrecisionCap f) p) primeData`.
This is the public `factorFast` call shape: the stored precision matches
`precisionForCoeffBound (factorFastPrecisionCap f) d.p`, and the Mignotte side
condition follows from
`mignotte_precision_at_precisionForCoeffBound_factorFastPrecisionCap`.
-/
theorem mignotte_precision_of_liftData_precisionForCoeffBound_factorFastPrecisionCap
    (f : Hex.ZPoly) (d : Hex.LiftData) (hp : 2 ≤ d.p)
    (hk : d.k =
      Hex.precisionForCoeffBound (Hex.factorFastPrecisionCap f) d.p) :
    2 * Hex.ZPoly.defaultFactorCoeffBound f < d.p ^ d.k := by
  rw [hk]
  exact mignotte_precision_at_precisionForCoeffBound_factorFastPrecisionCap f hp

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

/--
Exact-cap form of `bhksPaperThresholdReal_le_of_factorFastPrecisionCap_le`.
This is the canonical BHKS threshold fact for callers working at the
executable fast-path cap itself.
-/
theorem bhksPaperThresholdReal_le_factorFastPrecisionCap
    (f : Hex.ZPoly) (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2) :
    bhksPaperThresholdReal f C ≤ (Hex.factorFastPrecisionCap f : ℝ) :=
  bhksPaperThresholdReal_le_of_factorFastPrecisionCap_le
    f C hC_nonneg hC (Nat.le_refl _)

namespace ExecutableBadVectorWitness

/--
The executable coefficient L2 bound of the source polynomial controls the
Mathlib-facing input polynomial carried by any bad-vector witness.

This is the concrete input-side bound used by
`l2norm_product_lt_divisor_of_l2norm_bounds`; the auxiliary side and strict
cap arithmetic can be supplied independently.
-/
theorem inputPolynomial_l2norm_le_coeffL2NormBound
    (W : ExecutableBadVectorWitness) :
    HexPolyZMathlib.l2norm W.inputPolynomial ≤
      (Hex.ZPoly.coeffL2NormBound W.input : ℝ) := by
  simpa [ExecutableBadVectorWitness.inputPolynomial] using
    l2norm_toPolynomial_le_coeffL2NormBound W.input

/--
Turn separate l2-norm bounds for the input and auxiliary polynomials into the
strict Hadamard/l2norm comparison consumed by the resultant contradiction.

This is the generic witness-level arithmetic step used by the actual-cap
`factorFast` witness: auxiliary-polynomial norm estimates discharge
`hauxiliary`, input norm estimates discharge `hinput`, and the cap arithmetic
discharges `hstrict`.
-/
theorem l2norm_product_lt_divisor_of_l2norm_bounds
    (W : ExecutableBadVectorWitness) {inputBound auxiliaryBound : ℝ}
    (hinput : HexPolyZMathlib.l2norm W.inputPolynomial ≤ inputBound)
    (hauxiliary : HexPolyZMathlib.l2norm W.auxiliaryPolynomial ≤ auxiliaryBound)
    (hstrict :
      inputBound ^ W.auxiliaryPolynomial.natDegree *
          auxiliaryBound ^ W.inputPolynomial.natDegree <
        (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    (HexPolyZMathlib.l2norm W.inputPolynomial) ^
        W.auxiliaryPolynomial.natDegree *
      (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
        W.inputPolynomial.natDegree <
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) := by
  have hinput_pow :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree ≤
        inputBound ^ W.auxiliaryPolynomial.natDegree := by
    have hnonneg : 0 ≤ HexPolyZMathlib.l2norm W.inputPolynomial := by
      unfold HexPolyZMathlib.l2norm
      exact Real.sqrt_nonneg _
    exact pow_le_pow_left₀ hnonneg hinput _
  have hauxiliary_pow :
      (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree ≤
        auxiliaryBound ^ W.inputPolynomial.natDegree := by
    have hnonneg : 0 ≤ HexPolyZMathlib.l2norm W.auxiliaryPolynomial := by
      unfold HexPolyZMathlib.l2norm
      exact Real.sqrt_nonneg _
    exact pow_le_pow_left₀ hnonneg hauxiliary _
  have hauxiliary_pow_nonneg :
      0 ≤ (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree := by
    have hnonneg : 0 ≤ HexPolyZMathlib.l2norm W.auxiliaryPolynomial := by
      unfold HexPolyZMathlib.l2norm
      exact Real.sqrt_nonneg _
    exact pow_nonneg hnonneg _
  have hinput_bound_nonneg : 0 ≤ inputBound := by
    have hnonneg : 0 ≤ HexPolyZMathlib.l2norm W.inputPolynomial := by
      unfold HexPolyZMathlib.l2norm
      exact Real.sqrt_nonneg _
    exact hnonneg.trans hinput
  exact lt_of_le_of_lt
    (mul_le_mul hinput_pow hauxiliary_pow
      hauxiliary_pow_nonneg
      (pow_nonneg hinput_bound_nonneg _))
    hstrict

/--
Specialisation of `l2norm_product_lt_divisor_of_l2norm_bounds` that
discharges the input bound automatically from
`inputPolynomial_l2norm_le_coeffL2NormBound`.

Callers needing the strict Hadamard/l2norm comparison only have to supply the
auxiliary-polynomial l2 bound and the cap arithmetic against
`coeffL2NormBound W.input`; the input-side l2 bound is supplied by the
witness-level Cauchy–Schwarz fact carried by every executable bad-vector
witness.
-/
theorem l2norm_product_lt_divisor_of_auxiliary_bound
    (W : ExecutableBadVectorWitness) {auxiliaryBound : ℝ}
    (hauxiliary : HexPolyZMathlib.l2norm W.auxiliaryPolynomial ≤ auxiliaryBound)
    (hstrict :
      (Hex.ZPoly.coeffL2NormBound W.input : ℝ) ^
            W.auxiliaryPolynomial.natDegree *
          auxiliaryBound ^ W.inputPolynomial.natDegree <
        (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    (HexPolyZMathlib.l2norm W.inputPolynomial) ^
        W.auxiliaryPolynomial.natDegree *
      (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
        W.inputPolynomial.natDegree <
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) :=
  l2norm_product_lt_divisor_of_l2norm_bounds W
    (inputPolynomial_l2norm_le_coeffL2NormBound W)
    hauxiliary hstrict

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

/--
BHKS bad-vector norm lower bound against the executable cut radius.

This is the cut-radius-facing form of the existing resultant contradiction:
once the cap arithmetic has reduced every projected vector with squared norm
at most `cutRadiusSq4` to an l2norm upper bound below the modular divisor, a
bad vector must have squared projected norm strictly above `cutRadiusSq4`.

The hypothesis `hnorm_to_l2norm_upper_lt_divisor` is the remaining
paper-threshold arithmetic comparison.  Keeping it explicit lets later work
plug in the `auxiliaryPolynomial_l2norm_sq_le` and `BHKSBound.lean` estimates
without restating the resultant contradiction or the cap-dominance wrapper.
-/
theorem bhks_bad_vector_norm_sq_gt_cutRadiusSq4_of_paperThreshold_le
    (W : ExecutableBadVectorWitness) {a : Nat}
    (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p)
    (hnorm_to_l2norm_upper_lt_divisor :
      (∑ i : Fin W.projectedRows.factorCount,
          ((W.projectedVectorFn h_bad.bhksVector i : ℝ) ^ 2)) ≤
          (W.projectedRows.cutRadiusSq4 : ℝ) →
        (HexPolyZMathlib.l2norm W.inputPolynomial) ^
            W.auxiliaryPolynomial.natDegree *
          (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
            W.inputPolynomial.natDegree <
        (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    (W.projectedRows.cutRadiusSq4 : ℝ) <
      ∑ i : Fin W.projectedRows.factorCount,
        ((W.projectedVectorFn h_bad.bhksVector i : ℝ) ^ 2) := by
  by_contra hnot
  have hnorm_le :
      (∑ i : Fin W.projectedRows.factorCount,
          ((W.projectedVectorFn h_bad.bhksVector i : ℝ) ^ 2)) ≤
          (W.projectedRows.cutRadiusSq4 : ℝ) := by
    exact le_of_not_gt hnot
  exact
    no_bhks_bad_setup_of_factorFastPrecisionCap_le
      W ha C hC_nonneg hC h_bad hp
      (hnorm_to_l2norm_upper_lt_divisor hnorm_le)

/--
Exact-cap bad-vector contradiction wrapper for callers working at
`factorFastPrecisionCap W.input`.
-/
theorem no_bhks_bad_setup_at_factorFastPrecisionCap
    (W : ExecutableBadVectorWitness)
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
  no_bhks_bad_setup_of_factorFastPrecisionCap_le
    W (Nat.le_refl _) C hC_nonneg hC h_bad hp hlt

end ExecutableBadVectorWitness

namespace BHKS

/--
Proof-facing hypotheses for the executable-cap BHKS separation step.

The `bad_setup_of_projected_not_indicator` field is the remaining step from
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

namespace ExecutableCapSeparationHypotheses

/--
Instantiate the cap-separation hypotheses from the packaged
`ProjectedBadVectorSetupBridge` supplied by `BadVector.lean`, plus the
existing cut and resultant-bound side conditions.
-/
@[expose]
def ofProjectedBadVectorSetupBridge
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (hcut : CutProjectionHypotheses W.projectedRows trueSupports)
    (hbridge :
      ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge W trueSupports)
    (hp : 0 < W.liftData.p)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree <
      (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    ExecutableCapSeparationHypotheses W trueSupports where
  cut := hcut
  bad_setup_of_projected_not_indicator :=
    ExecutableBadVectorWitness.bad_setup_of_projected_not_indicator
      W trueSupports hbridge
  hp := hp
  l2norm_upper_lt_divisor := hlt

end ExecutableCapSeparationHypotheses

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
Exact-cap contradiction form for projected vectors in `L' \ W`.
-/
theorem no_projected_not_indicator_at_factorFastPrecisionCap
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap : ExecutableCapSeparationHypotheses W trueSupports) :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ projectedRowSpanInt W.projectedRows →
        v ∉ trueFactorIndicatorLattice trueSupports →
          False :=
  no_projected_not_indicator_of_factorFastPrecisionCap_le
    W trueSupports (Nat.le_refl _) C hC_nonneg hC hcap

/--
Executable-cap BHKS separation: at any precision meeting
`factorFastPrecisionCap`, the projected row span equals the true-factor
indicator lattice, assuming the remaining failed-recovery-to-bad-vector step.
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

/--
Exact-cap BHKS separation: at the executable fast-path cap itself, the
projected row span equals the true-factor indicator lattice, assuming the
remaining failed-recovery-to-bad-vector step.
-/
theorem projectedRowSpan_eq_trueFactorIndicatorLattice_at_factorFastPrecisionCap
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcap : ExecutableCapSeparationHypotheses W trueSupports) :
    projectedRowSpanInt W.projectedRows =
      trueFactorIndicatorLattice trueSupports :=
  projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap
    W trueSupports (Nat.le_refl _) C hC_nonneg hC hcap

/--
Wrapper form of `projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap` that
accepts the packaged `ProjectedBadVectorSetupBridge` directly.
-/
theorem projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap_bridge
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    {a : Nat} (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (hcut : CutProjectionHypotheses W.projectedRows trueSupports)
    (hbridge :
      ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge W trueSupports)
    (hp : 0 < W.liftData.p)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree <
      (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    projectedRowSpanInt W.projectedRows =
      trueFactorIndicatorLattice trueSupports :=
  projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap
    W trueSupports ha C hC_nonneg hC
    (ExecutableCapSeparationHypotheses.ofProjectedBadVectorSetupBridge
      W trueSupports hcut hbridge hp hlt)

end BHKS

/--
Coefficient-power composite bound: combine the BHKS auxiliary polynomial's
`natDegree ≤ 2 * bhksDegree input − 1` bound with the real-l2-norm
monotonicity step `‖input‖₂ ≥ 1` to land `‖input‖₂ ^ aux.natDegree` inside
`bhksPaperCoeffNormFactorReal input = ‖input‖₂^(2 * bhksDegree input − 1)`.

This is the real-l2-norm form of the BHKS Theorem 5.2 coefficient-power
sub-bound: `‖input‖₂ ^ deg(aux) ≤ ‖input‖₂^(2n − 1)`. Composing the natDegree
bound from `BadVectorAuxiliary` with the monotonicity step from `BHKSBound`,
both already proved, discharges the inequality outright once the caller
supplies the `toPolynomial input ≠ 0` hypothesis.

A caller targeting the factored cap-separation chain still has to bridge from
the real `‖input‖₂` here to the integer `coeffL2NormBound input` used in the
chain's `h_coeff` hypothesis; that integer-vs-real conversion is the genuine
open piece tracked by the SPEC Group-D pathway and is not discharged here.
-/
theorem l2norm_pow_auxiliaryPolynomialWithCorrections_natDegree_le_bhksPaperCoeffNormFactorReal
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int)
    (hinput : HexPolyZMathlib.toPolynomial input ≠ 0) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial input)) ^
        (HexPolyZMathlib.toPolynomial
          (BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections)).natDegree ≤
      bhksPaperCoeffNormFactorReal input := by
  have hdeg :
      (HexPolyZMathlib.toPolynomial
          (BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections)).natDegree ≤
        2 * bhksDegree input - 1 := by
    have := BHKS.natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le_two_mul_sub_one
      input liftData vec corrections
    simpa [bhksDegree] using this
  exact l2norm_pow_le_bhksPaperCoeffNormFactorReal hinput hdeg

/--
Zero-correction specialisation of
`l2norm_pow_auxiliaryPolynomialWithCorrections_natDegree_le_bhksPaperCoeffNormFactorReal`
for the wrapper `BHKS.auxiliaryPolynomial`.
-/
theorem l2norm_pow_auxiliaryPolynomial_natDegree_le_bhksPaperCoeffNormFactorReal
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int)
    (hinput : HexPolyZMathlib.toPolynomial input ≠ 0) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial input)) ^
        (HexPolyZMathlib.toPolynomial
          (BHKS.auxiliaryPolynomial input liftData vec)).natDegree ≤
      bhksPaperCoeffNormFactorReal input := by
  unfold BHKS.auxiliaryPolynomial
  exact
    l2norm_pow_auxiliaryPolynomialWithCorrections_natDegree_le_bhksPaperCoeffNormFactorReal
      input liftData vec #[] hinput

end HexBerlekampZassenhausMathlib
