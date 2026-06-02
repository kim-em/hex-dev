# BHKS D1 Frontier

This report maps the current path to the Group D leaf theorem

```lean
theorem factorFast_terminates (f : Hex.ZPoly) :
    Hex.factorFast f ≠ none
```

from `SPEC/Libraries/hex-berlekamp-zassenhaus.md`.

The theorem is still a leaf obligation: the public `factor` correctness path
uses the slow fallback and does not depend on this theorem.

## Landed Substrate

### Resultant and Hadamard Layer

Covered in `HexBerlekampZassenhausMathlib/Resultant.lean`:

- `abs_det_le_row_l2norm_prod`
- `abs_det_le_col_l2norm_prod`
- `abs_resultant_le_l2norm_pow`
- `int_resultant_ne_zero_of_coprime`
- `resultant_map_intCast_rat`
- `int_resultant_eq_zero_iff_not_coprime_over_rat`
- `int_resultant_ne_zero_of_coprime_over_rat`

This closes the Mathlib resultant/Hadamard wrapper part of D1. The local bridge
imports `Mathlib.RingTheory.Polynomial.Resultant.Basic`; no separate uncovered
resultant-port issue remains in the current tree.

### Bad-Vector Resultant Package

Covered in `HexBerlekampZassenhausMathlib/BadVector.lean`:

- `BadVectorResultantData`
- `BadVectorResultantData.divisor_real_le_l2norm_pow`
- `BadVectorResultantData.no_badVector_of_l2norm_upper_lt_divisor`
- `ExecutableBadVectorWitness`
- `BHKS.auxiliaryPolynomial`
- `ExecutableBadVectorWitness.IsBhksBadVectorSetup`
- `ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge`
- `ExecutableBadVectorWitness.bad_setup_of_projected_not_indicator`
- `ExecutableBadVectorWitness.bhks_bad_vector_resultant_lower_bound`
- `ExecutableBadVectorWitness.no_bhks_bad_setup_of_l2norm_upper_lt_divisor`

This packages the resultant lower/upper comparison and exposes the intended
boundary for BHKS Lemma 3.2: constructing
`ProjectedBadVectorSetupBridge` from executable lift and true-factor data is
not yet proved, but it has an explicit target API.

### Auxiliary Polynomial Coefficient Shape

Covered in `HexBerlekampZassenhausMathlib/BadVectorAuxiliary.lean`:

- `BHKS.list_range_getElem?_map_getD_zero`
- `BHKS.coeff_auxiliaryPolynomial`

This gives the coefficient readback surface needed by the future
Cauchy-Schwarz/l2-norm proof for `BHKS.auxiliaryPolynomial`.

### BHKS Cap Arithmetic

Covered in `HexBerlekampZassenhausMathlib/BHKSBound.lean`:

- `bhksThresholdNatBound`
- `bhksBound_eq_thresholdNatBound`
- `bhksBound_dominates_spec_components`
- `bhksPaperThresholdReal`
- `bhksPaperCoeffNormFactorReal_le_coeffNormFactor`
- `bhksPaperLogFactorReal_le_log2Factor`
- `bhksPaperThresholdReal_le_thresholdNatBound`
- `bhksPaperThresholdReal_le_bhksBound`
- `factorFastPrecisionCap_eq_max_bhksBound_defaultFactorCoeffBound`
- `bhksBound_le_factorFastPrecisionCap`
- `defaultFactorCoeffBound_le_factorFastPrecisionCap`
- `factorFastPrecisionCap_real_dominates_bhksPaperThreshold`

This covers the current executable-cap side of D1: `factorFastPrecisionCap`
dominates both the BHKS paper threshold wrapper and the Mignotte reconstruction
bound.

### Cap Separation and Recovery Interfaces

Covered in `HexBerlekampZassenhausMathlib/TerminationBound.lean`:

- `mignotte_precision_at_precisionForCoeffBound_factorFastPrecisionCap`
- `mignotte_precision_of_liftData_precisionForCoeffBound_factorFastPrecisionCap`
- `bhksPaperThresholdReal_le_factorFastPrecisionCap`
- `ExecutableBadVectorWitness.no_bhks_bad_setup_of_factorFastPrecisionCap_le`
- `BHKS.ExecutableCapSeparationHypotheses`
- `BHKS.ExecutableCapSeparationHypotheses.ofProjectedBadVectorSetupBridge`
- `BHKS.no_projected_not_indicator_of_factorFastPrecisionCap_le`
- `BHKS.projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap`
- `BHKS.projectedRowSpan_eq_trueFactorIndicatorLattice_of_cap_bridge`

Covered in `HexBerlekampZassenhausMathlib/Recovery.lean`:

- `projectedRowsOfLiftData`
- `badVectorWitnessOfLiftData`
- `projectedRowsOfLiftData_eq_trueFactorIndicatorLattice_of_cap`
- `ForwardRecoveryInputs`
- `bhksRecover_eq_some_of_recovery`
- `bhksRecover_isSome_of_recovery`

Covered in `HexBerlekampZassenhaus/Basic.lean`:

- `factorFastPrecisionCap`
- `factorFast_ne_none_of_core_recovery_on_schedule`

The recovery path is therefore structurally present: once cap separation gives
`L' = W`, `ForwardRecoveryInputs` can feed `bhksRecover?`, and the executable
scheduled-recovery theorem can feed `factorFast`.

## Remaining Gaps

### Gap 1: Exact CLD Quotient Coefficient Bound

Status: covered by open issue `#5223`.

Target surface:

- likely `BHKS.abs_phi_coeff_le` in a new or adjacent
  `HexBerlekampZassenhausMathlib` file.

Purpose:

- Prove the exact-polynomial BHKS Lemma 5.1 bound for
  `Phi(g) = f * g.derivative / g`, using Mahler/Landau infrastructure and the
  derivative Mahler bound transported through `HexPolyZMathlib`.

Dependencies:

- `#5266` for the integer-polynomial derivative Mahler estimate.

### Gap 2: Executable CLD Column Bound

Status: replanned by #6217 into #6220 after a counterexample showed the
original #5224 statement false for the current executable cut semantics.

Target surface:

- `BHKS.abs_cldCoeffs_le_bhksCoeffBound`

Purpose:

- First correct the executable cut path so `Hex.cldCoeffs input p k g`
  centers the ambient `p^k` representative before applying the lower
  `Psi` cut, then connect the executable column to the exact quotient
  coefficient bound from `#5223`, under true-factor and precision hypotheses.

Relevant executable definitions:

- `Hex.bhksCoeffBound` in `HexBerlekampZassenhaus/Basic.lean`
- `Hex.centeredResiduePow` in `HexBerlekampZassenhaus/Basic.lean`
- `Hex.psiCut` in `HexBerlekampZassenhaus/Basic.lean`
- `Hex.cldQuotientMod` in `HexBerlekampZassenhaus/Basic.lean`
- `Hex.cldCoeffs` in `HexBerlekampZassenhaus/Basic.lean`

### Gap 3: Projected Bad-Vector Setup Bridge

Status: covered by open issue `#5512`.

Target surface:

- construction of
  `ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge W trueSupports`

Purpose:

- Prove the structural and algebraic BHKS Lemma 3.2 fields for projected
  vectors in `L' \ W`:
  `auxiliary_eq`, `localFactorDegree_pos`, `coprime_input_aux_over_rat`, and
  `resultant_divisible_by_p_pow`.

Existing consumer:

- `BHKS.ExecutableCapSeparationHypotheses.ofProjectedBadVectorSetupBridge` in
  `HexBerlekampZassenhausMathlib/TerminationBound.lean`.

Dependency:

- `#6220`, because the bridge must use the corrected executable CLD coefficient
  and precision surface rather than inventing a parallel true-factor predicate.
- `#6221`, because the projected bad-vector polynomial must account for the
  diagonal lattice-row correction coordinates.

### Gap 4: Auxiliary-Polynomial l2-Norm Bound

Status: covered by open issue `#5204`.

Target surfaces:

- `BHKS.cldColumnNormBound`
- `BHKS.auxiliaryPolynomial_coeff_sq_le`
- `BHKS.auxiliaryPolynomial_l2norm_sq_le`

Purpose:

- Combine `BHKS.coeff_auxiliaryPolynomial` with
  `BHKS.abs_cldCoeffs_le_bhksCoeffBound` to obtain the Cauchy-Schwarz bound on
  `HexPolyZMathlib.l2norm (toPolynomial (BHKS.auxiliaryPolynomial ...))`.

Dependencies:

- `#6220`
- `#6221`

### Gap 5: Bad-Vector Norm Versus Cut Radius

Status: covered by open issue `#5216`.

Target surface:

- `bhks_bad_vector_norm_sq_gt_cutRadiusSq4_of_paperThreshold_le` or the
  closest local name in `HexBerlekampZassenhausMathlib/TerminationBound.lean`.

Purpose:

- Compose `ExecutableBadVectorWitness.bhks_bad_vector_resultant_lower_bound`,
  the `#5204` auxiliary-polynomial norm bound, and `BHKSBound.lean` threshold
  lemmas to prove that any bad vector exceeds the projected cut radius at the
  paper threshold.

Dependencies:

- `#5204`
- `#5224`

### Gap 6: Final Cap-Level Recovery and `factorFast_terminates`

Status: covered by open issue `#5237`.

Target surfaces:

- a cap-level recovery theorem at
  `precisionForCoeffBound (factorFastPrecisionCap f) p`
- `factorFast_terminates`

Purpose:

- Use `#5216` separation to prove the executable recovery call is `some`, then
  compose with
  `Hex.factorFast_ne_none_of_core_recovery_on_schedule`.

Dependencies:

- `#5216`
- `#5204`
- `#5224`
- `#5223`

## Frontier Summary

No uncovered D1 gaps remain at the deliverable level. The current open issues
cover the remaining path:

```text
#5223 -> #5224 -> #5204 -> #5216 -> #5237
                 \-> #5512 -/
```

The only nuance is dependency ordering. `#5512` constructs the
`ProjectedBadVectorSetupBridge` consumed by the cap-separation API and depends
on `#5224`; `#5216` constructs the norm/cut-radius separation and depends on
`#5204` and `#5224`; `#5237` is the final assembly after both the separation
and recovery prerequisites are available.

No new follow-up issue is recommended from this review. Future planning should
avoid duplicating the deliverables above and should instead keep the existing
dependency chain current as the theorem names from `#5223` and `#5224` land.
