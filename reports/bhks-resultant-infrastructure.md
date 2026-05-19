# BHKS Resultant Infrastructure

## Availability

`Polynomial.resultant` is available in the current Mathlib checkout via:

```lean
import Mathlib.RingTheory.Polynomial.Resultant.Basic
```

The upstream file exposes the required core API:

- `Polynomial.sylvester`
- `Polynomial.resultant`
- `Polynomial.resultant_map_map`
- `Polynomial.resultant_ne_zero`
- `Polynomial.resultant_eq_zero_iff`
- `Polynomial.isUnit_resultant_iff_isCoprime`
- `Polynomial.exists_mul_add_mul_eq_C_resultant`

The repo already has a Hex-local bridge in
`HexBerlekampZassenhausMathlib/Resultant.lean`, imported by the umbrella
`HexBerlekampZassenhausMathlib.lean`. The bridge packages the upstream API in
the integer-polynomial shape needed by BHKS D1:

- `abs_resultant_le_sylvester_row_l2norm_prod`
- `abs_resultant_le_l2norm_pow`
- `int_resultant_ne_zero_of_coprime`
- `resultant_map_intCast_rat`
- `int_resultant_eq_zero_iff_not_coprime_over_rat`
- `int_resultant_ne_zero_of_coprime_over_rat`

`HexBerlekampZassenhausMathlib/BadVector.lean` also already packages the
resultant lower/upper-bound comparison around executable BHKS bad-vector data:

- `BadVectorResultantData`
- `BadVectorResultantData.badVector_resultant_bounds`
- `BadVectorResultantData.no_badVector_of_l2norm_upper_lt_divisor_params`
- `ExecutableBadVectorWitness.badVector_resultant_bounds`
- `ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge`
- `ExecutableBadVectorWitness.badVector_resultant_bounds_of_bhks_bad`
- `ExecutableBadVectorWitness.no_bhks_bad_setup_of_l2norm_upper_lt_divisor`

## Missing Surface For #2567

No resultant port is required. The missing work for BHKS Theorem 5.2 is now
above the resultant layer:

- Prove the BHKS Lemma 3.2 algebraic clauses that instantiate
  `ProjectedBadVectorSetupBridge`: the canonical auxiliary polynomial for a
  projected bad vector, rational coprimality of the input/auxiliary pair, and
  divisibility of the integer resultant by `p^(k * d)`.
- Connect the l2norm upper bound from
  `ExecutableBadVectorWitness.no_bhks_bad_setup_of_l2norm_upper_lt_divisor`
  to the executable precision cap and bad-vector separation statement.
- Chain that separation result with the existing `L' = W` recovery path to
  prove the `factorFast` termination leaf.
- Use the separate arithmetic packaging around `bhksBound` to show the
  executable cap dominates the BHKS threshold and the Mignotte reconstruction
  precision.

## Recommended Split

Because the resultant bridge is already present, the next issues should not be
Mathlib resultant ports. A useful split is:

1. Instantiate `ProjectedBadVectorSetupBridge` from the executable CLD/Hensel
   data for a projected vector in `L' \\ W`.
2. Prove the cap-separation theorem that feeds
   `no_bhks_bad_setup_of_l2norm_upper_lt_divisor`.
3. Combine cap separation, `bhksBound` arithmetic dominance, and the existing
   recovery certificate path into the final `factorFast_terminates` theorem.
