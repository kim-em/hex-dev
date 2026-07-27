# Pseudo-division bounded convolution

## Accomplished

- Proved a Mathlib-free diagonal normal form for the executable dense
  polynomial multiplication coefficient fold.
- Proved that diagonal folds may be extended past the left support and
  truncated past the requested product degree.
- Bridged the List-based multiplication fold to the Array-based bounded fold
  used by pseudo-division.
- Proved `coeff_mul_bounded` with only the left-factor size bound; no support
  assumption on the right factor is needed.
- Independently cross-checked the bound and proof shape in a read-only Sol
  audit.
- Built `HexResultant` and `HexConformance`, verified all four Resultant
  benchmarks, and passed line-count, DAG, and diff checks.

## Current frontier

- The low-coefficient half of `pseudoDivMod_reconstruct_core` can now combine
  `pseudoRemainder_coeff` with `coeff_mul_bounded` directly.
- The remaining difficult layer is the active-array recurrence and the
  high-coefficient reversal/factorization that connects it to the quotient
  convolution.

## Next step

- Publish this bounded-convolution milestone as a stacked draft PR.
- Start the active-array recurrence proof immediately while CI and the
  independent review of the preceding index-kernel PR continue.

## Blockers

- No implementation blocker for the active-array recurrence.
