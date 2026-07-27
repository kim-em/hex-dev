# Pseudo-division index kernel

## Accomplished

- Added and proved the private dependent push-builder laws needed to reason
  about pseudo-division's prefix-dependent array folds: size, creation-time
  reads, extension stability, push reads, and fallback independence.
- Proved the exact contents of the leading-coefficient power table.
- Proved coefficient formulas for the raw pseudo-quotient and
  pseudo-remainder builders.
- Incorporated the completed independent review of the preceding Resultant
  proof kernel. The review found no merge blockers and confirmed the power,
  remainder-size, and NumberField irreducibility arguments.
- Addressed its concrete Resultant feedback by documenting the structural
  nature of the remainder bound, removing its unnecessary degree-ordering
  hypothesis, adding the companion quotient-size bound, shortening the private
  power lemma name, and making the reconstruction theorem directly rewritable.
- Built `HexResultant`, `HexConformance`, and `HexManual`; verified all four
  Resultant benchmarks; and passed Phase 4, DAG, copyright, line-count, and
  diff checks.

## Current frontier

- `pseudoDivMod_reconstruct_core` still needs the coefficient-level algebraic
  assembly. Its remaining proof layer is a bounded convolution formula, the
  active-array recurrence, and the high-coefficient reindexing/factorization.
- The private proof builders deliberately do not replace the public executable
  folds: Lean prevents a public executable definition from depending on a
  private helper, and the runtime definition remains unchanged.

## Next step

- Publish this index-kernel milestone as a stacked draft PR.
- Begin the bounded convolution and active-recurrence lemmas immediately while
  CI and the next independent review run.
- Continue reconciling the bottom of the existing PR stack as its long-running
  CI completes.

## Blockers

- No implementation blocker for the next coefficient proof layer.
