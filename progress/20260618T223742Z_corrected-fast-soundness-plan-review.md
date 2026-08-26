# Progress - corrected fast-soundness plan review

## Accomplished

Reviewed the corrected separation-free fast-soundness plan against `origin/main`
rather than the stale local checkout. Checked the forward-cut wrappers in
`PartitionRefinement.lean`, the true-factor and recovered-lift CLD surfaces in
`Lattice.lean`, the executable success/candidate-size extractors in
`HexBerlekampZassenhaus/Basic.lean`, and the recovery package fields in
`Recovery.lean`.

Verdict: the forward-count/cardinality route itself is separation-free. The
remaining obligations are producer/precision-alignment obligations, not a
forced `L' = W` step, provided the true-factor cut certificate is built at the
same successful precision extracted from the executable fast-core loop and uses
the recovered/period-corrected CLD route where needed.

## Current frontier

The main proof risks are:
- strengthening the executable success extractor to retain the accepted
  precision/floor fact needed for the CLD separation hypotheses;
- producing per-true-support centered `RecoveredLift` data from Hensel
  correspondence and Mignotte bounds at that same precision;
- avoiding accidental fallback to the older `TrueFactorLift` raw-product or
  canonical-indicator equality APIs, which do require stronger recovery data.

## Next step

Implement or verify the A1 producer for `liftedTrueSupports core d` at the
actual accepted lift precision, including the centered-recovery theorem for each
true support and the partition-count bridge to `normalizedFactors.card`.

## Blockers

No tooling blocker. The remaining blockers are proof-producing lemmas, especially
the accepted-precision extractor and the per-true-support centered recovery
constructor.
