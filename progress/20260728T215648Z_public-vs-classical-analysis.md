# Public versus classical factorization analysis

## Accomplished

- Traced the two plotted Hex entries through the warm service and production
  dispatcher.
- Established that `hex-classical-nodecline` is a one-shot exhaustive benchmark
  diagnostic, not the same classical implementation used inside public
  `ZPoly.factorize`.
- Recomputed paired public/classical ratios from the committed sweep without
  rerunning any timings, including the protocol-overhead signal filter and
  family-level reversals.

## Current frontier

- The public path combines recursive per-remainder relifting with a final
  reconstruction guard; the diagnostic classical path performs one lift and
  one full recombination without that guard. This explains the broad slowdown
  on easy one-pass families and the public path's large wins on Wilkinson and
  cyclotomic-product cases.

## Next step

- If exact attribution is needed, add untimed tier/path metadata to the sweep
  and separately benchmark production classical, reconstruction checking, and
  the no-decline diagnostic on the already selected corpus rows.

## Blockers

- Current sweep JSON does not record the public dispatch tier, so it cannot
  separate recursive-classical cost, reconstruction cost, and any fallback
  burn per row after the fact.
