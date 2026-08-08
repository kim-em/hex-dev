# Chebyshev/Legendre M1 final evidence

## Accomplished

- Recorded a clean, CPU-0, 392-row Hex-only factor sweep at review-hardened
  revision `d580b121292be127be33b312fe888b00573379ed`.
- Confirmed 373 solves, 19 timeouts, and identical statuses and factor-degree
  multisets against both the pre-M1 and first-M1 records.
- Refreshed the cross-system, library, Isabelle, and six-issue reports plus all
  25 current figures while retaining the already-current external-system data.
- Corrected the earlier cyclotomic drift interpretation: lazy M1 coordinate
  transport restores the eight affected monic controls to within 1.009–1.041×
  of their pre-M1 measurements.

## Current frontier

The implementation, conformance evidence, and final benchmark artifact are
complete locally. The PR needs the final evidence commit, a fresh independent
review of the hardened diff, and green post-push CI.

## Next step

Commit and push the refreshed evidence, obtain the final second opinion,
address any remaining soundness or merge-blocking finding, then merge PR
#9112 and verify that issues #9104–#9109 close.

## Blockers

None.
