# Progress — BHKS coarse-window review

## Accomplished

Reviewed the latest fast-path coarseness probe note, the executable BHKS
recovery path in `HexBerlekampZassenhaus/Basic.lean`, the Mathlib lattice and
signature-class surfaces, and the SPEC's BHKS Group B obligations.

Conclusion for this session: exact division plus product equality certifies
that emitted equivalence-class blocks are integer-factor supports, hence unions
of true supports. It does not by itself certify that the blocks are the true
supports. The load-bearing invariant that prevents coarse output is `W ⊆ L'`
at the successful precision; once true-factor indicators are in `L'`, the RREF
signature relation cannot merge two different true supports.

Also attempted the configured Claude second-opinion wrapper. It failed with a
transport-level `ConnectionRefused`, so no substantive external opinion was
used.

## Current frontier

The proof frontier is not a generic comparison between the recovery precision
of a merged product and the BHKS cap. It is the per-success-state bridge from
the executable stop condition to `W ⊆ L'`, or else an executable guard that
rejects coarse unions.

## Next step

Either prove that every executable success state satisfies the hypotheses of
the BHKS cut/projection containment theorem (`W ⊆ L'`), or add a guard that
certifies each emitted class is not a proper union of accepted divisor supports.

## Blockers

The second-opinion wrapper was unavailable due to API connection failure.
