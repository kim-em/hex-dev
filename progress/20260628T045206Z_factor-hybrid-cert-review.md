# Factor hybrid certificate review

## Accomplished
- Reviewed the proposed self-certifying `factorHybridTraced` design against the current `HexBerlekampZassenhaus/Basic.lean` definitions.
- Checked the existing `factorWithBound`, `factor`, `factor_product`, `factor_entry_*`, `factorizationOfFactors`, `factorSlowTrial_product`, and downstream Mathlib wrapper theorem shapes.
- Attempted to run the configured Claude second-opinion helper; it failed with an API connection error, so no external second opinion was incorporated.

## Current frontier
- The runtime product check appears suitable for preserving the public `factor_product` theorem, provided the check is in the actual public computation path.
- The main proof ripples are replacing default-factor transports through `factor_eq_factorWithBound_default` and deciding whether existing raw-source/irreducibility theorems remain old-path-specific or gain hybrid-specific variants.

## Next step
- If implementing the swap, add a hybrid branch-shape lemma for structural entry invariants and prove a `factorHybrid_product` theorem by splitting on the product equality guards and using `factorSlowTrial_product` in fallback arms.

## Blockers
- None for the design review. The Claude helper was unavailable due to API connection failure.
