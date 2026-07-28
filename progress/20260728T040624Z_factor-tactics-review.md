# Factor tactics and factorization manual review

## Accomplished

- Expanded the Factor Tactics chapter with tactic-form examples, mathematical
  motivation for the integer-factorization tiers, Isabelle/HOL references,
  and a cautious account of the van Hoeij implementation's formal status.
- Simplified the normalized-factorization API names and aligned the executable
  and Mathlib tactic forms around the same generated bindings.
- Added `OfNat` support for `ZMod64` and the `#p[...]` dense-polynomial literal,
  then used the resulting notation where it improves the chapter examples.
- Replaced internal/specification jargon in public documentation, added Verso
  name-link requirements to the writing specification, and clarified that the
  current primality replay is linear only because it scans all divisors below
  the modulus.
- Distinguished the 1982 LLL polynomial-factorization algorithm from van
  Hoeij recombination, recorded its polynomial-time significance and Isabelle
  formalization, and made explicit that Hex uses LLL reduction but does not
  implement the older factorizer.
- Separated optional-tier partial correctness from non-decline in the manual,
  documenting the proved irreducibility results, the still-guarded product
  obligations, and the good-prime hypothesis of the planned lattice-totality
  theorem.
- Opened follow-up issues #9022, #9023, #9029, and #9030 for the library-wide
  documentation, naming, primality-check, and manual-notation reviews.
- Verified the complete repository with `lake build` (9502 jobs).

## Current frontier

The requested implementation and documentation changes are complete and the
full build is green. They are being published together from
`agent/factor-tactics-manual`.

## Next step

Merge the review PR, then execute the four focused follow-up issues while the
manual review continues.

## Blockers

None.
