# Issue #8417 second opinion

## Accomplished

Reviewed the current `LatticeTier.lean` reduction, the executable
`bhksSingleAllOnesPartition` / `latticeCoreFactorsWithBound` definitions, the
#8413 smart-search coverage capstone, and the available BHKS/indicator lemmas.
Confirmed the new file is a clean conditional case split over the lattice tier:
small-mod singleton is proved unconditionally, while the fast CLD split and
single-all-ones branches are isolated as explicit BHKS obligations.

## Current frontier

The remaining arm-3 gap is the concrete lattice adequacy theorem connecting
`bhksLatticeBasis` / projected LLL rows / equivalence-class indicators to the
proof-side subset representation machinery (`RepresentsIntegerFactorAtLift` and
`LiftedFactorSubsetPartition`). Existing classical coverage results consume
subset/partition evidence; they do not prove that the LLL-derived classes are
that evidence.

## Next step

If continuing on #8417, the most useful sharpening is a small, reusable
non-lattice lemma: a no-proper-nonempty-representing-subset condition for the
top lifted partition implies irreducibility of `core`. That should become the
target mathematical invariant for the eventual Bool-to-no-subset lattice proof.

## Blockers

No blocker for the reduction skeleton. Fully closing arm 3 unconditionally
still requires new CLD/BHKS lattice adequacy over the executable lattice code;
doing so by assumption would violate the no-axiom project doctrine.
