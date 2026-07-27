# RCF literal-Sturm foundation milestone

## Accomplished

- Added abstract positive-scaled `Sturm.Replay` recurrences and proved they
  give consecutive coprimality, all generalized Sturm-chain axioms, and
  squarefreeness.
- Added integer `ZReplay` witnesses, exact integer-to-real replay transport,
  and composed finite-interval and whole-line root-count theorems over the
  literal replay array.
- Added generic literal isolation structures and proved count-one uniqueness
  plus ordered complete coverage of every real root.
- Added positive and malformed proof regressions for an abstract recurrence,
  plus the four-entry integer chain of `x³ - x`; the latter composes replay,
  squarefreeness, literal counts, and three nontrivially ordered isolations end
  to end.
- Promoted and deduplicated the small recurrence, cast, variation, and dyadic
  order lemmas needed by literal consumers, and updated the companion SPEC.
- Incorporated two independent Claude Opus reviews. The first confirmed the
  mathematics but found four integration/documentation blockers; the second
  verified all four were closed and returned a merge-ready verdict.
- Passed `lake build HexRealRootsMathlib HexRCF` (8,784 jobs) and the
  copyright, line-count, DAG, phase-4, Mathlib-free bench, conformance-target,
  diff, and forbidden-proof-token checks.

## Current frontier

Issue #8891 is ready to publish. The shared Mathlib theorem layer now accepts
literal generalized Sturm recurrences without identifying them with
`Hex.ZPoly.sturmChain`, which removes the main trust-boundary dependency for
the RCF checker.

## Next step

Implement the executable RCF replay certificate and Boolean checker. Instrument
the existing `spemAux` loop to emit exact positive left/right scales and
quotients, starting from the literal polynomial head rather than its primitive
part, then prove successful checking produces `ZReplay` and the two composed
count theorems.

## Blockers

None.
