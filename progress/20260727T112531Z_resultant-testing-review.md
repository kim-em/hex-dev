# Resultant testing review repair

## Accomplished

- Added explicit core pins for the odd degree-product swap sign,
  self-resultant and unit-resultant cases, and the characteristic-five formal
  derivative-degree correction.
- Extended the external profile with common-factor and repeated-root cases, so
  both zero-resultant and zero-discriminant return paths receive FLINT/PARI
  checking.
- Changed the dual oracle to evaluate and report both implementations even
  when the first disagrees, while keeping attempted-result counts accurate.
- Reworked the benchmark input family to share the committed LCG, added direct
  `pseudoDivMod` and `subresultantChain` registrations, forced complete chain
  outputs, and incorporated arbitrary-precision growth into the declared
  wallclock models. All four measured ladders now return `consistent`.
- Fixed the Mathlib-free bench linter to traverse modern `module`,
  `public import`, and `public meta import` headers; verified that it now sees
  the four transitive `HexResultant` imports.
- Rebuilt the conformance umbrella, emitter, and bench; reproduced the fixture
  exactly; verified all registrations; and passed the repository structural,
  syntax, forbidden-token, and benchmark-import checks. The local one-target
  verify used one second; CI applies its repo-wide 360-second cap.

## Current frontier

The actionable correctness and measurement findings from the independent
Resultant testing review are repaired. Phase bookkeeping remains intentionally
unchanged: this is a draft milestone in a larger stack, and `done_through` must
not advance past the still-sorried proof phase merely because later artifacts
already exist on draft branches.

## Next step

Push the repaired ResultantTesting branch, restack its descendants, then repair
the completed NumberField testing review before resuming new milestone work.

## Blockers

The local environment lacks `python-flint` and `cypari2`, so the live external
oracle still skips locally and will run in CI.
