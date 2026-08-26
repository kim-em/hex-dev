# HexRCF FLINT steady-state floor

## Accomplished

- Added `runFlintDecisionOverhead`, an atom-free `∀ x, True` request through
  the exact warmed `rcf/decide` path used by the five python-flint rungs.
- Precompressed and guarded the complete request line, shared reply decoding
  with the substantive rungs, and configured eleven outer repeats for a stable
  floor median.
- Documented the conservative adjustment contract: retain every raw ratio,
  subtract the floor only when positive, and mark floor-dominated rungs instead
  of manufacturing adjusted values.
- Built the bench, passed the focused tests and thirty-sentence oracle check,
  and verified all twenty-one registrations with python-flint 0.9.0.

## Current frontier

- The comparator now contains all wiring needed to collect raw and
  overhead-adjusted ratios on the named release host.
- The local diagnostic proof sweep exercised the null and all fifteen
  substantive pairs end to end, but was explicitly non-release-quality.

## Next step

- Run repository checks from the committed state, update draft PR #9027, and
  obtain an independent Claude review of the artifact milestone.
- Land the remaining parent stack while its CI completes.

## Blockers

- Release-quality ratios, complexity verdicts, profiles, and proof samples
  require the clean named benchmark host.
- The final phase marker remains gated on HexRealRootsMathlib Phase 4 (#8972).
