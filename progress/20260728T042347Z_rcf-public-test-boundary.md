# HexRCF public/test boundary

## Accomplished

- Audited the post-Phase-4 HexRCF frontier against the repository's Phase 5–7
  contracts instead of treating performance evidence as the end of the library.
- Removed all twelve regression-test imports from the public `HexRCF` umbrella.
- Added the twelve regression modules to the dedicated `HexReleaseTests` Lake
  target so they remain build-checked without being re-exported to consumers.
- Documented the public/test boundary and the previously omitted
  `ReifyTests.lean` module in the HexRCF SPEC.
- Built `HexRCF` and the complete `HexReleaseTests` target successfully.

## Current frontier

- The source and regression modules are now separated according to the Phase-3
  module contract.
- The full Phase 5–7 audit is still in progress; Phase-4 scientific evidence
  remains an independent gate rather than the finish line.

## Next step

- Finish the manual, API-quality, docstring, dead-declaration, and linter audit.
- Publish this focused boundary correction for independent review and merge.

## Blockers

- None for this milestone.
- Advancing the phase marker remains gated on HexRealRootsMathlib Phase 4 and
  release-quality HexRCF evidence.
