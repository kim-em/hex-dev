# HexResultantMathlib Phases 4-5 and bump to 5

## Accomplished

- Added the External comparators absence declaration to the SPEC
  (correspondence-only-layer; computational performance owner
  hex-resultant), completing the Phase-4 declaration surface. The
  headline-correctness-theorem designation (toPolynomial_resultant)
  landed with #9378. check_phase4 exempts the library (mathlib, no
  phase4 block, no report; HexLLLMathlib precedent) and Phase-4 dep
  coupling is satisfied (HexResultant 5, HexPolyMathlib 7).
- Phase 5 holds on the merits: the library is sorry-free and its full
  correspondence surface is proved (see the 2026-08-21 wave audit and
  status/hex-resultant-mathlib.scaffolding-reviewed).
- Bumped done_through 3 -> 5 per the wave bump queue
  (progress/20260822T034500Z_wave-dag-and-headline-audit.md).

## Current frontier

- The resultant pair now sits at 5/5. Remaining rungs are the Phase-6
  hygiene passes (docstrings, dead-code decision on the fraction
  detour, import trims) and Phase 7 (README, chapter heading rename).

## Next step

- B6: HexBerlekampZassenhaus headline report and bump.

## Blockers

- None.
