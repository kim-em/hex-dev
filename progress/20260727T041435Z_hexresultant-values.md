# HexResultant resultant and discriminant

## Accomplished

- Implemented executable `resultant` extraction from Brown's corrected
  terminal scale, including zero/constant conventions and the reversed-input
  degree-product sign.
- Implemented the standard positive-degree discriminant formula and a proved
  kernel/runtime split that compiles through `derivativeImpl`.
- Added compiled regressions for linear, quadratic, common-root, zero,
  constant, swapped, defective-drop, repeated-root, and bivariate resultant
  cases.
- Audited the Phase 1 API, advanced `HexResultant.done_through` to 1, and ran
  the targeted build, status, DAG, copyright, line-count, forbidden-form, and
  whitespace checks successfully.
- Confirmed the preceding exact-PRS stack passes the complete 9,460-job
  monorepo build.

## Current frontier

HexResultant's specified computational API is complete. Five propositional
Phase 1 obligations remain explicit; there are no data-level sorries. The
contract and exact-PRS Claude reviews remain active in background monitors.

## Next step

Publish this stacked milestone for review, then begin the
HexResultantMathlib correspondence layer without waiting for those independent
reviews to finish.

## Blockers

None. Nested dense-polynomial coefficients intentionally lack `NatCast`, so
the recursive exact-division regression is exercised by bivariate resultant;
the SPEC does not require a bivariate discriminant.
