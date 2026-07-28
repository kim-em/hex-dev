# HexNumberField disambiguation review fixes

## Accomplished

- Tightened the radius threshold from `2 * D * r < 1` to the sufficient
  `3 * D * r < 1`, accounting for the infinity-norm centre used by the shipped
  zero-exclusion test.
- Corrected the internally inconsistent SPEC threshold while retaining its
  finite search endpoint, whose extra two bits still cover the stronger test.
- Strengthened the Horner error recurrence for circumscribed root balls, whose
  radius can be up to two nominal input-error units.
- Generalized the recurrence over a coefficient magnitude callback so the
  number-field tower can reuse it without copying the proof-sensitive logic.
- Added compiled recurrence and nonzero-refutation checks and rebuilt the
  disambiguation and umbrella targets successfully.

## Current frontier

The independent review's two numeric completeness failures are addressed. The
fixed-field roots caller additionally requests one extra candidate-square bit,
so it lies inside the generalized two-unit contract with margin.

## Next step

Push the repaired disambiguation branch, rebase all descendants, and rerun the
fixed-field root regressions before returning to the common-field API.

## Blockers

None.
