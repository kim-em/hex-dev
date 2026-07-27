# Resultant and number-field orientation

## Accomplished

- Read the current repository roadmap, library DAG, conventions, and latest
  progress handoff.
- Read `SPEC/Libraries/hex-resultant.md` and
  `SPEC/Libraries/hex-number-field.md` in full.
- Read the two Mathlib companion SPECs and
  `SPEC/hex-number-field-expansion-plan.md` to understand the proof staging and
  downstream contracts.
- Confirmed that `HexResultant`, `HexResultantMathlib`, `HexNumberField`, and
  `HexNumberFieldMathlib` are all planned at `done_through: 0`, with no source
  trees or Lake entries yet.

## Current frontier

The resultant and number-field designs are SPEC-ready but deliberately not
activated. `hex-resultant` is the first new computational dependency;
`hex-number-field` then consumes its executable eliminants together with the
existing root-isolation, factorization, matrix, and row-reduction libraries.
The resultant Mathlib bridge is explicitly staged: common-root/vanishing facts
support early lazy arithmetic, while full value correspondence is required for
root completeness and later tower work.

## Next step

Await a concrete directive about activation, planning, or implementation. If
activated, begin with Phase 1 for `HexResultant` before dispatching dependent
number-field work.

## Blockers

None for orientation. Implementation remains gated only by the libraries'
intentional `planned` status.
