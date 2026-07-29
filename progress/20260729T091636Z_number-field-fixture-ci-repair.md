# Number-field fixture CI repair

## Accomplished

- Diagnosed PR #9080's replacement CI failure as the remaining generated
  `HexNumberField` fixture drift caused by the approximation-precision change;
  all library builds, manual builds, and bench checks passed.
- Regenerated `conformance-fixtures/HexNumberField/number_field.jsonl` from the
  PR head and confirmed a second emission is byte-for-byte identical.
- Verified the six changed records exactly match the fresh corpus reported by
  CI. The optional FLINT/PARI oracle dependencies are unavailable in this
  worktree, so the replacement CI run remains the external oracle check.

## Current frontier

- The approximation-radius milestone and both affected generated corpora now
  agree with the final mixed-strategy refinement behavior.

## Next step

- Push this fixture repair to PR #9080, monitor its replacement CI run, and
  merge when green while fixed-presentation exactification continues locally.

## Blockers

- None.
