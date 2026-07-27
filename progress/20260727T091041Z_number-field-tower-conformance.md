# Number-field tower conformance

## Accomplished

- Added core conformance guards for rational and relative adjoining,
  factorization, splitting, and flattening, including fixed-embedding and
  non-rational-base cases.
- Added a deterministic JSONL emitter with committed fixtures for rational and
  tower factorization, splitting-field summaries, and primitive presentations.
- Added a cypari2/PARI oracle which independently uses `nffactor`,
  `nfsplitting`, `polcompositum`, `nfinit`, and resultants. It checks all nine
  emitted cases locally with no failures.
- Registered the conformance module, emitter, CI oracle tuple, and local oracle
  dependency profile.
- Ran the full repository build, reproduced the committed fixture byte for
  byte, ran the PARI oracle, checked both shell scripts, and checked the diff.

## Current frontier

- The conformance milestone is ready to publish as the next draft PR above the
  flattening milestone.
- The independent flattening review found no soundness or dependent-typing
  defect, but did find that one failed `shift?` certification currently aborts
  the bounded primitive search instead of advancing to the next signed shift.

## Next step

- Publish this conformance milestone and launch its independent review, then
  fix the flattening search control flow and rebase the dependent draft stack.
- Reconcile the remaining review findings about performance and SPEC wording
  before extending the Mathlib companion and manual.

## Blockers

- None.
