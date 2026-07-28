# HexRCF fresh-module proof probes

## Accomplished

- Added the three fixed quadratic, degree-10, and adversarial degree-50 source
  and reflected cases with definitionally checked reification, accepted
  compiled search, and stable structural sentence/certificate hashes.
- Generated and committed independently rebuilding literal certificate macros;
  the combined source is 59,301 bytes and its current olean is 1,128,896 bytes.
  The generator accepts only the six expected dyadic-order proof omissions and
  rewrites each as `by decide`.
- Added the shared baseline and all eighteen case variants for the five exact
  `Reify - Baseline`, `Search - Input`, `Literal - Input`, `Replay - Literal`,
  and `Tactic - Baseline` pairs, with identical imports and no measured-module
  import path.
- Added a public bench-local replay elaborator using the same kernel-checked
  `mkDecideProof`/`check_sound` tail as the production tactic. This keeps the
  adversarial replay viable without private APIs, resource-limit workarounds,
  sorries, axioms, or `native_decide`.
- Extracted the compiled benchmark's structural hashes into a shared
  Mathlib-free helper and rebuilt `hexrcf_bench` against it.
- Added the neutral-runner adapter, fifteen-pair manifest tests, per-module
  axiom policies, reduced CI target, scientific build-only target, and SPEC
  documentation.
- Built both proof-probe targets and all three replay/tactic theorem variants.
  A one-sample dirty/busy diagnostic exercised all fifteen harness pairs and
  observed axiom output only from Replay and Tactic, exactly
  `[propext, Classical.choice, Quot.sound]`; it is not a timing artifact or
  Phase-4 evidence.

## Current frontier

- Directive #9017 is implementation-complete and ready for the stacked draft
  PR and independent review.
- No release timing artifact or `done_through` update is included.

## Next step

- Publish the draft on the compiled-benchmark branch, obtain and address an
  independent Claude review, then restack as the extraction parents merge.
- Continue the remaining HexRCF SPEC/manual completion audit while CI and
  review run.

## Blockers

- None for the structural proof-probe milestone.
- A release-quality Phase-4 report still requires the clean named-host sweep
  and completion of the HexRealRootsMathlib dependency gate.
