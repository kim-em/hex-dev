# RCF conformance and independent oracle

## Accomplished

- Merged the proof-producing `rcf` tactic milestone after hosted CI passed.
- Added the HexRCF core conformance module with the five SPEC examples,
  compiled decision/certificate branch checks, all four quantifier shapes,
  half-open endpoint ownership, equal/reversed intervals, fail-closed replay,
  isolation, carrier, and common-root mutations, and stable refusal/false
  diagnostics.
- Added a typed, versioned `rcf_sentence` wire AST and JSONL emission helper.
  The RCF emitter serialises only the original sentence AST, emits exactly one
  Boolean result, and throws if certificate construction returns `none`.
- Added exactly 30 structured deterministic CI sentences from seed `0x524346`,
  covering every comparison/connective/quantifier, both verdicts, constants,
  no roots, shared/repeated roots, endpoint ownership, close roots, and
  equal/reversed domains. Added a separate three-case local stress profile
  including a degree-50 Mignotte polynomial.
- Added strict recursive schema validation and an independent python-flint
  oracle. It independently factors the atom product, certifies the complete
  ordered real-root decomposition with Arb balls, samples open cells exactly,
  handles root cells by irreducible-factor divisibility and continuity, and
  folds the quantified sentence without consuming Lean evidence.
- Corrected two stale SPEC premises: `scripts/ci/run_oracles.sh`, not an
  unsupported `libraries.yml` block, is the oracle registry; the developer
  local emitter exercises compiled workloads but is not a tactic-elaboration
  benchmark.
- Wired the conformance module and emitter into Lake and the existing single
  CI job, added the sequential oracle tuple, documented the oracle assignment,
  and advanced `HexRCF.done_through` to 3.
- Reproduced the committed fixture exactly. python-flint matched all 30 CI and
  all 3 local cases. The full sequential oracle runner, focused targets,
  manifest/target checks, structural trust scan, and the 9497-job monorepo
  build all pass.

## Current frontier

Issue #8966 is complete and independently audited with no remaining blocking
defect. The branch is ready to publish as a stacked PR.

## Next step

Publish and monitor the conformance/oracle PR, then begin the Phase-4 timing
and release-readiness validation on a new stacked branch while hosted CI runs.

## Blockers

None. The fresh Opus launcher remains unavailable because its OAuth session
expired, but multiple independent Sol audits covered the architecture,
python-flint API, oracle soundness, fixture schedule, and final diff.
