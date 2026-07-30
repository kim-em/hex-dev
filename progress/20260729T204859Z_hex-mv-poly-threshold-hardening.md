# HexMvPoly threshold hardening

## Accomplished

- Added construction-only controls and larger proof-probe rungs for the
  cancellation and SOS families.
- Made representation-gate classification threshold-aware: a family passes
  only when its conservative ratio lower bound exceeds 2, after import and,
  where available, construction subtraction.
- Corrected the size-eight structural corpus so its rename probe contains four
  genuine collision pairs, with a downstream kernel check.
- Expanded the public query surface with characterization and zero laws. Added
  the reusable `Std.ExtTreeMap.maxEntry?_empty` law to the designated Std-only
  upstream-candidate file.
- Expanded the SOS compatibility layer to compile against all nine companion
  `aeval` homomorphism lemmas while retaining the legacy direct-evaluation
  signature.
- Added ordinary unscoped `Int` and `Rat` executable and algebra-law checks
  before activating the Mathlib bridge scope.
- Passed all 63 sweep-harness tests, the full 9,650-job build, the 9,266-job
  conformance build, all 11 native benchmark smoke checks, exact fixture
  comparison, DAG/release/Phase-4/Mathlib-free policy checks, and fresh pinned
  SOS and CompPoly acceptance builds (1,545 and 1,902 jobs respectively).
  The local SymPy oracle path skipped cleanly because SymPy is unavailable.

## Current frontier

The code and measurement harness now address the independent review findings.
The performance reports and representation decision still describe the
superseded v3 capture.

## Next step

Commit this cleanly verified harness/API checkpoint, capture a release-quality
v4 kernel sweep from that revision, and update the reports and SPEC decision
from the conservative threshold statuses.

## Blockers

None.
