# HexRealRootsMathlib probe evidence hardening

## Accomplished

- Reworked the fresh-module sweep to hash the complete repository-local import
  closure of every probe and record each Lake dependency checkout's HEAD, tree,
  dirty status, and content-sensitive state digest.
- Made every Git provenance query fail closed and compare repository/package
  state before and after a sweep.
- Added clean-host admission: ordinary runs reject tracked or untracked dirt,
  dirty dependency checkouts, concurrent Lake/Lean processes, and excessive
  one-minute load per logical CPU. Explicit diagnostic overrides are recorded
  as invalidating exceptions in the artifact.
- Replaced round-wide baseline subtraction with a fresh import-only build
  immediately before every measured arm.
- Hardened timeout cleanup through TERM/KILL process-group handling and added
  seven regression tests covering transitive provenance, content changes,
  untracked checkout state, fail-closed Git errors, adjacent pairing, the
  `run_timed` timeout path, and a SIGTERM-resistant descendant.
- Added those harness tests to the existing single CI job. The combined 18
  benchmark-lint/harness tests, real lint, DAG, Python compile, and diff checks
  pass; an independent Sol re-review returned GO.

## Current frontier

The build-only probe and evidence harness are structurally ready for a
release-quality run. No measurement artifact or Phase-4 status claim has been
made from the busy shared host.

## Next step

Run the default three-sample adjacent-baseline sweep from a clean checkout on a
quiescent host, commit the resulting machine-readable artifact and five-part
headline report only if every practical limit passes, then advance
`HexRealRootsMathlib.done_through` to 4.

## Blockers

The shared host is still running unrelated Lake/Lean work, so the new default
admission check correctly rejects a scientific run here. Diagnostic overrides
must not be used for the Phase-4 claim.
