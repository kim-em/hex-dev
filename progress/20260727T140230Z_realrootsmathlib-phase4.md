# HexRealRootsMathlib Phase-4 proof probes

## Accomplished

- Identified `HexRealRootsMathlib.done_through: 3` as the immediate dependency
  gate before HexRCF may start Phase 4, while HexRCF conformance PR #8970 runs
  CI with auto-merge enabled.
- Opened critical-path issue #8972 after premise-checking the distinction
  between bookkeeping-only Mathlib bridges and the user-facing
  `isolate_roots` elaborator.
- Added build-only fresh-module probes with a matched import baseline,
  natural-width Wilkinson degrees 6/8/10, and width-`2^-20` degrees 2/4/6.
- Added their Lake, DAG, and existing single-job CI build wiring. No executable,
  LeanBench registration, job, matrix, or workflow was introduced.
- Added `scripts/bench/real_roots_mathlib_sweep.py`, which rotates exact
  fresh-module Lake builds and records wall time, matched baseline margins,
  RSS, axiom sets, artifacts, environment, and source hashes.
- Built every probe successfully. Each measured isolation reports exactly
  `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

## Current frontier

The probe implementation and harness are ready. The scientific sweep and
headline report remain to be produced from a clean implementation commit.

## Next step

Commit the probe infrastructure, run the clean three-sample sweep, audit the
results against the SPEC's practical limits, write the Phase-4 report, and
advance `HexRealRootsMathlib.done_through` only if the report has no concern.

## Blockers

HexRCF itself cannot yet claim Phase 4: after this dependency advances, the
generic Phase-4 LeanBench contract still conflicts with its Mathlib-dependent
elaboration-only tactic surface. A separate contract directive is required.
