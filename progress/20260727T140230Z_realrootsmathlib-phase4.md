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
- Hardened timeout cleanup so a timed-out GNU-time/Lake wrapper terminates its
  complete process group before the harness reports failure.
- Built every probe successfully. Each measured isolation reports exactly
  `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
- Attempted the scientific sweep, but refused to treat the result as evidence:
  the host had roughly 159 concurrent Lake/Lean processes from unrelated
  worktrees, and the final refined-degree-6 arm hit the 60-second timeout.
- Opened contract directive #8973 for HexRCF's deeper Phase-4 conflict: the
  generic LeanBench requirements exclude the tactic/elaboration work they are
  supposed to validate and the existing bench lint misses module-system roots.

## Current frontier

The probe implementation and harness are ready and committed. The scientific
sweep is deliberately pending a quiescent host; no partial/noisy artifact was
written and `HexRealRootsMathlib.done_through` remains 3.

## Next step

Run the clean three-sample sweep when the host is quiescent, audit the results
against the SPEC's practical limits, write the Phase-4 report, and advance
`HexRealRootsMathlib.done_through` only if the report has no concern. Meanwhile
the independently actionable bench-lint repair from #8973 can proceed.

## Blockers

- Release-quality timing is blocked by current host saturation, not by CI or
  review state.
- HexRCF itself cannot yet claim Phase 4: after this dependency advances, the
  generic Phase-4 LeanBench contract still conflicts with its Mathlib-dependent
  tactic surface. Contract directive #8973 tracks that premise repair.
