# Permutation-group Mathlib preparation

The supported tactic interface keeps certificate production, packing, bounded
kernel checks and auxiliary declaration management in Hex. The Mathlib adapter
only normalizes goals, supplies conversion equalities and translates the
computational conclusion. Generation/order semantics and basic conversions have
separate lightweight imports; the adapter does not install a group instance
on Hex permutations.

## Verification

- The complete monorepo build passed (13,931 jobs).
- Existing Mathlib tests and certificate tests, graph tactic consumers,
  permutation-group proof probes and the manual chapter built successfully.
- The lightweight adapter tests cover all four goal forms, literal sets,
  Finsets, set builders, definitions, false goals, fallback images, degrees
  zero and one, M11's order and a transposition's nonmembership.
- Public-interface tests check malformed canonical witnesses, wrong degrees,
  unresolved inputs, corrupted prepared data and rollback of declarations,
  assignments and goal lists. Kernel checks run synchronously within replay.
- A fresh consumer built the staged HexBasic and HexPermGroup packages,
  including the core regression tests, with no Mathlib in its manifest.
- Both computational and Mathlib certificate emitters produced source that
  compiled in separate processes and fresh consumer modules. The Mathlib
  consumer imported only the lightweight tactic module.
- The four-module upstream prototype built with Mathlib's options and linters.
  The release dry run used the live baseline and previewed the core package
  without overriding the uncoordinated-commit guard.

The manual chapter was not changed, so its rendered-page review requirement
is not triggered by this preparation. The migration boundary and sequence
are specified in [the plan](../PLAN/PermGroupMathlib.md).

## Kernel replay

The baseline is `f9ab615bbca2`, before this preparation. Inputs and source
are retained in [the results](bench-results/perm-group-mathlib-preparation.json),
including the ATLAS image lists and classical M11. The metric is Lean's
cumulative `type checking` profiler time. Each series uses an automatically
leased CPU, adjacent before/after arms followed by after/before arms, and
records host load. All 44 completed samples are retained.

Every final comparison stays within the 10% limit. M22's initial mean change
was +25.35%; its one permitted unchanged rerun gave -0.79%. The table uses
that rerun for M22 and the initial series for every other workload. These are
shared-host observations, without a claim of deterministic speedup or
multithreaded throughput. Subsequent review fixes affect source rendering and
compatibility aliases, rather than certificate production or replay; their
source hashes are recorded separately from the measured endpoints.

| Workload | Before (s) | After (s) | Change |
| --- | ---: | ---: | ---: |
| M11 | 0.09765 | 0.0902 | -7.63% |
| M11-classical | 0.09545 | 0.09045 | -5.24% |
| M12 | 0.123 | 0.1195 | -2.85% |
| M22 | 0.252 | 0.25 | -0.79% |
| M23 | 0.45 | 0.3985 | -11.44% |
| M24 | 0.5745 | 0.532 | -7.40% |
| HS | 5.75 | 5.975 | +3.91% |
| J2 | 3.06 | 2.71 | -11.44% |
| McL | 35.9 | 35.1 | -2.23% |
| Co3 | 85.5 | 76.3 | -10.76% |
