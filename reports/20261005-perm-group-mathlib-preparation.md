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

The baseline is `f9ab615bbca2`, before this preparation. The metric is
Lean's cumulative `type checking` profiler time. Each series uses an
automatically leased CPU and adjacent AB/BA arms, recording host load.
All 84 completed samples are retained.

[The initial results](bench-results/perm-group-mathlib-preparation.json)
retain 44 samples. M22's initial comparison was +25.35%; its permitted
unchanged rerun was -0.79%. Pooling all four samples per arm gives +12.24%,
which exceeds the limit. That implementation did not establish acceptance.

[The packing results](bench-results/perm-group-mathlib-preparation-packing.json)
retain a new full cohort of 40 samples, with no unchanged rerun. Canonical
packing now combines the transport and literal packing checks in one
auxiliary declaration, removing one declaration per canonical input.
Finalizers also restore state after runtime exceptions. Every workload of
this implementation stays within the 10% limit; J2 has the largest mean
increase, +6.44%. The table uses all completed samples of this implementation.
These are shared-host observations, without a claim of deterministic speedup
or multithreaded throughput.

| Workload | Before (s) | After (s) | Change |
| --- | ---: | ---: | ---: |
| M11 | 0.0938 | 0.0895 | -4.58% |
| M11-classical | 0.0973 | 0.09065 | -6.83% |
| M12 | 0.124 | 0.117 | -5.65% |
| M22 | 0.239 | 0.2335 | -2.30% |
| M23 | 0.4035 | 0.3915 | -2.97% |
| M24 | 0.534 | 0.525 | -1.69% |
| HS | 5.39 | 5.145 | -4.55% |
| J2 | 2.64 | 2.81 | +6.44% |
| McL | 32.2 | 33.25 | +3.26% |
| Co3 | 75.1 | 73.4 | -2.26% |
