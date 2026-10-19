# Permutation-group Mathlib preparation

The supported tactic interface keeps certificate production, packing, bounded
kernel checks and auxiliary declaration management in Hex. The Mathlib adapter
only normalizes goals, supplies conversion equalities and translates the
computational conclusion. Generation/order semantics and basic conversions have
separate lightweight imports; the adapter does not install a group instance
on Hex permutations.

## Verification

- The complete monorepo build passed (13,936 jobs).
- Existing Mathlib tests and certificate tests, graph tactic consumers,
  permutation-group proof probes and the manual chapter built successfully.
- The lightweight adapter tests cover all four goal forms, literal sets,
  Finsets, set builders, definitions, false goals, fallback images, degrees
  zero and one, M11's order and a transposition's nonmembership.
- Public-interface tests check malformed canonical witnesses, wrong degrees,
  unresolved inputs, corrupted prepared data and rollback of declarations,
  assignments and goal lists. Kernel checks run synchronously within replay.
  Exception handlers in the regression tests do not restore state themselves;
  heartbeat and recursion-depth failures are also checked after partial replay.
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
retain a further full cohort of 40 samples, with no unchanged rerun. Canonical
packing now combines the transport and literal packing checks in one
auxiliary declaration, removing one declaration per canonical input while
preserving the packing evaluation. Finalizers also restore state after runtime
exceptions. Most kernel work is unchanged; the swing in M22 cannot be attributed
to this small change. The later cohort alone is within the limit, but it does
not erase the initial failure.

The table pools all 84 retained samples across both cohorts: six per arm for
M22 and four per arm for every other workload. These observed means are within
the 10% limit, with M22 at +7.55%. Small samples and changing baseline times
on the shared host prevent a precise estimate of the effect. No sample was
discarded, and no further unchanged measurements are taken to obtain acceptance.
The individual cohorts remain available in their result files.

| Workload | Before (s) | After (s) | Change |
| --- | ---: | ---: | ---: |
| M11 | 0.095725 | 0.08985 | -6.14% |
| M11-classical | 0.096375 | 0.09055 | -6.04% |
| M12 | 0.1235 | 0.11825 | -4.25% |
| M22 | 0.247167 | 0.265833 | +7.55% |
| M23 | 0.42675 | 0.395 | -7.44% |
| M24 | 0.55425 | 0.5285 | -4.65% |
| HS | 5.57 | 5.56 | -0.18% |
| J2 | 2.85 | 2.76 | -3.16% |
| McL | 34.05 | 34.175 | +0.37% |
| Co3 | 80.3 | 74.85 | -6.79% |
