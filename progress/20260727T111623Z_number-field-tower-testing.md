# NumberFieldTower testing milestone

## Accomplished

- Audited the existing Tower core conformance and nine-case PARI fixture
  profile against the library testing contract; they already cover the public
  operations, degenerate inputs, fixed embeddings, recursive Trager cases,
  splitting, and primitive-element recovery.
- Added seven Mathlib-free LeanBench registrations for dimension-four tower
  arithmetic, adjoining a fourth root, rational factorization, a bad-first-
  shift Trager retry, recursive intermediate-field factorization, quartic
  splitting, and two-level flattening.
- Registered the executable in Lake and extended the existing single CI job's
  build and sequential benchmark-verification lists.
- Built the executable, listed and verified all seven registrations, and
  passed the benchmark wallclock, Mathlib-import, conformance-target, DAG,
  line-count, copyright, diff-hygiene, and forbidden-token checks. Benchmark
  verification took three seconds against the 600-second hard cap.

## Current frontier

The NumberFieldTower testing surface is complete at the merge-facing ceiling
of dimension four and input degree four used by these fixtures.

## Next step

Publish this milestone as a stacked draft PR and launch its independent review
in a detached worktree. Then repair the actionable findings returned by the
asynchronous Resultant testing review and restack affected descendants.

## Blockers

None.
