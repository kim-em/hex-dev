# HexMvPoly SymPy conformance

## Accomplished

- Added a self-describing `mvpoly` JSONL fixture schema and shared emitter
  helpers.
- Added one source of committed Lean fixtures shared by the core conformance
  module and emit executable.
- Covered the full Mathlib-free API on typical, edge, and adversarial inputs,
  including normalization, ring laws, all monomial operations, queries,
  evaluation, structural transformations, and recursive-view round trips.
- Added 108 reproducible JSONL records and a SymPy oracle that independently
  checks 59 construction, arithmetic, query, ordering, derivative,
  evaluation, rename, substitution, and partial-evaluation results.
- Extended the existing single CI job with the emitter target, SymPy
  dependency/preflight, and one sequential oracle tuple.
- Incorporated an independent Claude Opus review: added nondegenerate query
  coverage, a grlex/grevlex tie-break discriminator, shared fixtures, three
  cases per externally checked operation, and genuine SymPy degree queries.
- Passed repository lints, fixture reproduction, the complete
  `HexConformance` build (9269 jobs), and all SymPy comparisons.

## Current frontier

The conformance slice is ready to rebase and publish. PR #9095 (the preceding
order/algebra law slice) remains the sole open HexMvPoly PR with auto-merge
armed.

## Next step

After #9095 merges, rebase and publish this conformance slice, then implement
the Mathlib-free benchmark suite while its CI runs.

## Blockers

No implementation blocker. Publication is intentionally sequenced behind
PR #9095.
