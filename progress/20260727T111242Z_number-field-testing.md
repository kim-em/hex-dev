# NumberField testing milestone

## Accomplished

- Added core conformance coverage for fixed-presentation arithmetic, lazy
  arithmetic, exactification, root isolation, cancellation, and adversarial
  presentation/root-selection cases.
- Added deterministic JSONL fixtures for lazy arithmetic and exactification,
  together with an independent PARI/FLINT oracle that starts from the original
  operand or enclosing polynomials.
- Added eight Mathlib-free LeanBench registrations covering fixed arithmetic,
  the lazy elimination/isolation/selection stages, end-to-end lazy addition,
  exactification, and root construction.
- Extended the existing single CI job with the new conformance emitter,
  oracle, and benchmark executable.
- Built `HexConformance`, the emitter, and the benchmark; regenerated and
  diffed fixtures; verified all eight benchmarks; and passed repository DAG,
  line-count, copyright, fixture-target, Mathlib-free benchmark, shell syntax,
  Python syntax, and diff-hygiene checks. Benchmark verification took two
  seconds against the 600-second hard cap.

## Current frontier

The NumberField testing profile is complete locally. The fixture stream has
seven cases (twenty JSONL records), including repeated-resultant-factor and
nonminimal-enclosing-polynomial cases.

## Next step

Publish this milestone as a stacked draft PR, launch its independent review in
a dedicated detached worktree, and continue with the NumberFieldTower testing
milestone while that review runs.

## Blockers

The local environment does not contain `python-flint` or `cypari2`, so the live
external oracle run skips locally. Its script compiles, follows APIs already
used by the repository's existing FLINT/PARI oracles, and is wired into CI,
where those dependencies are installed.
