# NumberFieldTower testing review repair

## Accomplished

- Replaced silent benchmark fallbacks with loud fixture failures and pinned the
  semantic checksum of every fixed benchmark.
- Split tower arithmetic into independently timed addition, multiplication,
  and inversion cases, and added coverage for one-level norms, square-free
  shift search, rational presentation construction, identity adjoining,
  factorization checking, and the separable flattening stages.
- Added the committed degree-six bad-first-candidate fixture to isolated
  primitive-element recovery and bounded-search benchmarks.  The flattening
  checksums now cover both coordinate maps on every tower basis vector.
- Thunked computational fixture builders and cached their results during
  warmup.  This reduced executable startup from roughly 7.2 seconds to 0.05
  seconds and keeps factorization, tower construction, and exactification out
  of timed bodies.
- Expanded the tower suite from seven to nineteen fixed registrations.  All
  nineteen expected hashes pass `verify`; the adversarial recovery search has
  a measured call time of roughly 30.5 seconds and a 60-second cap.
- Passed `lake build hexnumberfieldtower_bench`, the full `lake build`, and
  `git diff --check`.

## Current frontier

The actionable NumberFieldTower benchmark findings are repaired.  The suite
now attributes the dominant public stages and exercises both the successful
dimension-four flattening path and a genuine nonlinear-recovery retry.

## Next step

Commit and publish this repair, launch its follow-up independent review in a
detached worktree, then return to the newly completed NumberField follow-up
review to fix its root-selection checksum and constant-foldable isolator case
before restacking this branch.

## Blockers

The repository-wide benchmark-budget wrapper cannot complete in this local
environment because the pre-existing FLINT comparison registrations in
`hexpoly_bench` require the unavailable `python-flint` module.  The tower-only
verification and full Lean build are green.
