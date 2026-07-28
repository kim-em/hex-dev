# NumberField testing review repair

## Accomplished

- Reworked the lazy-add benchmark so eliminant construction occurs inside the
  timed kernel, while irreducibility checks remain outside inversion and root
  timings.
- Expanded core conformance across checked and total `AlgebraicRoot`
  arithmetic, canonical `AlgebraicNumber` arithmetic, fixed-field arithmetic
  and conversions, rational smul, semantic polynomial trimming, and checked
  and total fixed-field and algebraic-coefficient root APIs.
- Added adversarial tiny-root inversion and a multiplication case whose
  unselected zero conjugate introduces an irrelevant power of `X`.
- Made the external inverse oracle construct an independent PARI resultant,
  normalized product eliminants after removing introduced powers of `X`, and
  rejected exactification boxes outside the exact-double profile.
- Added fixed-field and algebraic-coefficient root fixtures and checked their
  discs and multiplicities against FLINT's certified Arb root balls. The
  deterministic fixture stream now contains 27 records across 10 cases.
- Made every fixed benchmark fail loudly on fixture/operation failure and
  pinned all eight observed result hashes.
- Built the conformance, emitter, benchmark, and full repository; regenerated
  and diffed fixtures; verified and ran all eight benchmarks; and passed the
  relevant Python, shell, DAG, line-count, copyright, Mathlib-free, and diff
  checks.

## Current frontier

The independent review's material NumberField findings are repaired. The
draft branch still intentionally does not advance phase bookkeeping because
later testing artifacts are stacked before the existing proof obligations are
closed.

## Next step

Publish the repair, leave a follow-up independent review running in a detached
worktree, then rebase the NumberFieldTower testing branch and address its
benchmark attribution and silent-failure findings without waiting for that
review.

## Blockers

The local environment lacks `python-flint` and `cypari2`, so the live combined
oracle skips locally. Its Python sources compile, emitted fixtures are stable,
and CI installs both dependencies.
