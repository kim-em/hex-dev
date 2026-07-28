# Number-field semantic equality and zero certification

## Accomplished

- Proved the Mathlib-free executable irreducibility and squarefreeness facts
  needed for the canonical representation of zero, without evaluating the
  opaque factorizer in the kernel.
- Replaced the fallible zero construction with one explicit certified
  representative at `separationDepth`, while retaining an executable guard
  that the ordinary root isolator succeeds on `X`.
- Proved semantic correctness of successful canonicalization, Boolean
  equality, and both zero predicates, adding the required complex-geometry and
  root-uniqueness bridges.
- Preserved the published Mathlib factorization API while moving its
  Mathlib-free positive-degree proof to the computational library.
- Updated the number-field SPEC to document the explicit canonical-zero path.
- Passed focused builds, the full 9,559-job build, number-field conformance,
  all eight number-field benchmark smoke cases, `git diff --check`, and an
  explicit axiom audit with no `sorryAx` in the new theorems.
- Addressed the substantive independent-review findings: canonical precision,
  isolator evidence, fast-path semantic preservation, public API compatibility,
  and explicit dependent transport.

## Current frontier

The semantic equality and zero-certification milestone is complete locally and
ready to be rebased onto current `origin/main`, published as the sole task PR,
and merged before any further implementation begins.

## Next step

Commit this milestone, rebase it over current main, rerun integration checks,
push and open one PR, inspect the underlying GitHub Actions jobs, and merge once
green.

## Blockers

None.
