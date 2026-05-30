**Accomplished**

- Investigated `HexBerlekampZassenhaus.factor` against Isabelle/AFP's
  extracted-Haskell `factor_int_poly` and identified a live regression:
  hex BZ returns mathematically wrong factorisations on
  `(x-1)(x-2)…(x-n)` for several `n ∈ [11, 24]` and is 200–2,400×
  slower than the AFP comparator even when correct. Root cause is
  `isGoodPrime`'s `gcd == 1` check rejecting square-free polynomials
  whose `DensePoly.gcd` returns a non-monic unit, which then triggers
  the silent `fallbackPrimeChoiceData → p = 3` cascade. Full diagnosis
  + five orchestration gaps in
  [reports/bz-vs-isabelle-investigation.md](../reports/bz-vs-isabelle-investigation.md).
- Produced this SPEC-clarification PR per the
  `spec-driven-development` skill discipline (SPEC PR first, worker
  issues against the new SPEC second). The PR codifies four
  orchestration requirements that the project did not have when BZ's
  Phase-4 bench scaffolding landed under HO-3 (#2566):
  - `SPEC/Libraries/hex-berlekamp-zassenhaus.md`: new
    `## External comparators` section declaring the verified-Isabelle
    BZ comparator as `gating` with goal `hex/isabelle ≤ 1×` and an
    explicit algorithm-class caveat, and new
    `## Headline correctness theorem` section pinning the semantic
    shape of `factor`'s post-condition (five clauses: product
    preservation, primitive irreducibility, positive multiplicities,
    no factor associates, scalar carries sign × content).
  - `libraries.yml`: `HexBerlekampZassenhaus.phase4.comparators` entry
    matching the SPEC clause.
  - `SPEC/design-principles.md`: new principle 8 ("Fallback discipline
    for total forms of partial helpers"), sibling of principle 7, with
    exactly two admissible classifications
    (`unreachable-by-pipeline-invariant` /
    `audited-emergency-value`). `refactor-pending` is not admissible;
    existing total forms must be proved unreachable or removed before
    the next `done_through` bump past their phase.
  - `PLAN/Conventions.md`: cross-reference paragraphs making both new
    SPEC rules discoverable from the per-session conventions read.
- Drafted dispatched worker artefacts (file these after the SPEC PR
  merges):
  [reports/bz-spec-comparator-pr-draft.md](../reports/bz-spec-comparator-pr-draft.md)
  (the PR body itself, in long form),
  [reports/bz-rollback-issue-draft.md](../reports/bz-rollback-issue-draft.md)
  (HO-5 + four children HO-5a/b/c/d), and a separate tactical
  `isGoodPrime` fix issue bundled with the failing-conformance
  fixtures.
- Moved the investigation's diagnostic Lean files + Python
  comparators + plotting scripts to
  [reports/scratch/](../reports/scratch/) with a README documenting
  what each one probes, so the evidence persists alongside the
  reports rather than as orphaned working-tree state.

**Current frontier**

- This PR is SPEC text + metadata only. It does not touch Lean code.
- After merge, the dispatched worker issues land: HO-1 (#2564)
  reframed in place to name the headline correctness theorem as its
  deliverable (preserving the existing additive-vs-multiplicative
  lattice diagnosis); HO-5 coordination issue + four children
  (HO-5a wires the comparator with an acceptance matrix, HO-5b
  rewrites the perf report against ratios, HO-5c extends the bench
  schedules, HO-5d removes `fallbackPrimeChoiceData`); a bundled
  tactical `isGoodPrime`-fix-plus-fixtures issue.

**Next step**

- Kim reviews and (per spec-driven-development doctrine) merges this
  PR. After merge, the worker issues above are filed; HO-1 is
  edited in place.

**Blockers**

- None for this PR. The PR is dispatchable on its own; downstream
  work blocks on merge.
