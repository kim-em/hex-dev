# Phase 4: Performance and Benchmarking

**Coupling:** dep-coupled. Library L can start Phase 4 once
`libraries.yml[L].done_through ≥ 3` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 4`.

Phase 4 makes algorithmic complexity a first-class deliverable. By
the end of Phase 4 every advertised operation in the library's API
has a textbook complexity model declared at its `setup_benchmark`
registration, and a benchmark family whose verdict is *consistent
with declared complexity*. An *inconclusive* verdict is not a Phase
4 exit; it is a finding that triggers a rollback per
[Conventions.md §Rollback is a normal action](Conventions.md#rollback-is-a-normal-action)
and a fix at the rolled-back phase.

The harness, the registration forms, the CLI surface, the
verdict-as-bug-trigger doctrine, and the anti-patterns all live in
[SPEC/benchmarking.md](../SPEC/benchmarking.md). Read it before
opening Phase 4 issues.

## Deliverables

For each library `HexFoo` advancing through Phase 4:

1. **`HexFoo.Bench` exe** — rooted at `HexFoo/Bench.lean`, with
   helper modules under `HexFoo/Bench/` when useful. It registers
   every advertised operation in the library's SPEC API surface
   with `setup_benchmark` (parametric) or
   `setup_fixed_benchmark` (canonical input). The complexity
   expression in each `setup_benchmark` is the *textbook*
   complexity, not the observed one.

2. **`lakefile.lean` exe entry**:

   ```lean
   lean_exe hexfoo_bench where
     root := `HexFoo.Bench
   ```

   On the first library to enter Phase 4, also add the lean-bench
   `require` (per the snippet in
   [SPEC/benchmarking.md §Harness](../SPEC/benchmarking.md#harness-lean-bench)).

3. **Bench-module smoke gate** — `lake exe hexfoo_bench list &&
   lake exe hexfoo_bench verify`. `verify` is the bitrot gate; it
   does not assert timing values. It may use reduced smoke settings,
   but may not weaken the scientific settings used for real runs.
   This gate runs worker-side before publishing PRs, not in
   merge-gating CI; see
   [SPEC/benchmarking.md §Worker affected-bench discipline](../SPEC/benchmarking.md).
   A scheduled `nightly-bench-verify.yml` workflow against `main`
   is the backstop.

4. **`compare` registrations** for any pair of alternative algorithms
   the library SPEC calls out (e.g. Barrett vs Montgomery, linear vs
   quadratic Hensel, exponential-recombination vs LLL-assisted
   recombination). The `compare` invocation joins on result hashes
   and serves as the cross-implementation conformance check; a
   divergence at a common parameter is treated as any other
   conformance failure. Each required `compare` group must have an
   intentional common domain.

5. **External-comparator registrations** where the library SPEC
   names an architecturally important external tool (FLINT, fpLLL,
   GMP, NTL for FFI; Sage, GAP, PARI, python-flint for process
   calls). Each named comparator carries a classification per
   [SPEC/benchmarking.md §Comparator classification](../SPEC/benchmarking.md#comparator-classification-gating-vs-informational)
   — `gating` (must be wired before Phase 4 is claimed) or
   `informational` (ratio recorded, may be scheduled-only).
   Structured metadata lives in `libraries.yml: phase4.comparators`.
   FFI is preferred; see
   [SPEC/benchmarking.md §External comparators](../SPEC/benchmarking.md#external-comparators)
   for the integration patterns.

6. **Profile coverage** per
   [SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md#coverage-requirement):
   at least one representative case per `phase4.input_families`
   entry in `libraries.yml`, recorded in
   `reports/<lib>-performance.md §Profile`. Categorise leaf cost
   across {own code, GMP, allocation, Lean runtime}; rank inclusive
   cost; explain the dominant entries.

7. **Headline report** at `reports/<lib>-performance.md` per
   [SPEC/benchmarking.md §Headline reports](../SPEC/benchmarking.md#headline-reports).
   Five subsections: Bench targets, Verdicts, Comparator ratios,
   Profile, Concerns. Every numeric claim cites the bench case
   name, command line, seed/parameter, JSONL path, profile
   location, and comparator source.

The PR description records, in one paragraph, any case where the
declared complexity model differs from the canonical textbook
complexity (e.g. amortised vs worst-case, randomised vs
deterministic). This is the only "performance rationale" section
required.

## Discipline

- **Declare textbook complexity.** Not the observed complexity of
  the current implementation. If the textbook is `O(n²)` and the
  current code is `O(n³)`, declare `O(n²)`, run the benchmark, get
  the inconclusive verdict, file the issue, roll back. The
  benchmark's job is to reveal the gap, not to ratify it.
- **Use one harness.** lean-bench is the inner harness; gaps go to
  its issue tracker, not into a hex-local replacement.
- **Use stable case names.** The `setup_benchmark` declaration name
  is the case name; renaming a registration is a tracked change.
- **Use fixed seeds and committed inputs.** Randomised inputs
  derive from a seed tied to the benchmark name; canonical hard
  inputs live under `HexFoo/Bench/Inputs/`.
- **Keep smoke and scientific settings distinct.** `verify` is for
  wiring; Phase 4 completion is judged on real runs.
- **Cover downstream call patterns.** When the SPEC declares an
  operation the production hot path of a downstream operation, the
  bench parameter schedule must cover the parameter values the
  downstream caller actually produces. A schedule that excludes the
  downstream-realistic range cannot detect a wrong-asymptotic
  implementation that downstream use exercises. The schedule must
  vary every parameter the operation takes that the downstream
  caller varies — not only the most obvious one.

## Exit criteria

For library `hex-foo`, Phase 4 is done when:

- every operation listed in the library's SPEC API surface has a
  `setup_benchmark` or `setup_fixed_benchmark` registration in the
  `HexFoo.Bench` exe;
- every parametric registration declares a complexity model that
  matches the SPEC's textbook complexity for that operation;
- every new or changed parametric registration has an adjacent
  cost-model derivation comment, and every PR that changes a
  `setup_benchmark` complexity declaration includes an independent
  cost-model derivation in the commit message that made the change;
- `lake exe hexfoo_bench verify` succeeds under smoke settings, and
  `lake exe hexfoo_bench run NAME` returns *consistent with declared
  complexity* for every parametric registration at its scientific
  settings;
- every `compare` group named by the SPEC is registered and reports
  `allAgreed` on its declared common domain;
- every comparator declared `gating` in `libraries.yml:
  phase4.comparators` is wired and the headline report records its
  measured ratio; `informational` comparators record ratios but do
  not gate;
- the [Attribution rule](../SPEC/benchmarking.md#the-attribution-rule)
  is satisfied: every dominant profiled cost maps to a registered
  bench target, or the per-library SPEC documents why the cost
  cannot be separated;
- a profile run per
  [SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md#coverage-requirement)
  is recorded in `reports/<lib>-performance.md §Profile`;
- the headline report at `reports/<lib>-performance.md` exists with
  the five mandated subsections and full artefact traceability;
- the headline report's §Concerns subsection is empty. A library
  cannot **remain** at `done_through: 4` while any Concern is
  unresolved; the orchestrator rolls back if this state is detected.
  The only resolution available to the orchestrator is to act on
  the HO issue tied to the Concern until the underlying problem is
  fixed and the Concern entry is removed from the report.
- the Phase-4 PR/report records the exact
  `lake exe hexfoo_bench list` and `lake exe hexfoo_bench verify`
  invocations the author ran (paired with their outcomes, the host
  and toolchain, and the bench target names produced). CI does not
  run `verify` per PR; this is the evidence trail in place of that
  gate. The scheduled `nightly-bench-verify.yml` workflow against
  `main` provides the residual backstop.

If any of these fail, the right action is rollback per
[Conventions.md](Conventions.md), not a SPEC-text edit weakening
the criterion.

### Audit reset

As of the merge of the PR introducing the new exit criteria above
(profile coverage, headline report, gating-comparator wiring,
Attribution rule, empty-Concerns), every library currently at
`done_through ≥ 4` is re-evaluated under those criteria. The
re-evaluation is queued via a single umbrella `human-oversight`
issue with a checkbox per library; per-library follow-on issues
are filed only when the audit identifies actual gaps. Libraries
already passing all new criteria stay at `done_through: 4`
unchanged.

Record completion by bumping `libraries.yml[L].done_through` to `4`.
