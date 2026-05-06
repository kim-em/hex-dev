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

3. **CI smoke step** invoking
   `lake exe hexfoo_bench list && lake exe hexfoo_bench verify`.
   `verify` is the bitrot gate; it does not assert timing values.
   It may use reduced smoke settings, but may not weaken the
   scientific settings used for real runs.

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
   calls). FFI is preferred; see
   [SPEC/benchmarking.md §External comparators](../SPEC/benchmarking.md#external-comparators)
   for the integration patterns. Each required comparator must end
   Phase 4 as either implemented now, scheduled-only with its
   environment stated, or blocked by a narrow issue that keeps the
   library below completion.

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
- every external-comparator registration named by the SPEC is wired
  (FFI shim or process call), with its execution policy recorded in
  the bench module docstring;
- no registration is merely "consistent" while still orders of
  magnitude slower than a named architectural comparator on the same
  canonical task family;
- the CI smoke step (`list` + `verify`) runs on every PR.

If any of these fail, the right action is rollback per
[Conventions.md](Conventions.md), not a SPEC-text edit weakening
the criterion.

Record completion by bumping `libraries.yml[L].done_through` to `4`.
