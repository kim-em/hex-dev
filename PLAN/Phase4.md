# Phase 4: Performance and Benchmarking

**Coupling:** dep-coupled. Library L can start Phase 4 once
`libraries.yml[L].done_through ≥ 3` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 4`.

Phase 4 looks for performance bugs: an implementation that does not scale the
way its algorithm should. The harness, registration forms, CLI surface,
verdict-as-bug-trigger doctrine and anti-patterns live in
[SPEC/benchmarking.md](../SPEC/benchmarking.md). Read it before opening
Phase 4 issues.

Performance coverage is a judgement call. Where a performance check is useful
(an operation users will call at scale, a kernel with a known complexity, a
hot path a downstream library depends on, a choice between algorithms) it
should exist; where it would be pure ceremony it should not. A fixed
registration that only checks an output hash is a correctness and bitrot
check, not performance evidence. See
[SPEC/benchmarking.md §What needs performance evidence](../SPEC/benchmarking.md#what-needs-performance-evidence).

## Evidence tracks

A library may have one track or both:

- **Compiled track.** Mathlib-free compiled computation, measured by an
  ordinary LeanBench executable as described below.
- **Proof track.** Tactics, elaborators and proof generators keep a few
  example files below an explicit `libraries.yml` `proof_probes` root, built
  by CI on every PR; see
  [SPEC/benchmarking.md §Proof-probe example files](../SPEC/benchmarking.md#proof-probe-example-files).
  They carry no timing obligation and are never substitutes for the compiled
  track's ladders.

A `mathlib: true` library with a separable compiled core is a mixed library:
its compiled core takes the compiled track and its tactic surface the proof
track.

## Deliverables

For each library `HexFoo` advancing through Phase 4:

1. **`HexFoo.Bench` exe** rooted at `HexFoo/Bench.lean`, registering the
   compiled operations that warrant performance checks with
   `setup_benchmark` (parametric), and canonical inputs worth pinning with
   `setup_fixed_benchmark`. Each parametric declaration is an independently
   derived model or a cited upper bound, never a model read from observed
   timings, with the derivation in an adjacent comment.
2. **`lakefile.lean` exe entry**:

   ```lean
   lean_exe hexfoo_bench where
     root := `HexFoo.Bench
   ```

3. **CI step** running `lake exe hexfoo_bench list && lake exe hexfoo_bench
   verify`. `verify` is a required fast check for bitrot; it does not assert
   timing values. It may use reduced verify settings, but may not weaken the
   scientific settings used for real runs.
4. **`compare` registrations** for any alternative algorithms the library
   SPEC calls out (e.g. Barrett vs Montgomery, linear vs quadratic Hensel,
   exponential versus LLL-assisted recombination), and for any external
   comparator the SPEC sets a performance target against. Each `compare`
   group has an intentional common domain.

## Discipline

- **Declare the intended algorithm's independently derived expected scaling on
  the registered family**, derived before measurement and never read off
  observed timings. When no family model is derivable, declare a cited upper
  bound. The adjacent comment explains how the family relates to the
  per-library SPEC's worst-case bound.
- **Use the assigned harness.** LeanBench is the sole compiled-code harness.
- **Use stable case names, fixed seeds and committed inputs.**
- **Keep verify and scientific settings distinct.** `verify` is for wiring;
  performance claims are judged on real runs.
- **Cover downstream call patterns.** When the SPEC declares an operation the
  hot path of a downstream operation, the parameter schedule covers the values
  the downstream caller actually produces, varying every parameter the caller
  varies.

## Exit criteria

For library `hex-foo`, Phase 4 is done when:

- every performance claim the library makes has a complete scientific run;
- after at most the one identical rerun the
  [shared-host policy](../SPEC/benchmarking.md#shared-host-measurement-policy)
  permits, the evidence satisfies the declared two-sided model or cited upper
  bound;
- every completed run is retained: the raw JSONL is linked from the PR that
  advances the library;
- fixed hash-only registrations carry no performance verdict;
- every `compare` group named by the SPEC reports `allAgreed` on its common
  domain;
- `lake exe hexfoo_bench verify` passes in CI, and every declared proof-probe
  root builds in CI.

A failing result triggers a rollback per
[Conventions.md §Rollback is a normal action](Conventions.md#rollback-is-a-normal-action)
and a fix at the rolled-back phase, not a SPEC-text edit weakening the claim.

### Mathlib libraries

A `mathlib: true` library has no compiled track:
[SPEC/benchmarking.md §Mathlib-free benches](../SPEC/benchmarking.md#mathlib-free-benches)
forbids it a benchmark executable. If it owns a tactic, elaborator, or proof
generator, it declares a `proof_probes` root and keeps proof-probe example
files. Otherwise Phase 4 has no deliverables for it.

### Criteria changes apply going forward

A change to these criteria applies to libraries claiming Phase 4 after it
merges. It does not re-audit libraries already at `done_through ≥ 4` or roll
them back. A library moves backward only when someone finds a defect in the
library itself, per
[Conventions.md §Rollback is a normal action](Conventions.md#rollback-is-a-normal-action).

Record completion by bumping `libraries.yml[L].done_through` to `4`.
