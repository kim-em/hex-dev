# Phase 4: Performance and Benchmarking

**Coupling:** dep-coupled. Library L can start Phase 4 once
`libraries.yml[L].done_through ≥ 3` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 4`.

Phase 4 makes algorithmic complexity a first-class deliverable. By
the end of Phase 4 every advertised compiled operation in the library's API
has the strongest applicable benchmark mode from
[`SPEC/benchmarking.md` §Choosing the complexity claim](../SPEC/benchmarking.md#choosing-the-complexity-claim)
and a passing result in that mode; every advertised tactic or proof generator
has example files that CI builds, as defined below. An *inconclusive* compiled verdict is not
a Phase 4 exit unless it is the current harness wording for a documented,
passing one-sided upper-bound result. A failing result triggers a rollback per
[Conventions.md §Rollback is a normal action](Conventions.md#rollback-is-a-normal-action)
and a fix at the rolled-back phase.

The harness, the registration forms, the CLI surface, the
verdict-as-bug-trigger doctrine, and the anti-patterns all live in
[SPEC/benchmarking.md](../SPEC/benchmarking.md). Read it before
opening Phase 4 issues.

## Evidence tracks

Phase 4 classifies each advertised operation by what is actually being
measured. A library may have one track or both; its SPEC must assign every
advertised compiled operation, tactic or proof generator to exactly one row.

Ordinary theorem applications and instance-law proofs use correctness tests,
not dedicated timing probes. The proof track below measures tactic execution,
proof generation, certificate checking and the kernel computations they perform.
Profiling the elaboration or kernel checking of other proofs is appropriate when investigating an
observed build-cost problem.

| Surface | Required evidence | Generic requirements replaced |
| --- | --- | --- |
| Mathlib-free compiled computation | An ordinary LeanBench executable, registrations with controlled one-parameter ladders and adjacent independent cost derivations, `list`/`verify`, scientific verdicts, comparator coverage, and timed-region sampling profiles. | None. |
| Tactic execution, proof generation, and their certificate and kernel checking | A few example files below an explicit `libraries.yml` `proof_probes` root, each running the tactic or proof generator on a representative input, built by CI on every PR. | No LeanBench registration or executable, no `list`/`verify` entry for that surface, no complexity verdict, no profile, and no headline report. |

A `mathlib: true` library with a separable compiled core is a **mixed**
library, not a proof-only exception. Its compiled core obeys every ordinary
LeanBench requirement, while its tactic/proof surface uses the second row.
Proof-track example files are never substitutes for the compiled track's
asymptotic ladders, and the headline report covers the compiled track only.

## Deliverables

For each library `HexFoo` advancing through Phase 4:

1. **`HexFoo.Bench` exe** — for every compiled-track operation, rooted at
   `HexFoo/Bench.lean`, with helper modules under `HexFoo/Bench/` when useful.
   It registers every compiled operation in the library's SPEC API surface
   with `setup_benchmark` (parametric) or
   `setup_fixed_benchmark` (canonical input). The complexity
   expression in each `setup_benchmark` is the independently derived expected
   family scaling for a two-sided registration or the cited published bound
   for a one-sided registration, never a model read from observed timings.
   Proof-track operations instead have example files under an explicit
   manifest `proof_probes` directory; those files are not registrations.

2. **`lakefile.lean` exe entry** for a library with compiled-track targets:

   ```lean
   lean_exe hexfoo_bench where
     root := `HexFoo.Bench
   ```

   On the first library to enter Phase 4, also add the lean-bench
   `require` (per the snippet in
   [SPEC/benchmarking.md §Harness](../SPEC/benchmarking.md#harness-lean-bench)).

3. **CI smoke step** invoking, when the compiled track exists,
   `lake exe hexfoo_bench list && lake exe hexfoo_bench verify`.
   `verify` is the bitrot gate; it does not assert timing values.
   It may use reduced smoke settings, but may not weaken the
   scientific settings used for real runs. Proof-probe files are built by the
   existing build job; they never become executable roots.

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

6. **Profile coverage** for the compiled track per
   [SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md#coverage-requirement):
   at least one representative case per `phase4.input_families`
   entry in `libraries.yml`, recorded in
   `reports/<lib>-performance.md §Profile`. Categorise leaf cost
   across {own code, GMP, allocation, Lean runtime}; rank inclusive
   cost; explain the dominant entries. The proof track has no profile
   requirement.

7. **Headline report** at `reports/<lib>-performance.md` per
   [SPEC/benchmarking.md §Headline reports](../SPEC/benchmarking.md#headline-reports).
   Five subsections: Bench targets, Verdicts, Comparator ratios,
   Profile, Concerns. Every numeric claim cites the bench case
   name, command line, seed/parameter, JSONL path, profile
   location, and comparator source. A library with no compiled track has no
   headline report.

The PR description records, in one paragraph, any case where the benchmark
claim differs from the per-library SPEC's worst-case contract (for example,
family-specific expected scaling, amortised versus worst-case, or randomised
versus deterministic). This is the only "performance rationale" section
required.

## Discipline

- **Declare the intended algorithm's independently derived expected scaling on
  the registered family.** Derive it before measurement and never read it off
  observed timings. The adjacent derivation must explain how the family
  relates to the per-library SPEC's worst-case bound. When a tight family model
  is unavailable, work the ordered alternatives in
  [`SPEC/benchmarking.md` §Choosing the complexity claim](../SPEC/benchmarking.md#choosing-the-complexity-claim)
  rather than fitting the declaration to the current implementation.
- **Use the assigned harness.** LeanBench is the sole compiled-code inner
  harness. The external fresh-build runner is permitted only for proof-track
  evidence and may not time compiled computation redundantly.
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

- every compiled operation, tactic or proof generator listed in the library's
  SPEC API surface is assigned to a track, every compiled-track operation has a `setup_benchmark` or
  `setup_fixed_benchmark` registration in the `HexFoo.Bench` exe, and every
  proof-track operation has example files in the library's `proof_probes`
  root that CI builds;
- the headline report names the strongest applicable mode from
  `SPEC/benchmarking.md`'s ordered rule for every performance-evidence
  registration; fixed registrations used only as hash, comparator, or protocol
  anchors are labelled as such and cannot satisfy operation coverage; every mode-1
  parametric declaration matches the independently derived expected scaling
  on its family, every
  mode-2 declaration is a cited published upper bound covering the dominant
  profiled phase, and every mode-3 registration has a canonical hard input and
  meaningful absolute budget;
- every new or changed parametric registration has an adjacent
  cost-model derivation comment, and every PR that changes a
  `setup_benchmark` complexity declaration includes an independent
  cost-model derivation in the commit message that made the change;
- when a compiled track exists, `lake exe hexfoo_bench verify` succeeds under
  smoke settings, and
  `lake exe hexfoo_bench run NAME` returns a passing verdict for every
  parametric registration's declared mode at its scientific settings; until
  lean-bench has a one-sided mode, the headline report may translate a mode-2
  harness result to the distinct passing result *within declared upper bound
  (observed faster)* or *within declared upper bound (observed matching)*, as
  its observed direction requires; a slower-than-declared observation fails
  mode 2 and admits no translation;
- every `compare` group named by the SPEC is registered and reports
  `allAgreed` on its declared common domain;
- every comparator declared `gating` in `libraries.yml:
  phase4.comparators` is wired and the headline report records its
  measured ratio; `informational` comparators record ratios but do
  not gate;
- the per-library SPEC's external-comparator declarations are
  complete per
  [SPEC/benchmarking.md §"Comparator naming"](../SPEC/benchmarking.md#comparator-naming):
  every required comparator is named with its class (optionally
  scoped per bench target), or the absence is declared with exactly
  one of the enumerated reasons (`implementation-is-extern`,
  `structural-layer`, `input-source-only`,
  `no-comparable-surface-in-named-comparator`). This applies to the
  compiled track only;
- the [Attribution rule](../SPEC/benchmarking.md#the-attribution-rule)
  is satisfied: every dominant profiled cost maps to a registered
  bench target, or the per-library SPEC documents why the cost
  cannot be separated;
- a profile run per
  [SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md#coverage-requirement)
  is recorded in `reports/<lib>-performance.md §Profile` for every compiled
  input family;
- when the library has a compiled track, the headline report at
  `reports/<lib>-performance.md` exists with the five mandated subsections and
  full artefact traceability;
- the headline report's §Concerns subsection is empty. A passing mode-2 or
  mode-3 registration is not itself a Concern merely because it makes a weaker
  claim than mode 1; its report must contain the ordered-rule rationale;
- the compiled-track CI step (`list` + `verify`) and the build of every
  declared proof-probe root run on every PR where their track exists.

If any of these fail, the right action is rollback per
[Conventions.md](Conventions.md), not a SPEC-text edit weakening
the criterion.

### Mathlib libraries

A `mathlib: true` library has no compiled track:
[SPEC/benchmarking.md §Mathlib-free benches](../SPEC/benchmarking.md#mathlib-free-benches)
forbids it a benchmark executable. If it owns a tactic, elaborator, or proof
generator, it declares a `proof_probes` root and takes the proof track.
Otherwise Phase 4 has no deliverables for it: it needs no headline report, no
comparator declaration, and no classification in its SPEC or `libraries.yml`.

### Criteria changes apply going forward

A change to these criteria applies to libraries claiming Phase 4 after it
merges. It does not re-audit libraries already at `done_through ≥ 4` or roll
them back. A library moves backward only when someone finds a defect in the
library itself, per
[Conventions.md §Rollback is a normal action](Conventions.md#rollback-is-a-normal-action).

Record completion by bumping `libraries.yml[L].done_through` to `4`.
