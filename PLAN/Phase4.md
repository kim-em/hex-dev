# Phase 4: Performance and Benchmarking

**Coupling:** dep-coupled. Library L can start Phase 4 once
`libraries.yml[L].done_through ≥ 3` and every `d ∈ L.deps` has
`libraries.yml[d].done_through ≥ 4`.

Phase 4 makes algorithmic complexity a first-class deliverable. By
the end of Phase 4 every advertised compiled operation in the library's API
has a textbook complexity model declared at its `setup_benchmark`
registration and a benchmark family whose verdict is *consistent
with declared complexity*; every advertised proof/tactic operation has the
fresh-module evidence defined below. An *inconclusive* compiled verdict is not
a Phase 4 exit; it is a finding that triggers a rollback per
[Conventions.md §Rollback is a normal action](Conventions.md#rollback-is-a-normal-action)
and a fix at the rolled-back phase.

The harness, the registration forms, the CLI surface, the
verdict-as-bug-trigger doctrine, and the anti-patterns all live in
[SPEC/benchmarking.md](../SPEC/benchmarking.md). Read it before
opening Phase 4 issues.

## Evidence tracks

Phase 4 classifies each advertised operation by what is actually being
measured. A library may have one track or both; its SPEC must assign every
advertised operation to exactly one row.

| Surface | Required evidence | Generic requirements replaced |
| --- | --- | --- |
| Mathlib-free compiled computation | An ordinary LeanBench executable, registrations with controlled one-parameter ladders and adjacent textbook cost derivations, `list`/`verify`, scientific verdicts, comparator coverage, and timed-region sampling profiles. | None. |
| Elaboration, proof-search tactics, emitted proof terms, or kernel checking | Externally timed fresh-module builds below an explicit `libraries.yml` `proof_probes` root, with matched import baselines, rotated raw samples, compiler/proof artefacts, and the trust/provenance record in `SPEC/benchmarking.md`. | No LeanBench registration or executable, no `list`/`verify` entry for that surface, no complexity verdict, and no timed-region sampling profile. |

A `mathlib: true` library with a separable compiled core is a **mixed**
library, not a proof-only exception. Its compiled core obeys every ordinary
LeanBench requirement, while its tactic/proof surface uses the second row.
Fixed tactic-build budgets are acceptance cases, never substitutes for the
compiled track's asymptotic ladders. The headline report keeps the two tracks
separate and does not combine their times into a synthetic verdict.

## Deliverables

For each library `HexFoo` advancing through Phase 4:

1. **`HexFoo.Bench` exe** — for every compiled-track operation, rooted at
   `HexFoo/Bench.lean`, with helper modules under `HexFoo/Bench/` when useful.
   It registers every compiled operation in the library's SPEC API surface
   with `setup_benchmark` (parametric) or
   `setup_fixed_benchmark` (canonical input). The complexity
   expression in each `setup_benchmark` is the *textbook*
   complexity, not the observed one. Proof-track operations instead have
   named fresh-module probes and matched baselines under an explicit manifest
   `proof_probes` directory; those probes are not registrations.

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
   scientific settings used for real runs. Build-only proof probes extend the
   existing build job with structural/reduced build checks; they never become
   executable roots.

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
   cost; explain the dominant entries. Proof-track probes carry the external
   build evidence required by `SPEC/benchmarking.md` instead of a timed-region
   sampling profile.

7. **Headline report** at `reports/<lib>-performance.md` per
   [SPEC/benchmarking.md §Headline reports](../SPEC/benchmarking.md#headline-reports).
   Five subsections: Bench targets, Verdicts, Comparator ratios,
   Profile, Concerns. Every numeric claim cites the bench case
   name, command line, seed/parameter, JSONL path, profile
   location, and comparator source. Mixed libraries split every subsection by
   compiled versus proof/tactic evidence and state each proof-track replacement
   explicitly.

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

- every operation listed in the library's SPEC API surface is assigned to a
  track, every compiled-track operation has a `setup_benchmark` or
  `setup_fixed_benchmark` registration in the `HexFoo.Bench` exe, and every
  proof-track operation has the specified externally timed fresh-module probe;
- every parametric registration declares a complexity model that
  matches the SPEC's textbook complexity for that operation;
- every new or changed parametric registration has an adjacent
  cost-model derivation comment, and every PR that changes a
  `setup_benchmark` complexity declaration includes an independent
  cost-model derivation in the commit message that made the change;
- when a compiled track exists, `lake exe hexfoo_bench verify` succeeds under
  smoke settings, and
  `lake exe hexfoo_bench run NAME` returns *consistent with declared
  complexity* for every parametric registration at its scientific
  settings;
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
  one of the six enumerated reasons (`implementation-is-extern`,
  `structural-layer`, `input-source-only`, `mathlib-bridge`,
  `no-comparable-surface-in-named-comparator`,
  `correspondence-only-layer`). Missing declarations
  block Phase-4 completion;
- the [Attribution rule](../SPEC/benchmarking.md#the-attribution-rule)
  is satisfied: every dominant profiled cost maps to a registered
  bench target, or the per-library SPEC documents why the cost
  cannot be separated;
- a profile run per
  [SPEC/profiling.md §Coverage requirement](../SPEC/profiling.md#coverage-requirement)
  is recorded in `reports/<lib>-performance.md §Profile` for every compiled
  input family; proof-track surfaces instead record the required fresh-build
  samples and provenance;
- the headline report at `reports/<lib>-performance.md` exists with
  the five mandated subsections and full artefact traceability;
- the headline report's §Concerns subsection is empty. A library
  cannot **remain** at `done_through: 4` while any Concern is
  unresolved; the orchestrator rolls back if this state is detected.
  The only resolution available to the orchestrator is to act on
  the HO issue tied to the Concern until the underlying problem is
  fixed and the Concern entry is removed from the report.
- the compiled-track CI smoke step (`list` + `verify`) and every declared
  proof-probe structural/build smoke check run on every PR where their track
  exists.

If any of these fail, the right action is rollback per
[Conventions.md](Conventions.md), not a SPEC-text edit weakening
the criterion.

### Correspondence-only mathlib layers

The criteria above presuppose that the library advertises at least one
operation in one of the two evidence tracks. A **correspondence-only
mathlib layer** advertises zero: it is a `mathlib: true` library whose
API is correspondence statements alone, with no compiled operation and
no proof or tactic operation of its own.
[SPEC/benchmarking.md §Mathlib-free benches](../SPEC/benchmarking.md#mathlib-free-benches)
forbids it a `HexFooMathlib/Bench.lean`, a `HexFooMathlib/Bench/`
directory, and a `lean_exe *mathlib*_bench` entry, so it has no
compiled track, and owning no proof surface it has no proof track
either. For such a library Phase 4 is done when:

- the library's SPEC declares the external-comparator absence with the
  `correspondence-only-layer` reason from
  [SPEC/benchmarking.md §"Comparator naming"](../SPEC/benchmarking.md#comparator-naming),
  naming the computational performance owner or owners whose bench
  targets carry the evidence for the operations this layer transports;
- `libraries.yml[L]` declares no `phase4` block, and no headline report
  at `reports/<lib>-performance.md` is required, per
  [SPEC/benchmarking.md §Headline reports](../SPEC/benchmarking.md#headline-reports).
  A report committed before the layer was classified may stay as a
  historical artefact.

The deliverables, the compiled-track exit criteria, and the
empty-Concerns criterion do not apply; there is no track for them to
attach to.

The exemption is narrow, and every other `mathlib: true` library takes
ordinary track assignment per [§Evidence tracks](#evidence-tracks) in
whichever shape its SPEC declares: compiled-only, proof-only (an
elaboration or tactic surface evidenced by fresh-module probes, as with
HexRealRootsMathlib's `isolate_roots` term elaborator), or mixed. A
library declaring a `libraries.yml` `proof_probes` root is normally
outside the exemption, since those probes measure a proof surface it
owns; so is a library owning an executable reifier, certificate
checker, or tactic.

### Audit reset

As of the merge of the PR introducing the new exit criteria above
(profile coverage, headline report, gating-comparator wiring,
Attribution rule, empty-Concerns), every library currently at
`done_through ≥ 4` is re-evaluated under those criteria. The
re-evaluation is queued via a single umbrella `directive`
issue with a checkbox per library; per-library follow-on issues
are filed only when the audit identifies actual gaps. Libraries
already passing all new criteria stay at `done_through: 4`
unchanged.

Record completion by bumping `libraries.yml[L].done_through` to `4`.
