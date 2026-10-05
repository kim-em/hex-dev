# Profiling

This document describes CPU profiling of compiled Lean benchmarks. It
complements [benchmarking.md](benchmarking.md): benchmarking checks declared
asymptotic complexity against observed scaling; profiling shows where the
time actually goes.

Profiling is a diagnostic tool, not a phase deliverable. Reach for it when a
verdict is unexpected, when a constant factor is surprising (for example,
far off an external comparator), or when a dominant cost might sit outside
any registered bench target. It applies to the Mathlib-free compiled track;
elaboration, tactic and kernel-checking costs are investigated with the
build-time tools described in
[benchmarking.md §Proof-probe example files](benchmarking.md#proof-probe-example-files).

## Why profile

A registered target measures the cost of the function it is registered
against. If a non-trivial cost sits inside a prep step, an inlined helper, or
an unmeasured allocation pattern, the bench harness cannot see it. A verdict
of "consistent with declared complexity" is asymptotic only; a profile tells
you whether the cost is landing where the algorithm says it should.

If the profile disagrees with what the per-library SPEC's complexity analysis
predicts, typically by showing a dominant cost in a function the SPEC does not
name as the algorithm's hot path, that is a finding. It routes through the
same issue path as a bench verdict mismatch (see
[Conventions.md](../PLAN/Conventions.md#bench-found-conformance-found-and-audit-found-issues)).

## Tooling

- **Sampling profiler:** [samply](https://github.com/mstange/samply)
  on macOS and Linux. Records a CPU profile at a configurable rate
  (1 kHz by default), then exposes a symbolication HTTP API.
- **Symbolication:** samply's symbolication API resolves PC
  addresses against the binary's debug info.
- **Lean name demangling:** Lean function names are mangled into
  C-style identifiers in the binary; demangling restores the
  original `Module.Namespace.fn` form. The current pipeline shells
  out to a small Lean program importing `Lean.Compiler.NameDemangling`.
  Once the upstream `lake profile` command
  ([leanprover/lean4 #12545](https://github.com/leanprover/lean4/issues/12545))
  lands in a Lean release the project pins to, the pipeline collapses to a
  single `lake profile <exe> -- <args>` invocation.

`lake exe foo_bench profile` filters samples to the bench thread during the
bench library's timed regions, the same monotonic-clock boundaries that
define the bench verdict's timing. Prep, autotune overhead between probes,
result hashing, and process exit are excluded by construction. The filtering
postprocessor emits a diagnostics block (calibration residual, total timed
duration, retained sample count, sensitivity check); treat a profile it flags
as low-confidence with suspicion and re-run with a longer per-probe duration.
Raw `*.json.gz` profiles are not committed.

## Reading a profile

Useful summaries, when writing up a finding:

- **Leaf cost by category:** Lean own code (the library's namespace), GMP
  (`__gmpn_*`, `__gmpz_*`), allocation (`malloc`, `free`, the platform
  allocator, kernel memory primitives), and Lean runtime (`lean_*`, refcount
  cold paths, closure dispatch, boxing).
- **Inclusive-cost ranking** of Lean functions in the library's namespace,
  with a sentence on why each dominant entry is dominant.
- **Context:** commit, hardware, sampling rate, input and parameter, seed,
  and command line, so someone else can reproduce it.

Profile shapes generalise across machines; absolute percentages do not. A
profile is a shape check, not a stopwatch: use the bench harness for timing.
