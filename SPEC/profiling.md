# Profiling

This document specifies the CPU-profiling contract for compiled
Lean benchmarks. It complements [benchmarking.md](benchmarking.md):
benchmarking checks declared asymptotic complexity against observed
scaling; profiling attributes the constant factor and surfaces
dominant costs that the registered bench targets do not measure.

A bench verdict of "consistent with declared complexity" is
asymptotic-only. A profile is what tells you whether the cost is
landing where the algorithm says it should — or whether 90% of the
time is being spent in a phase that no bench target ever timed.

## Why profile

Profiling exists because benchmark coverage is necessarily
incomplete: a registered target measures the cost of the function
it is registered against. If a non-trivial cost sits inside a
prep step, an inlined helper, or an unmeasured allocation pattern,
the bench harness cannot see it.

Profiling closes that gap by giving the author a flat list of
"where did the cycles go on this representative input." If the
flat list disagrees with what the per-library SPEC's complexity
analysis predicts — typically by showing a dominant cost in a
function that the SPEC does not name as the algorithm's hot path —
that is a finding, and it routes through the same audit-found
issue path as a bench verdict mismatch (see
[Conventions.md](../PLAN/Conventions.md)).

## Tooling

The current toolchain is:

- **Sampling profiler:** [samply](https://github.com/mstange/samply)
  on macOS and Linux. Records a CPU profile at a configurable rate
  (1 kHz is the default and is what this contract assumes), then
  exposes a symbolication HTTP API.
- **Symbolication:** samply's symbolication API resolves PC
  addresses against the binary's debug info.
- **Lean name demangling:** Lean function names are mangled into
  C-style identifiers in the binary; demangling restores the
  original `Module.Namespace.fn` form. The current pipeline shells
  out to a small Lean program importing `Lean.Compiler.NameDemangling`
  to perform the demangling. Once the upstream `lake profile`
  command (leanprover/lean4 #12545) lands in a Lean release the
  project pins to, this entire pipeline collapses to a single
  `lake profile <exe> -- <args>` invocation; until then the
  workflow is a small shell script chaining `samply record`,
  `samply load`, the symbolication API call, and the demangling
  step.

The profile's destination is a Firefox Profiler JSON, but the
headline report ([benchmarking.md §Headline reports](benchmarking.md#headline-reports))
records only an analytical summary; raw `*.json.gz` artefacts are
not committed.

## Coverage requirement

Profile **at least one representative case per
`phase4.input_families` entry** in `libraries.yml` for the library
being audited. Within the case-per-family minimum:

- Always profile the family that the per-library SPEC names as
  the downstream hot path. For HexLLL, that is the BZ
  recombination basis.
- Always profile the family with the worst measured comparator
  gap (per the headline report's Comparator-ratios subsection).
  These two may be the same family.
- The third (and any further) family is profiled at one
  representative case, sized large enough that the bench-harness
  startup cost is small compared to the algorithm's cost on that
  case.

One case per family is enough; the goal is shape-coverage, not
microbenchmarking. A profile is a coverage-and-shape check, not
a timing artefact.

## Required output

For each profiled case, the headline report's §Profile subsection
records:

- **Leaf cost categorisation.** The flat self-time budget split
  across:
  - **Lean own code** — functions in `Hex<Library>.*` and any
    helper modules under the library's own namespace;
  - **GMP big-integer arithmetic** — `__gmpn_*`, `__gmpz_*`;
  - **Allocation / free** — `malloc`, `free`, the platform's
    allocator (`nanov2_*`, `mi_*`, `tiny_*` on macOS), kernel
    memory primitives (`_platform_memset` etc.);
  - **Lean runtime** — `lean_*` functions, refcount cold paths,
    closure dispatch (`<apply/N>`), boxing (`mpz_to_int`).

  Percentages need not sum to exactly 100; the categories are
  exhaustive enough that ≥ 90% should be classified.

- **Inclusive-cost ranking** of Lean functions in the library's
  namespace. The top entries are the hot paths according to the
  profile.

- **Dominant-cost narrative.** For each entry in the inclusive-cost
  ranking that exceeds a clear share of total time (the threshold
  is interpretive, not numeric), a short paragraph explaining what
  that function is and why it is dominant. If a dominant cost is
  not attributable to a registered bench target, this is an
  audit-found issue per
  [benchmarking.md §Attribution rule](benchmarking.md#the-attribution-rule)
  and the §Concerns subsection links it.

## Reproducibility

The headline report's §Profile subsection records, for each
profiled case:

- the commit hash the binary was built from;
- hardware (architecture, CPU model, OS version);
- sampling rate (Hz);
- input family name and parameter (e.g. `random-bounded`, `n=160`);
- seed, where the input is randomised;
- exact command line invoked.

The raw `*.json.gz` artefact's developer-local path may be
recorded for reference but is not committed.

## Author's role

The author writing the headline report is interpretive. The
profile is data; the report's §Profile narrative is judgement
about whether the data matches what the algorithm should be
doing. Anything that doesn't match is filed as an audit-found
issue per
[Conventions.md §Bench-found, conformance-found, and audit-found
issues](../PLAN/Conventions.md#bench-found-conformance-found-and-audit-found-issues),
and the §Concerns subsection links it. The library cannot
**remain** at `done_through: 4` while any Concern is unresolved.

## Non-goals

- **Microbenchmark-grade timing precision.** A profile is a
  coverage-and-shape check, not a stopwatch. Use the bench
  harness for timing.
- **Cross-machine portability of percentages.** Profile shapes
  generalise; absolute percentages do not. The headline report
  records the hardware so a reader can read the percentages in
  context.
- **Production telemetry.** The profile is a Phase-4 audit step,
  not a continuous monitoring system.
