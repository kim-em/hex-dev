# Ordered-function API regression observations

The question is whether the retained computational workloads slow down between
the last committed benchmark baseline and the API-polished candidate. The
baseline is `ee490f54889e2db8170c8b9fc6e8568f8a978bbe`; the candidate is
`a9a8997e470a996509940d035deebdc79db56a79`. The latter was subsequently rebased
without changing the OrderedFn patch. The measured candidate is retained at
[its source commit](https://github.com/kim-em/hex-dev/tree/a9a8997e470a996509940d035deebdc79db56a79).
Neither source is a published release.

## Method and provenance

[sources.json](sources.json) records clean source revisions, exact Lake lock
digests, Lean versions, frozen executable hashes and dynamic linkage. The baseline
was rebuilt in an isolated checkout with each historical package revision fetched
independently. Its executable hash exactly reproduces the retained
[`z3-final` binary hash](../../data/hex-ordered-fn/z3-final/context.json).
The `z3-final` context records pre-merge head `45c3638`; the merged baseline
`ee490f5` has identical OrderedFn computational sources and benchmark driver.
The clean historical rebuild reproduces its executable hash.

All 17 retained workload families use their existing eight parameters and batch
targets. Three trial-major repetitions run adjacent baseline/candidate arms,
alternating AB/BA by trial, on one automatically leased CPU. Three trials give
two AB orders and one BA order; the design does not balance order effects.
There is no idle-core
preflight, sample rejection or retry. [schedule.json](schedule.json) and
[measure.py](measure.py) specify the full schedule; [context.json](context.json)
records host activity, affinity and final unchanged binary hashes. `measure.py`
is the frozen capture record, with original absolute checkout/executable paths;
it is not an installable benchmark driver. For fresh runs use the repository
benchmark tooling, with an explicit question and schedule.

The child rows’ `env.git_commit` and `git_dirty` describe the invocation working
directory, including for the historical executable. They are not the baseline’s
source identity. Use `sources.json` and the executable hash for that identity.
The first two rows record a clean invocation directory; the other 814 record
`git_dirty: true`. The dirty paths and concurrent build activity were not
inventoried, so this capture cannot identify that change or certify absence
of overlapping builds. This is a provenance limitation rather than evidence
that the measured executable changed. Host load is retained, and both frozen
executables remain unchanged. All rows retain the same invocation HEAD;
the capture script checks the frozen executable hash before every arm.

The baseline uses Lean 4.34.1; the candidate uses 4.35.0-rc3 and the current pins.
This is a comparison of whole pinned builds. It cannot causally attribute a
difference to this API patch or to one transitive dependency.

## Results

All 816 scheduled arms complete with status `ok`. Every adjacent pair agrees
on the result hash. Many workloads return sign-sized or parameter-invariant
hashes; agreement is a consistency check, not an independent semantic oracle.
[observations.jsonl](observations.jsonl), per-arm stdout/stderr
and [analysis.json](analysis.json) retain every result, including slower samples.

For each parameter and trial, divide candidate `per_call_nanos` by baseline
`per_call_nanos`. The family median pools all 24 ratios; the range spans the
eight parameter medians, each of three ratios.
[analyze.py](analyze.py) recomputes the statistics and verifies all raw stdout,
the complete ordered schedule, rounded README table, capture-script hash
and recorded before/after executable hashes. Run
`python3 reports/bench-results/ordered-fn-api-regression/analyze.py` to check
`analysis.json`, or add `--write` to regenerate that derived file without
running benchmarks.

| Family | Median of all 24 candidate/baseline ratios | Range of eight parameter medians |
| --- | ---: | ---: |
| `approximation` | 1.001 | 0.970–1.006 |
| `compareHeight` | 1.002 | 0.984–1.034 |
| `comparison` | 0.981 | 0.970–0.998 |
| `degree` | 1.022 | 1.003–1.039 |
| `denominators` | 0.982 | 0.979–1.005 |
| `height` | 1.012 | 0.997–1.032 |
| `horner` | 1.002 | 0.996–1.004 |
| `jointRefinement` | 1.003 | 0.998–1.059 |
| `provider` | 1.004 | 0.993–1.015 |
| `realHeight` | 0.999 | 0.985–1.005 |
| `refinement` | 1.002 | 0.999–1.015 |
| `scan` | 0.874 | 0.854–0.885 |
| `second` | 1.006 | 0.995–1.078 |
| `subtraction` | 0.970 | 0.946–1.012 |
| `successiveApproximation` | 1.003 | 0.984–1.022 |
| `third` | 1.007 | 0.995–1.079 |
| `thirdApproximation` | 0.999 | 0.995–1.023 |

Most family medians are near parity; the single-level scan is faster in this
capture. The constant-time degree probe is about 2% slower overall, and
per-parameter medians reach about 8% for two nested scan probes. In particular,
`second` at 16384 is the largest rung, so a size-dependent slowdown remains
unresolved rather than being dismissed as an isolated sample. Individual arms
have wider variation; none is discarded. These observations do not establish
statistical equivalence, a universal absence of regressions, or a new complexity
pass. No acceptance threshold is selected after observing the data.

These descriptive observations do not discharge the Phase-6 requirement to
pass a performance regression check. No predeclared acceptance rule accompanies
this capture. Final acceptance must consider every retained family and
parameter, including each largest rung. The largest-rung `second` point,
`third` at 4096, `jointRefinement` at 14336 and the degree family are illustrative
findings, not an exhaustive scope or a post-data pass/fail selection rule.
An explicit acceptance decision or focused investigation needs its comparison
rule and schedule declared before collection. A fresh capture must retain these original results
and follow the unchanged-rerun limit.

[The API change](https://github.com/kim-em/hex-dev/pull/10750) advances only
Phase 5. CI benchmark verification and theorem timing cannot substitute for
computational evidence. The Mathlib companion has no separate computational
benchmark surface.
