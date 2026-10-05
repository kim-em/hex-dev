# Ordered-function API regression observations

The question is whether the retained computational workloads slow down between
the last committed benchmark baseline and the API-polished candidate. The
baseline is `ee490f54889e2db8170c8b9fc6e8568f8a978bbe`; the candidate is
`a9a8997e470a996509940d035deebdc79db56a79`. The latter was subsequently rebased
without changing the OrderedFn patch. The measured candidate is retained on
[`issue-10575-evidence-orderedfn`](https://github.com/kim-em/hex-dev/tree/issue-10575-evidence-orderedfn).
Neither source is a published release.

## Method and provenance

[sources.json](sources.json) records clean source revisions, exact Lake lock
digests, Lean versions, frozen executable hashes and dynamic linkage. The baseline
was rebuilt in an isolated checkout with each historical package revision fetched
independently. Its executable hash exactly reproduces the retained
[`z3-final` binary hash](../../data/hex-ordered-fn/z3-final/context.json).
The original failed shared-object-store checkout attempts are retained in the
task artifacts; they produced no measurement.

All 17 retained workload families use their existing eight parameters and batch
targets. Three trial-major repetitions run adjacent baseline/candidate arms,
alternating AB/BA by trial, on one automatically leased CPU. There is no idle-core
preflight, sample rejection or retry. [schedule.json](schedule.json) and
[measure.py](measure.py) specify the full schedule; [context.json](context.json)
records host activity, affinity and final unchanged binary hashes.

The child rows’ `env.git_commit` and `git_dirty` describe the invocation working
directory, including for the historical executable. They are not the baseline’s
source identity. Use `sources.json` and the executable hash for that identity.
The baseline uses Lean 4.34.1; the candidate uses 4.35.0-rc3 and the current pins.
This is a comparison of whole pinned builds. It cannot causally attribute a
difference to this API patch or to one transitive dependency.

## Results

All 816 scheduled arms complete with status `ok`. Every adjacent pair agrees
on the result hash. [observations.jsonl](observations.jsonl), per-arm stdout/stderr
and [analysis.json](analysis.json) retain every result, including slower samples.

| Family | Median candidate/baseline time | Range of per-parameter median ratios |
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
capture. The constant-time degree probe is about 2% slower overall, and isolated
per-parameter medians reach about 8% for two nested scan probes. Individual arms
have wider variation; none is discarded. These observations do not establish
statistical equivalence, a universal absence of regressions, or a new complexity
pass. No acceptance threshold is selected after observing the data.

The comparison supplies actual computational evidence for the outstanding
Phase-6 review. The API PR advances only Phase 5. Final Phase-6 acceptance must
assess this evidence alongside the declaration review; smoke verification and
theorem timing cannot substitute for it. The Mathlib companion has no separate
computational benchmark surface.
