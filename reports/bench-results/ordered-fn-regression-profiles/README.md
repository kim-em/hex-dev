# OrderedFn guard-finding profiles

Question: do the retained slow points expose an unexpected computation path or
changed profile shape between the exact frozen builds? These operation-only
profiles diagnose that question; they do not override timing comparisons.

The [follow-up](../ordered-fn-regression-followup/README.md) flags four parameters.
The chosen cases are `height@2048`, `third@1024` and `approximation@12288`, with
one profile per frozen arm. `height@128` and `height@2048` run the same constant-work
sign algorithm; preparation constructs the large rational coefficient outside
the timed region. The decision and six capture manifests retain this scope.

The existing pipeline uses `perf record` at 999 Hz with user-space cycle events,
DWARF stacks and `CLOCK_MONOTONIC`; imports through samply; restores the clock
origin using exact agreement of every imported/raw sample timestamp; and filters
to the benchmark thread's actual `warm-loop` regions. Existing calibration,
minimum-sample and shifted-window sensitivity checks remain intact. No new
acceptance thresholds or quiet-core conditions were introduced.

| Case | Arm | Retained samples | GMP leaf % | Runtime leaf % | Allocation leaf % |
| --- | --- | ---: | ---: | ---: | ---: |
| height 2048 | baseline | 574 | 0.70 | 87.98 | 3.48 |
| height 2048 | candidate | 583 | 0.17 | 71.53 | 26.76 |
| third 1024 | baseline | 980 | 0 | 91.43 | 5.00 |
| third 1024 | candidate | 1021 | 0 | 89.03 | 6.37 |
| approximation 12288 | baseline | 4321 | 93.08 | 0.39 | 6.27 |
| approximation 12288 | candidate | 4335 | 92.76 | 0.18 | 6.78 |

All six filtered profiles pass the existing diagnostics. Clock-calibration
residuals are below one millisecond. Full leaf and inclusive rankings,
diagnostics, command lines, executable hashes, sampler identity, automatic CPU
selection and shared-host context are in the summaries and manifests. The
classification calls runtime allocation/free symbols allocation; its percentages
are sampled leaf shares, not allocation counts or comparable counts of objects.
Missing table categories denote zero classified samples in that category.

Approximation retains the expected GMP-dominated path in both builds. The
third-level sign scan spends most samples in `lean_dec_ref_cold`, with the actual
`Infinitesimal.sign`/`lowestIndex` path accounting for almost all inclusive work.
The tiny height query includes substantial runtime and benchmark-loop work:
baseline leaves include `lean_st_ref_take`, `lean_st_ref_set` and
`lean_dec_ref_cold`; candidate leaves include `lean_st_ref_take`,
`lean_st_ref_put`, `lean_dec_ref_cold` and `lean_free_object`.
The different leaf distribution is an investigative finding, not a demonstrated
increase in algorithmic allocations. Exact source comparisons show the
infinitesimal sign function's executable body and benchmark driver are unchanged;
the frozen builds use different Lean versions and pinned requirements. These
observations do not isolate the cause of the flagged timing changes.

## Failed capture and retained evidence

The initial six `samply record` attempts emitted zero samples, so the existing
filter rejected every capture. Their diagnostics and attempted commands are in
[failed-samply](failed-samply). A direct perf recording then supplied 609 samples,
and the existing perf-based pipeline produced the six usable filtered profiles
above. Failed captures remain retained; they were not converted into profile
passes. Profile-child timings are diagnostic context, not another unchanged
comparison run or substitute performance verdict.

Raw `perf.data`, samply JSON, filtered profiles, symbol tables and replay artifacts
remain locally under
`/home/kim/.codex/tasks/hex-10575/orderedfn-perf-profiles` and
`/home/kim/.codex/tasks/hex-10575/orderedfn-profile-findings`.
They are omitted from git as required by `SPEC/profiling.md`; manifests record
artifact hashes. [capture.py.txt](capture.py.txt) retains the driver using the
existing sampler and repository postprocessors. [tooling.json](tooling.json)
records those postprocessor hashes and observed tool versions.

The four timing findings remain unresolved. The next acceptance step needs an
explanation and resolution of those findings or an explicitly revised acceptance
contract; it cannot be another unchanged comparison, a pooled paired median,
theorem timing, or a profile treated as a timing pass. Neither library advances
beyond Phase 5 through these diagnostics.
