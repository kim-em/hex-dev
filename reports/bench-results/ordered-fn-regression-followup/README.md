# OrderedFn retained regression follow-up

This is the single unchanged full comparison following the unresolved original
capture. [decision.json](decision.json) states the question and rule before
collection. All 17 families, eight parameters per family, three trial-major
adjacent AB/BA trials and 816 completed arms are retained, including raw stdout,
stderr, host context, schedule and frozen source/binary identities. The existing
measurement script is byte-identical to the original capture.

The existing pinned lean-bench default compares each arm's median and flags
strictly greater than 10% change. This arithmetic differs from the median of
adjacent-pair ratios reported by the original descriptive analysis. The child
outputs do not include runner signal-floor/verdict eligibility, so the analysis
applies the median arithmetic to every scheduled successful observation; it is
not a replay of those runner eligibility checks.

| Capture | Completed arms | Failed arms | Compared parameters | Flagged regressions | Flagged improvements |
| --- | ---: | ---: | ---: | ---: | ---: |
| [Original](../ordered-fn-api-regression/guard-analysis.json) | 816 | 0 | 136 | 1 | 8 |
| [Follow-up](guard-analysis.json) | 816 | 0 | 136 | 4 | 12 |

The original `approximation@10240` finding was +16.85%; it is −0.34% here.
The follow-up flags `height@128` (+14.58%), `height@2048` (+17.63%),
`third@1024` (+12.92%) and `approximation@12288` (+14.20%). Adjacent-pair
medians are retained separately and do not replace the declared comparison.
The sets of flagged workload/parameter pairs are disjoint between captures.
For each follow-up flag, only one of its three adjacent ratios exceeds 1.10:
`height@128` 1.365, `height@2048` 1.238, `third@1024` 1.129 and
`approximation@12288` 1.142. Their paired medians range from 1.019 to 1.047;
those observations do not replace the declared independent-arm median rule.
The symmetric rule also flags eight improvements in the original capture and
12 in the follow-up: all eight `scan` parameters in each, plus follow-up
`horner@20480`, `horner@24576`, `degree@16384` and `subtraction@128`.
No causal interpretation or performance pass follows from those improvement flags.

All 408 adjacent result hashes agree; these small hashes are consistency checks,
not exact semantic oracles.

Both frozen executable hashes are unchanged. Every follow-up child records the
clean invocation checkout `79b991882a486a8c8d05fd26aaf1656358834b7e`, preserved by
`audit/issue-10575-orderedfn-review`; that is
invocation metadata. The executable provenance remains the exact historical
and candidate source/toolchain identities in [sources.json](sources.json).
The entire shared-host record remains retained. No sample was discarded,
no quiet-core condition was imposed, and no further unchanged comparison is
permitted by this investigation's decision.

Recompute the stored median comparison without running a benchmark:

```bash
python3 reports/bench-results/ordered-fn-regression-followup/analyze_guard.py \
  reports/bench-results/ordered-fn-regression-followup --output /tmp/orderedfn-guard.json
```

Exit status **2** is expected because four regressions remain. The command checks
all raw observations, complete schedule, script hash, recorded final executable
hashes and pair hashes before emitting its findings. It does not assert a
performance pass. The same analyzer can check the original capture, which also
returns 2 with one finding.

The [operation-only profile investigation](../ordered-fn-regression-profiles/README.md)
retains successful diagnostics and failed sampling attempts. Profiles describe
computational shape and do not erase the timing findings. **Phase 6 remains
unattested.** No phase counters or publication eligibility changed.
