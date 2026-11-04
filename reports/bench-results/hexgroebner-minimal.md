# Local work accounting during minimal-basis selection

The read-only minimal-basis scan accumulates work locally and commits the exact successful or exhausted prefix once. It preserves the first representative of equal leading monomials and removes proper multiples. The same specialized helper preserves traced entries and untraced basis elements. It avoids updating the statistics/workspace records at every comparison; the O(n²) comparison count and divisibility checks are unchanged.

Baseline `8fbb55cf8788`; candidate `7812aa2db75b`. Only the reducer helper and the two F4 drivers change in the runtime manifest. Native compiler `clang version 21.1.8`, generated-C compiler `clang version 23.1.0` (SDK), native flags and benchmark inputs match between arms.

## Matched full-system observations

Each sweep leases one CPU and uses one algorithm thread. Adjacent pairs alternate AB/BA. Every completed sample, outlier, failure and RSS observation is retained. The second pass is the sole unchanged repeat; no further unchanged repeat is collected. F₂ enables binary pivots in both arms; prime controls disable them at p = 32003 and 2147483647. All use degree scheduling, grevlex and complete reduced output.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 10 | 1.005888 | 1.014318 | 1.021723 | 0.864151 / 0.987497 / 1.300374 | 88056 / 88064 |
| f2-false-repeat | 14 | 0.964756 | 0.961203 | 0.969480 | 0.760804 / 0.969217 / 1.253338 | 87972 / 88128 |
| prime-control | 17 | 0.991198 | 0.991198 | 0.992411 | 0.854045 / 0.979537 / 1.215959 | 73932 / 73724 |
| prime-control-repeat | 11 | 0.975265 | 0.975265 | 1.082728 | 0.391812 / 0.961225 / 2.402775 | 58232 / 57688 |

All 192 processes completed. All 96 paired complete reduced bases and every logical statistic agree. The F₂ process ratios are 1.005888 and 0.964756; these observations do not establish an overall gain or performance leadership. Per-family differences, including small-system regressions, remain visible below. Candidate production returns unchecked candidates; certification, independent native verification and kernel checking are separate checks excluded from these timing ratios.

| Family | F₂ first / repeat process B/A | Prime first / repeat process B/A |
|---|---|---|
| cyclic | 0.966026 / 0.859736 | 0.974958 / 0.952045 |
| kat | 1.067672 / 1.061744 | 0.994968 / 0.754252 |
| eco | 0.979425 / 0.868522 | 0.974014 / 0.960861 |
| noon | 1.060057 / 1.017518 | 0.996121 / 1.054870 |
| reimer | 1.040782 / 0.954409 | 0.981747 / 0.995871 |
| minrank | 1.020042 / 0.983167 | 1.028630 / 1.212734 |
| dense-quadratic | 1.013062 / 0.983159 | 0.988987 / 0.954674 |
| mq | 0.972864 / 0.979102 | not in prime suite |

These diagnostic suites are development inputs, not the SPEC’s balanced, held-out leadership corpus. No fresh external-comparator result is inferred for this implementation, and ratios from separate stages are not multiplied.

## Correctness and replay

All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include 567 unique SymPy and 567 Singular reduced-basis comparisons, both 1134-case driver checks, native/portable comparisons, downstream kernel replay, axiom audits and bench verification.

A hand-worked basis `[x²y,x,x²y,y]` requires eleven charged comparisons, costing 33 work units, and retains `x,y`. Conformance covers every exhaustion cut, nonzero initial work, duplicate ties, arbitrary carried labels, empty bases and unchanged monomial/scratch payloads. The same checks execute in the compiled native harness. The source/check manifests, full logs, collector programs and every raw sample are bound by per-file SHA-256 hashes. An initial freeze attempted before the commit completed was rejected before building; that diagnostic and the successful committed freeze are both retained.

Raw capsule `f4-minimal-work-7812aa2db75b.tar.xz`: SHA-256 `84c92da55aa96dc4d5e61b983507e3476d4424e8ccdab5bf2d8217cfb6d09e88`.

```bash
python3 scripts/bench/groebner_minimal_report.py \
  --archive reports/bench-results/raw/f4-minimal-work-7812aa2db75b.tar.xz \
  --report reports/bench-results/hexgroebner-minimal.md --check
```

Add `--current` when replaying against the measured runtime/check source snapshot. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
