# Reuse existing packed F₂ pivot rows

Packed F₂ elimination reads sparse pivot columns from the existing pivot row. It omits a temporary native pivot wrapper and its duplicate array entry for each installed pivot. The private bit rows and metadata, sparse/word/table projection choices, canonical output, immutable aliases and logical work counters are unchanged. Ordinary prime-field scans retain their native pivot wrappers.

Baseline `7812aa2db75b`; candidate `15b52d43cb71`. Only the native matrix elimination source changes in the runtime manifest. Native compiler `clang version 21.1.8`, generated-C compiler `clang version 23.1.0` (SDK), native flags and benchmark inputs match between arms.

## Matched full-system observations

Each sweep leases one CPU and uses one algorithm thread. Adjacent pairs alternate AB/BA. Every completed sample, outlier, failure and RSS observation is retained. The second pass is the sole unchanged repeat; no further unchanged repeat is collected. F₂ enables binary pivots in both arms; prime controls disable them at p = 32003 and 2147483647. All use degree scheduling, grevlex and complete reduced output.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 19 | 0.979981 | 0.976412 | 0.983147 | 0.776114 / 0.991007 / 1.196869 | 88016 / 88636 |
| f2-false-repeat | 60 | 0.979641 | 0.974486 | 0.990177 | 0.780389 / 0.994004 / 1.134344 | 88016 / 88636 |
| prime-control | 10 | 0.988173 | 0.988173 | 0.995960 | 0.765923 / 0.994417 / 1.145064 | 73656 / 74296 |
| prime-control-repeat | 69 | 0.990976 | 0.990976 | 0.998002 | 0.789235 / 0.995120 / 1.138520 | 73656 / 74296 |

All 192 processes completed. All 96 paired complete reduced bases and every logical statistic agree. The F₂ process ratios are 0.979981 and 0.979641; both passes show a modest reduction on this development suite. They do not establish performance leadership. Per-family differences, including small-system regressions, remain visible below. Candidate production returns unchecked candidates; certification, independent native verification and kernel checking are separate checks excluded from these timing ratios.

| Family | F₂ first / repeat process B/A | Prime first / repeat process B/A |
|---|---|---|
| cyclic | 1.004989 / 1.018093 | 0.992119 / 0.991630 |
| kat | 0.945395 / 0.934508 | 0.992994 / 0.988842 |
| eco | 1.000793 / 0.998011 | 1.000948 / 1.001262 |
| noon | 0.963798 / 0.948009 | 0.996569 / 0.986683 |
| reimer | 0.966112 / 0.961045 | 1.000552 / 0.999847 |
| minrank | 0.947761 / 0.965182 | 0.956334 / 0.974935 |
| dense-quadratic | 0.990098 / 0.973418 | 0.978481 / 0.993874 |
| mq | 0.994386 / 1.000537 | not in prime suite |

These diagnostic suites are development inputs, not the SPEC’s balanced, held-out leadership corpus. No fresh external-comparator result is inferred for this implementation, and ratios from separate stages are not multiplied.

## Correctness and replay

All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include 567 unique SymPy and 567 Singular reduced-basis comparisons, both 1134-case driver checks, native/portable comparisons, downstream kernel replay, axiom audits and bench verification.

The existing compiled conformance covers shared input snapshots, sparse and word updates, known-pivot projection, high pivot indices, malformed rows and exact budget/refusal boundaries. All native paths agree with their portable models. The change retains each row in the existing pivot array throughout the frame; sparse reads borrow that row without retaining another wrapper. Source/check manifests, complete logs, collector programs and every raw sample are bound by per-file SHA-256 hashes.

Raw capsule `f4-binary-pivot-headers-15b52d43cb71.tar.xz`: SHA-256 `d0ffac2364aba71402a8aa42ddb165be93fc7122cb93900da15f6c50206bdf93`.

```bash
python3 scripts/bench/groebner_pivot_report.py \
  --archive reports/bench-results/raw/f4-binary-pivot-headers-15b52d43cb71.tar.xz \
  --report reports/bench-results/hexgroebner-pivots.md --check
```

Add `--current` when replaying against the measured runtime/check source snapshot. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
