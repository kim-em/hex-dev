# Larger bounded ordinary prime-field matrix frames

This unselected experiment expands ordinary native elimination to 16384 columns, 16384 known reducers, 1024 targets and 2²⁸ charged scalar work. The former limits were 4096 columns, 1024 reducers, 64 targets and 2²⁰ work. The exact portable result, logical counters, ownership, parent budgets and refusal/fallback contracts are unchanged. Packed F₂ retains its separate 2³² logical and 2²⁸ physical-work bounds. The production limits remain unchanged because the matched observations do not show a gain.

Baseline `7812aa2db75b`; candidate `9d150346fe62`. Only the Lean admission limits and their C implementation change in the runtime manifest. Native compiler `clang version 21.1.8`, generated-C compiler `clang version 23.1.0` (SDK), native flags and benchmark inputs match between arms.

## Matched full-system observations

Each sweep leases one CPU and uses one algorithm thread. Adjacent pairs alternate AB/BA. Every completed sample, outlier, failure and RSS observation is retained. The second pass is the sole unchanged repeat; no further unchanged repeat is collected. F₂ enables binary pivots in both arms; prime controls disable them at p = 32003 and 2147483647. All use degree scheduling, grevlex and complete reduced output.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 43 | 1.034778 | 1.041396 | 1.032045 | 0.873995 / 1.014046 / 1.355967 | 88060 / 88084 |
| f2-false-repeat | 76 | 1.015082 | 1.017738 | 1.004418 | 0.825469 / 1.008777 / 1.304145 | 87996 / 88084 |
| prime-control | 43 | 1.001859 | 1.001859 | 0.979988 | 0.538170 / 1.035653 / 1.321222 | 71568 / 69648 |
| prime-control-repeat | 18 | 1.004425 | 1.004425 | 0.993647 | 0.887246 / 0.998498 / 1.234758 | 73636 / 69648 |

All 192 processes completed. All 96 paired complete reduced bases and every logical statistic agree. The F₂ process ratios are 1.034778 and 1.015082; these observations do not establish an overall gain or performance leadership. Per-family differences, including small-system regressions, remain visible below. Candidate production returns unchecked candidates; certification, independent native verification and kernel checking are separate checks excluded from these timing ratios.

| Family | F₂ first / repeat process B/A | Prime first / repeat process B/A |
|---|---|---|
| cyclic | 1.003304 / 1.004217 | 0.871351 / 0.990177 |
| kat | 1.106889 / 1.016290 | 0.975270 / 1.003431 |
| eco | 1.005761 / 0.985280 | 1.046087 / 0.993341 |
| noon | 1.078094 / 1.049520 | 0.960417 / 1.010200 |
| reimer | 1.048387 / 1.034554 | 1.118674 / 0.991390 |
| minrank | 1.057242 / 1.026128 | 1.018485 / 1.038167 |
| dense-quadratic | 1.027471 / 1.022764 | 1.041456 / 1.005088 |
| mq | 1.008727 / 1.004526 | not in prime suite |

These diagnostic suites are development inputs, not the SPEC’s balanced, held-out leadership corpus. No fresh external-comparator result is inferred for this implementation, and ratios from separate stages are not multiplied.

## Correctness and replay

All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include 567 unique SymPy and 567 Singular reduced-basis comparisons, both 1134-case driver checks, native/portable comparisons, downstream kernel replay, axiom audits and bench verification.

Conformance checks both sides of each size cap, adjacent conservative-work bounds 2²⁸ and 2²⁸+1, ordinary F₂ and odd-characteristic frames above the former column limit, nonempty dense preparation beyond the former work quantum, and exact aliases/counters. The 66-input dense F4 fixture must enter a whole frame; a 1025-input variant must exercise dense continuation updates. A separate 1025-input F₇ example checks successful continuation reductions, zero rows and non-unit inverses. Earlier failed attempts with obsolete old-cap route assertions are retained as diagnostics; the final complete test suite requires both newly admitted frames and continuation coverage. The driver gate was replayed with an isolated output file after an outer runner log collided with the gate log; both the original log and the complete isolated replay are retained, and the final gate record binds the isolated replay.

Raw capsule `f4-scalar-frames-9d150346fe62.tar.xz`: SHA-256 `1df3b5b252988364eeeefcadf2e4522809cd555242d7509e85dc9b05778f0b3d`.

```bash
python3 scripts/bench/groebner_frames_report.py \
  --archive reports/bench-results/raw/f4-scalar-frames-9d150346fe62.tar.xz \
  --report reports/bench-results/hexgroebner-frames.md --check
```

Add `--current` when replaying against the measured runtime/check source snapshot. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
