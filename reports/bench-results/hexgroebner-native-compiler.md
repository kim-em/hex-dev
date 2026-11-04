# Audited Groebner native compiler profile

The same runtime `8fbb55cf8788` is built with native `clang version 21.1.8` and `clang version 23.1.3`. Other native libraries retain `clang version 21.1.8` and generated C retains `clang version 23.1.0` (SDK). The effective target is generic x86-64, with no native-CPU tuning flag. This profile has a complete source-bound correctness audit; it does not establish an overall F₂ performance gain or leadership.

All 192 processes completed. All 96 paired complete reduced bases and every logical statistic agree. Each sweep leases one CPU, uses one algorithm thread, alternates adjacent AB/BA pairs and retains every completed sample, outlier, failure and RSS observation. The repeat is the sole unchanged repeat. Inputs use degree scheduling and grevlex. F₂ enables binary pivots in both arms; prime controls disable them at p = 32003 and 2147483647.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 9 | 0.990547 | 0.992916 | 0.932724 | 0.769418 / 0.971448 / 1.414732 | 87972 / 88032 |
| f2-false-repeat | 3 | 1.009237 | 1.021263 | 0.983079 | 0.855839 / 0.981381 / 1.372340 | 88420 / 87972 |
| prime-control | 24 | 0.889125 | 0.889125 | 0.929384 | 0.350998 / 0.943148 / 2.192156 | 65728 / 62404 |
| prime-control-repeat | 12 | 0.989189 | 0.989189 | 0.968865 | 0.837818 / 0.972983 / 1.275326 | 74080 / 73632 |

| Family | F₂ first / repeat B/A | Prime first / repeat B/A |
|---|---|---|
| cyclic | 0.978661 / 0.986370 | 0.905111 / 0.963916 |
| kat | 1.073879 / 1.117518 | 0.858353 / 0.985051 |
| eco | 0.961197 / 0.967072 | 1.067508 / 0.960769 |
| noon | 0.933140 / 1.046399 | 0.686643 / 1.002084 |
| reimer | 1.061588 / 1.036341 | 0.957480 / 0.976668 |
| minrank | 1.003682 / 1.074510 | 0.868902 / 1.030551 |
| dense-quadratic | 0.958680 / 0.989749 | 0.927191 / 1.007205 |
| mq | 0.981130 / 0.962528 | not in prime suite |

Candidate production returns unchecked candidates. Certificate generation, independent native verification and kernel checking remain separate and are excluded from timing. These development inputs are not the SPEC’s balanced, held-out leadership suite. This profile does not demonstrate a necessary language/runtime limitation. The library’s host-compiler default is unchanged; the native compiler remains explicitly configurable.

## Configuration and correctness audit

All twelve Clang/GCC ASan/UBSan variants cover the identical runtime/check source. All nine project gates also passed under the measured compiler configuration, including the independent basis oracles, both driver corpora, native/portable comparisons and downstream kernel replay. The audit verifies the compiler stamp and exact object hash of all five Groebner C objects after every gate. The driver executables match the frozen timed binaries after the complete audit; the collector asserts this identity at every gate.

An initial audit caught downstream builds reverting to the host compiler. Its failed object stamp check and complete logs are retained. The successful audit routes the five Groebner kernel sources through Clang 23 even when a downstream project selects the dependency’s default `cc`; other native sources keep Clang 21. Both routing wrappers, the Lake configuration, their hashes and all object/executable identity records are retained. No timing is inferred from these correctness runs.

Raw capsule `f4-pointers-clang23-audit-8fbb55cf8788.tar.xz`: SHA-256 `ab880170f515f6eb035dcb07d7dc1d533a2adf2d92bb6ea4da46bc603b1b2ec1`.

```bash
python3 scripts/bench/groebner_native_compiler_report.py \
  --archive reports/bench-results/raw/f4-pointers-clang23-audit-8fbb55cf8788.tar.xz \
  --report reports/bench-results/hexgroebner-native-compiler.md --check
```

[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
