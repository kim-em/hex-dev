# Larger packed F₂ matrix frames

The optional packed F₂ route admits 131072 columns, 131072 known reducers and 4096 targets. The previous limits were 16384/16384/1024. Its conservative logical-work limit is 2³⁸ and its packing/scalar/word-visit limit is 2³⁴, previously 2³² and 2²⁸. Complete private bit rows, metadata, projected targets and the reusable sixteen-row table must fit the parent packed-byte allowance. Every accepted result has the exact portable rows, sugars and counters; unsupported or refused frames retain the reference continuation.

Leading-column validation has a fixed 16384-byte bitmap and initializes only `ceil(columns/8)` bytes. The field and monomial-order contracts are unchanged. These are ordinary F₂ polynomial rings, including squares; no Boolean quotient relations are added.

Baseline `804f6c96d43a`; candidate `b135e329b277`. Only the matching Lean admission guards and native matrix source change in the runtime manifest. Native compiler `clang version 21.1.8`, generated-C compiler `clang version 23.1.0` (SDK), compiler options, inputs and controls match.

## Matched observations

Each campaign leases one CPU, uses one algorithm thread and runs adjacent AB then BA pairs. All use degree scheduling, grevlex, batch size 1024, complete reduced output and explicit binary-pivot controls. Every completed sample, outlier, failure and RSS observation is retained. No unchanged repeat is included. These comparisons measure candidate production through final interreduction and output. Parsing, launch and initialization are included in process time; certificate generation, independent native verification and kernel checking are separate.

| Cohort | CPU | Process B/A | Family balanced B/A | Candidate B/A | Pair min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 76 | 0.983905 | 0.981831 | 0.955104 | 0.779258 / 0.990959 / 1.175736 | 88060 / 88636 |
| prime-control | 94 | 0.995656 | 0.995656 | 1.004910 | 0.848194 / 1.000224 / 1.176898 | 73720 / 74296 |
| hard-cyclic9-f2 | 11 | 0.704035 | 0.704035 | 0.703610 | 0.676299 / 0.704603 / 0.732908 | 461416 / 912532 |

All 100 processes complete, with 50 equal complete-basis pairs and identical logical statistics. Cyclic-9 over F₂ has process B/A 0.704035, a 29.6% reduction on these two pairs. Peak RSS rises from 461416 to 912532 KiB (1.98×). The additional private packing trades memory for elimination speed. The moderate F₂ and prime-control observations do not establish a broad speedup.

| Development family | F₂ process B/A | Prime-control process B/A |
|---|---:|---:|
| cyclic | 0.999212 | 1.008199 |
| kat | 0.979576 | 0.989224 |
| eco | 0.998779 | 0.998447 |
| noon | 0.943518 | 0.999710 |
| reimer | 0.983242 | 0.995807 |
| minrank | 0.976445 | 0.981473 |
| dense-quadratic | 0.982764 | 0.996946 |
| mq | 0.992246 | not in prime suite |

The Cyclic-9 focus addresses a public hard case with matrices beyond the former native geometry. It is reported separately from the development suites. These observations are not a completed fixed-corpus evaluation, a held-out result or an external-comparator leadership claim. Ratios from different implementation stages are not multiplied.

## Correctness and replay

All twelve Clang/GCC ASan/UBSan variants and all nine project gates pass, including the executable/theory build, 567 independent SymPy and 567 Singular reduced-basis comparisons, both 1134-case driver checks, native/portable comparisons, downstream kernel replay, axiom audits, benchmark verification, DAG, phase and release-manifest checks.

Conformance exercises each maximum dimension and its next value, nonempty rows at columns 65536 and 131072, shared targets, independent targets, malformed rows, large sugar labels and parent budget refusals. The logical-bound example attains 2³⁸; one extra entry exceeds it by 4098. Physical-bound examples have 2³⁴−2 and 2³⁴+1 visits. Both sides of the former physical boundary remain accepted. The portable models are also evaluated during the Lean build. No new axiom or `native_decide` is introduced.

Raw capsule `f4-wide-binary-b135e329b277.tar.xz`: SHA-256 `b4e7d02be620aa7f3baf946cf04e7d4a9cdb62723636f19e7881c35710303f22`. Source and check manifests, compiler inputs, collector programs, full logs, outputs and raw samples have individual SHA-256 bindings.

```bash
python3 scripts/bench/groebner_wide_report.py \
  --archive reports/bench-results/raw/f4-wide-binary-b135e329b277.tar.xz \
  --report reports/bench-results/hexgroebner-wide.md --check
```

Add `--current` when replaying against the measured runtime/check source snapshot. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
