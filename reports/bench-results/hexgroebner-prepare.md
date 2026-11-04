# Batched monomial preparation

The native product planner prepares independent monomials together, keeping their FNV accumulators in parallel while preserving exact hashes, collision comparisons, stable identifiers, output bytes and logical charges. Preparation reserves its full coordinate work before traversal. Scratch stays below 32 KiB, native work stays within 4096 units, and refusal preserves the input table for scalar continuation.

Baseline `294f219094cd`; candidate `3d6488148183`. The measured runtime delta is confined to `HexGroebner/ffi/monomial_hit.c`. Native compiler Clang 21.1.8, generated-C compiler SDK Clang 23.1.0, toolchain, native flags and benchmark inputs match between arms. Complete compiler identities and host context are retained in the capsule.

## Isolated kernels

CPU 81, one algorithm thread, four-second inner targets, three fixed trial-major complexity trials, then adjacent AB/BA matched samples. Preparation is excluded; product lookup, any insertion, validation and result hashing are included. The hit kernels consume complete support/workspace results; the insertion kernel also consumes every arena, metadata and index byte. Independently compiled checks validate all three functions against scalar results at ten sizes, including slice boundaries.

| Kernel | n | New / previous time | Below-signal flags |
|---|---:|---:|---:|
| monomialProducts | 256 | 0.699043 | 0 |
| monomialProducts | 1024 | 0.700656 | 0 |
| monomialProducts | 4096 | 0.685125 | 0 |
| productWide | 256 | 0.838175 | 0 |
| productWide | 1024 | 0.837535 | 0 |
| productWide | 4096 | 0.835797 | 0 |
| productMisses | 256 | 0.758680 | 0 |
| productMisses | 1024 | 0.750600 | 0 |
| productMisses | 4096 | 0.736844 | 0 |

`monomialProducts` uses three variables and existing products; `productWide` uses 22 variables and shorter adaptive slices. `productMisses` lacks the last product of each complete 64-term slice. These fixed workloads do not establish an equal full-system improvement.

## Full-system observations

Each pass alternates adjacent AB/BA pairs on one leased CPU, with one algorithm thread, degree scheduling, grevlex and complete reduced output. F₂ enables binary pivots in both arms; prime controls use p = 32003 and 2147483647 with binary pivots disabled. Every completed sample, outlier, failure and RSS observation is retained. The repeat is the sole unchanged repeat.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 54 | 0.990679 | 0.996293 | 0.979871 | 0.818380 / 0.987659 / 1.249521 | 85924 / 88088 |
| f2-false-repeat | 82 | 0.988887 | 0.990698 | 0.975351 | 0.838416 / 0.981804 / 1.232371 | 88060 / 88248 |
| prime-control | 86 | 1.001268 | 1.001268 | 0.905615 | 0.451853 / 1.022359 / 2.770582 | 73636 / 73748 |
| prime-control-repeat | 68 | 0.993634 | 0.993634 | 0.982795 | 0.855420 / 0.993226 / 1.207696 | 73720 / 73908 |

All 192 processes completed, with all 96 paired complete bases and every logical statistic equal. The full-system aggregates do not establish an overall gain or performance leadership. These small diagnostic suites do not satisfy the SPEC’s leadership acceptance suite. Candidate production returns unchecked candidates; certificate generation, independent native verification and kernel checking remain separate and are excluded from these timing ratios.

| Family | F₂ first / repeat B/A | Prime first / repeat B/A |
|---|---|---|
| cyclic | 0.972384 / 0.969090 | 0.969123 / 0.956866 |
| kat | 1.002252 / 0.999457 | 0.854446 / 1.006509 |
| eco | 1.010081 / 0.985910 | 1.056133 / 0.997288 |
| noon | 1.026958 / 1.016484 | 1.039662 / 0.998693 |
| reimer | 1.030467 / 0.995562 | 1.059794 / 0.975739 |
| minrank | 1.012600 / 1.002910 | 0.903087 / 1.020731 |
| dense-quadratic | 0.950137 / 0.975366 | 1.159385 / 1.000966 |
| mq | 0.968536 / 0.981676 | not in prime suite |

## Verification and reproduction

All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include 567 unique SymPy and 567 Singular reduced-basis comparisons, malformed inputs/certificates, overflow, work exhaustion, native/portable comparisons, downstream kernel replay and axiom audits. The native harness checks full product-table snapshots, aliases, collisions and refusal at the 4096-work boundary. The committed sources, check manifests, complete logs, inputs, raw samples and collector programs are bound by per-file SHA-256 hashes.

Raw capsule `f4-product-prepare-3d6488148183.tar.xz`: SHA-256 `12cb7f73af07e03336f1c3aeb3a4533f5668e0b678ebb9892c2c0172e258918d`.

```bash
python3 scripts/bench/groebner_prepare_report.py \
  --archive reports/bench-results/raw/f4-product-prepare-3d6488148183.tar.xz \
  --report reports/bench-results/hexgroebner-prepare.md --check --current
```

[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
