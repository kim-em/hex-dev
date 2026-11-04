# Precomputed source rows in monomial preparation

The native planner validates each source identifier and precomputes its row pointer before coordinate traversal. This removes repeated row-index multiplications from the inner loop. The private pointer array stays within the existing 32 KiB scratch bound. Exact hashes, collision comparisons, output bytes, work charges, overflow checks and atomic refusal are unchanged. The independently compiled digest checks use the preceding provider and validate every matched and complexity result of both arms against its successful scalar comparison.

Baseline `3d6488148183`; candidate `8fbb55cf8788`. The measured runtime delta is confined to `HexGroebner/ffi/monomial_hit.c`. Native compiler `clang version 21.1.8`, generated-C compiler `clang version 23.1.0` (SDK), toolchain, native flags and benchmark inputs match between arms. Complete compiler identities and host context are retained in the capsule.

## Isolated kernels

CPU 95, one algorithm thread, four-second inner targets, three fixed trial-major complexity trials, then adjacent AB/BA matched samples. Benchmark input setup (table interning and support construction) is excluded; monomial preparation, product lookup, any insertion, validation and result hashing are included. The hit kernels consume complete support/workspace results; the insertion kernel also consumes every arena, metadata and index byte. Independently compiled checks validate all three functions against scalar results at ten sizes, including slice boundaries.

| Kernel | n | New / previous time | Below-signal flags |
|---|---:|---:|---:|
| monomialProducts | 256 | 0.953363 | 0 |
| monomialProducts | 1024 | 0.948186 | 0 |
| monomialProducts | 4096 | 0.947723 | 0 |
| productWide | 256 | 0.866631 | 0 |
| productWide | 1024 | 0.856322 | 0 |
| productWide | 4096 | 0.867518 | 0 |
| productMisses | 256 | 0.960380 | 0 |
| productMisses | 1024 | 0.958747 | 0 |
| productMisses | 4096 | 0.963178 | 0 |

`monomialProducts` uses three variables and existing products; `productWide` uses 22 variables and shorter adaptive slices. `productMisses` lacks the last product of each complete 64-term slice. These fixed workloads do not establish an equal full-system improvement. All rows are prepared before lookup, so early refusal can discard the full preparation reservation, still within the 4096-work call bound. The last-term insertion kernel does not measure early-refusal performance.

## Full-system observations

Each pass alternates adjacent AB/BA pairs on one leased CPU, with one algorithm thread, degree scheduling, grevlex and complete reduced output. F₂ enables binary pivots in both arms; prime controls use p = 32003 and 2147483647 with binary pivots disabled. Every completed sample, outlier, failure and RSS observation is retained. The repeat is the sole unchanged repeat.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 87 | 0.989349 | 0.987363 | 0.994939 | 0.810852 / 0.992557 / 1.244311 | 88008 / 87972 |
| f2-false-repeat | 80 | 0.998143 | 1.001898 | 1.003078 | 0.848609 / 0.997033 / 1.220310 | 88008 / 87972 |
| prime-control | 3 | 0.995755 | 0.995755 | 0.998306 | 0.832175 / 0.997883 / 1.191960 | 73624 / 73632 |
| prime-control-repeat | 87 | 0.999172 | 0.999172 | 1.000575 | 0.860525 / 0.998143 / 1.185709 | 73624 / 73632 |

All 192 processes completed, with all 96 paired complete bases and every logical statistic equal. The full-system aggregates do not establish an overall gain or performance leadership. These small diagnostic suites do not satisfy the SPEC’s leadership acceptance suite. Candidate production returns unchecked candidates; certificate generation, independent native verification and kernel checking remain separate and are excluded from these timing ratios.

| Family | F₂ first / repeat B/A | Prime first / repeat B/A |
|---|---|---|
| cyclic | 0.992557 / 1.004089 | 0.997736 / 0.997654 |
| kat | 0.955665 / 1.019262 | 0.997814 / 1.000070 |
| eco | 0.995516 / 1.000330 | 0.992253 / 0.996233 |
| noon | 1.032829 / 1.017627 | 0.984915 / 1.012166 |
| reimer | 0.972314 / 0.963161 | 0.991816 / 0.997305 |
| minrank | 0.920900 / 1.029608 | 0.995992 / 0.998480 |
| dense-quadratic | 1.037089 / 0.999439 | 1.009935 / 0.992408 |
| mq | 0.997333 / 0.983264 | not in prime suite |

## Verification and reproduction

All twelve Clang/GCC ASan/UBSan variants and all nine project checks passed. The checks include 567 unique SymPy and 567 Singular reduced-basis comparisons, malformed inputs/certificates, overflow, work exhaustion, native/portable comparisons, downstream kernel replay and axiom audits. The native harness checks full product-table snapshots, aliases, collisions and refusal at the 4096-work boundary. The committed sources, check manifests, complete logs, inputs, raw samples and collector programs are bound by per-file SHA-256 hashes.

Raw capsule `f4-product-pointers-8fbb55cf8788.tar.xz`: SHA-256 `ef211422fe9142644b5411e737c0042c98ecb459ec509875c3cf34cceaa59203`.

```bash
python3 scripts/bench/groebner_pointer_report.py \
  --archive reports/bench-results/raw/f4-product-pointers-8fbb55cf8788.tar.xz \
  --report reports/bench-results/hexgroebner-pointers.md --check --current
```

[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
