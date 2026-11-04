# Packed F₂ known-pivot projection

The four-row XOR table kernel improves the measured known-pivot workload. Full-system results are mixed; these observations establish neither an overall F4 speedup nor the fastest-open-source milestone. Issue #10987 remains open.

Projection visits known pivots in column order before target-pivot installation. Groups of four dense known pivots use sixteen exact XOR combinations. Triangular pivot decisions retain the sparse provider’s source charges, reduction counts and maximum source sugar even when combinations cancel. Sparse pivots interrupt groups. Ordinary F₂ polynomial semantics apply.

The opt-in binary provider keeps its 2^28 physical and 2^32 logical call bounds. Admission accounts for the actual dense groups; tests cover all 64 triangular four-pivot patterns and all sixteen incoming masks, sparse interruptions, payloads of all five private buffers and sharp physical/logical boundaries. Default binary policy is unchanged.

## Matched full-system observations

Baseline `e7360335bbe2`; tables `b1d9393103cf`. Each pass alternates adjacent AB/BA pairs on one leased CPU with one algorithm thread. The repeat is the sole unchanged repeat. F₂ uses binary pivots in both arms; prime controls disable them in both arms (p = 32003 and 2147483647). All use degree scheduling and grevlex. Every one of the 192 processes completed; all 96 paired complete reduced bases and every logical statistic agree. Candidate production yields unchecked candidates. Certification, independent verification and kernel replay are separate correctness gates, and are excluded from these timing ratios.

| Pass | CPU | Process B/A | Family balanced B/A | Candidate B/A | Min / median / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| f2-false | 75 | 0.996383 | 1.075661 | 0.715766 | 0.217665 / 0.925717 / 4.374768 | 79844 / 85904 |
| f2-false-repeat | 50 | 0.913920 | 0.941010 | 0.910674 | 0.614907 / 0.935713 / 1.327328 | 80092 / 88572 |
| prime-control | 71 | 1.051524 | 1.051524 | 1.010848 | 0.556405 / 0.984668 / 2.713491 | 69856 / 69460 |
| prime-control-repeat | 53 | 0.941348 | 0.941348 | 0.940070 | 0.421916 / 0.986332 / 1.822311 | 73264 / 74252 |

| Family | F₂ first / repeat process B/A | Prime first / repeat process B/A |
|---|---|---|
| cyclic | 1.156151 / 0.955962 | 0.940065 / 0.996055 |
| kat | 2.329707 / 0.883423 | 1.005323 / 0.795399 |
| eco | 1.023530 / 0.867352 | 0.973895 / 1.001419 |
| noon | 1.686243 / 1.138898 | 1.212427 / 0.864713 |
| reimer | 1.582791 / 0.892106 | 1.073825 / 0.984231 |
| minrank | 0.937344 / 0.999309 | 1.220709 / 0.925538 |
| dense-quadratic | 0.354255 / 1.016681 | 0.971759 / 1.048103 |
| mq | 0.733548 / 0.813138 | not in prime suite |

Startup outliers, host activity, all completed samples and RSS records are retained. The MQ family improves in both passes, while the family-balanced first pass regresses. The small opt-in suite is diagnostic, not the SPEC’s leadership acceptance suite.

## Known-pivot benchmark

Benchmark snapshot `294f219094cd` adds exactly three benchmark/registration files to the tested runtime. Both computation executables are byte-identical to the full-system snapshot. Native compiler Clang 21.1.8, generated-C toolchain Lean 4.35.0-rc3, native options and compiler digests match both full-system arms. Exact compiler, host and ISA context is in the manifests.

For n known rows in 2n columns, the leading block is the identity and tails are deterministic dense vectors. Each of n targets is the sum of the known rows plus a distinct free-column unit. The projected targets are therefore independently known. Preparation is excluded; validation, table construction, elimination, independent unit checks and complete row/sugar/counter hashing are included. The sparse comparison uses the reference provider with bounded native phases; it is not a fully portable executable.

One CPU lease (CPU 68), one thread, four-second inner targets, three fixed trial-major complexity trials and adjacent matched AB/BA comparisons. No below-signal flags occurred in matched samples.

| n | Packed / sparse time | Below-signal flags |
|---:|---:|---:|
| 64 | 0.336040 | 0 |
| 128 | 0.257067 | 0 |
| 256 | 0.168350 | 0 |
| 512 | 0.106311 | 0 |

Independent compiled checks also cover 64/65, 128/129, 256/257 and 512/513, including known rank, all independent target units, pivot flags, sugars and all eight counters. All complete benchmark result hashes agree between providers.

## Unselected eight-row experiment

Prototype `bf49419e9294` uses 256-row tables for at least eight known reducers and 512 targets. It passed all twelve sanitized native variants and all nine project gates, including triangular masks, exact private allocations and a measured incomplete-group column bound. The corrected conservative bound includes unsuccessful group searches and keeps the physical cap. The initial prototype was corrected before timing.

The first pass and sole unchanged repeat retain all 192 processes and 96 equal paired complete bases/statistics. No further unchanged full-system repeat is collected.

| Pass | Process B/A | Family balanced B/A | Min / median / max |
|---|---:|---:|---|
| f2-false | 0.984203 | 0.994836 | 0.600282 / 1.024268 / 1.327748 |
| f2-false-repeat | 0.906865 | 0.894559 | 0.144254 / 0.997351 / 1.365672 |
| prime-control | 0.999319 | 0.999319 | 0.381804 / 0.973398 / 3.902982 |
| prime-control-repeat | 1.063547 | 1.063547 | 0.272503 / 1.018040 / 4.183329 |

MQ10 process ratios are 1.083406 / 1.145937; candidate ratios 1.171336 / 1.141207. Both passes regress on that input. Aggregating three MQ sizes hides this regression. The experiment remains unselected; its implementation is retained only in the source capsule.

| n | Eight-row policy / four-row kernel time | Below-signal flags |
|---:|---:|---:|
| 64 | 1.039436 | 0 |
| 128 | 1.002665 | 0 |
| 256 | 0.955252 | 0 |
| 512 | 0.940972 | 2 |

Only n=512 selects eight-row tables in this kernel. Its modest decrease has two signal flags. No unchanged kernel repeat was taken. A shared-filesystem ENOSPC interrupted the separate driver audit after successful build/oracle gates. Those successes were recovered from their complete logs (durations unavailable); the interrupted driver and remaining gates were rerun successfully. Timings completed before the interruption and were not rerun because of it.

Raw capsule `f4-eight-gap-bf49419e9294.tar.xz`: SHA-256 `1d3297eaba6a6c928c33de2010d8a0ed3bd36c0def96bc0974981b93cdfaa5b5`.

## Verification and reproduction

The runtime snapshot passed all twelve Clang/GCC ASan/UBSan native variants and all nine project gates: build, independent oracles, driver checks, benchmark smoke, DAG, phase 4, release manifest, headers and line counts. Oracles compare 567 bases each with SymPy and Singular, with driver and downstream kernel replay/axiom checks in the retained logs. The later benchmark-only snapshot passed six benchmark/source gates and the independent compiled checks; its runtime/check source and computation ELF bindings are verified separately.

Raw capsules contain source/check blobs, per-file SHA-256 manifests, commands, all samples and retained failures. Frozen executables and perf data stay in the local measurement store; executable hashes are retained in the capsules.

- `f4-table-owned-b1d9393103cf.tar.xz`: SHA-256 `a6ef7d5744733a8861f13c3fe2212a086e271846630476d3335f479a45d42885`.
- `f4-projection-bench-294f219094cd.tar.xz`: SHA-256 `f625b68ae238aa8f78c23fd055a69f2745a77cc1576796385b1cea2e812d63df`.

```sh
python3 scripts/bench/groebner_tables_report.py \
  --archive reports/bench-results/raw/f4-table-owned-b1d9393103cf.tar.xz \
  --bench reports/bench-results/raw/f4-projection-bench-294f219094cd.tar.xz \
  --eight reports/bench-results/raw/f4-eight-gap-bf49419e9294.tar.xz \
  --report reports/bench-results/hexgroebner-tables.md --check --current
```
