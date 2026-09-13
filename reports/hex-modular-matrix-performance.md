# Bounded modular determinant baseline

This report measures the ordinary bounded CRT determinant from milestones 1–2. It makes no Phase-4 completion or divisor-route speed claim. The structured family is slower than Bareiss at the completed common rungs; large modular calls reach the harness cap. Dixon and the determinant-divisor optimization are separate milestones.

These fixed registrations are external-comparator anchors, not an empirical complexity attestation or an absolute-budget gate. Elimination performs cubic word arithmetic per image; reconstruction needs enough images to exceed twice the row/column Hadamard bound.

## Inputs and timing protocol

- `structured-determinant`: the shared Bareiss salt-71 tridiagonal fixture at 16, 24, 32, 48, 64, 96, 128, 192, 256, 320, 384 and 512.
- `dense-random-determinant`: splitmix64 seed 10219, dimensions 32, 64, 96, 128, 192 and 256, with centered 8-, 64- and 1024-bit entries.
- `unimodular-determinant`: dense `I + u vᵀ`, with `u` all ones, `v` alternating ±2⁶⁴, and `vᵀu = 0`, so the determinant is one. Dimensions are 32, 64, 96, 128, 192 and 256. Negative determinant variants are covered by conformance.

The three arms receive identical matrices. Matrix construction and FLINT request encoding precede the timed closures. The modular arm includes bound computation, finite prime supply, elimination and CRT, and rejects any Bareiss fallback. The comparator is FLINT fmpz_mat_det via python-flint, using the shared persistent subprocess protocol; JSON parsing and result transport remain included.

Each arm has a discarded outer warmup, a discarded first invocation inside each child, and five fixed repeats with a 0.2-second auto-tuning floor. Adjacent modular/Bareiss/FLINT arms reverse order on alternate rungs. CPU placement uses a nonblocking lease on the shared host. Every completed export is retained; host load is recorded without filtering.

The initial run used one Lean worker. A blocking stderr reader prevented the harness timer from running, so its completed timings can exceed the configured ten-second cap. Relinking the executable interrupted the Bareiss and FLINT child launches at dimension 256. The incomplete dimension-320 comparison was stopped before its combined export was written; its partial arm output is unavailable. The resumed run uses two workers on one CPU and an immutable executable copy; it repeats dimension 256 once and completes the remaining schedule. Both datasets are retained. A final collector check verifies per-arm checkpoints, so future interrupted comparisons preserve completed arms. Large determinant replies also exposed Python’s default 4300-digit conversion limit; the large-integers dataset repeats the affected dense 256/64 and 1024-bit range with `PYTHONINTMAXSTRDIGITS=0`. The original errors remain visible.

`Hex / FLINT` means modular median divided by the FLINT median minus that dataset’s empty-protocol median; lower is faster. Raw medians are in seconds. The parameter b is the dense signed-entry width or the unimodular power-of-two exponent; it is unused for the fixed structured fixture. `cap` denotes a killed child batch, including setup and warmup; it is not a lower bound on the timed call alone. Ratios are omitted if an arm lacks all five successful repeats. No partial sample is silently promoted to a complete comparison.

## hex-modular-matrix-baseline

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 40; Lean 4.34.0-rc2, python-flint 0.9.0. Protocol median: 39.508 µs.

Load before: `419.39 387.89 283.99 425/12297 175448`; after: `314.28 336.21 300.04 267/10890 327491`. [Complete exports and source fingerprints](data/hex-modular-matrix-baseline.json).

| Family | n | b | Modular s | Bareiss s | FLINT s | Hex / FLINT |
|---|---:|---:|---:|---:|---:|---:|
| structured | 16 | 8 | 0.0340557 | 8.2709e-05 | 0.000211803 | 197.66× |
| structured | 24 | 8 | 0.022775 | 0.000278921 | 0.000448972 | 55.62× |
| structured | 32 | 8 | 0.0258753 | 0.001114 | 0.000622747 | 44.36× |
| structured | 48 | 8 | 0.105181 | 0.00246266 | 0.00158481 | 68.07× |
| structured | 64 | 8 | 0.120864 | 0.00677576 | 0.00744138 | 16.33× |
| structured | 96 | 8 | 0.310843 | 0.0421114 | 0.0179408 | 17.36× |
| structured | 128 | 8 | 1.38703 | 0.0648592 | 0.017143 | 81.10× |
| structured | 192 | 8 | 6.16406 | 0.635648 | 0.0553479 | 111.45× |
| structured | 256 | 8 | 15.9141 | 0/5 ok | 0/5 ok | — |

## hex-modular-matrix-baseline-resumed

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 9; Lean 4.34.0-rc2, python-flint 0.9.0. Protocol median: 15.229 µs.

Load before: `427.75 384.26 327.59 314/12103 404149`; after: `87.02 150.39 207.29 81/6841 925948`. [Complete exports and source fingerprints](data/hex-modular-matrix-baseline-resumed.json).

| Family | n | b | Modular s | Bareiss s | FLINT s | Hex / FLINT |
|---|---:|---:|---:|---:|---:|---:|
| structured | 256 | 8 | cap (5/5) | 0.460472 | 0.0760702 | — |
| structured | 320 | 8 | cap (5/5) | 0.715601 | 0.15173 | — |
| structured | 384 | 8 | cap (5/5) | 1.19142 | 0.210234 | — |
| structured | 512 | 8 | cap (5/5) | 3.39919 | 0.506214 | — |
| dense | 32 | 8 | 0.0864626 | 0.00448519 | 0.00174484 | 49.99× |
| dense | 64 | 8 | 0.393772 | 0.061092 | 0.0066925 | 58.97× |
| dense | 96 | 8 | 1.82944 | 0.177723 | 0.0145456 | 125.90× |
| dense | 128 | 8 | 4.21446 | 0.501925 | 0.0267157 | 157.84× |
| dense | 192 | 8 | cap (5/5) | 2.29852 | 0.0665152 | — |
| dense | 256 | 8 | cap (5/5) | cap (5/5) | 0.190223 | — |
| dense | 32 | 64 | 0.426034 | 0.00816899 | 0.00316271 | 135.36× |
| dense | 64 | 64 | 2.12567 | 0.121894 | 0.0138926 | 153.18× |
| dense | 96 | 64 | cap (5/5) | 0.893124 | 0.0360511 | — |
| dense | 128 | 64 | cap (5/5) | 2.89318 | 0.0691064 | — |
| dense | 192 | 64 | cap (5/5) | cap (5/5) | 0.183214 | — |
| dense | 256 | 64 | cap (5/5) | cap (5/5) | 0/5 ok | — |
| dense | 32 | 1024 | cap (5/5) | 0.323869 | 0/5 ok | — |
| dense | 64 | 1024 | cap (5/5) | cap (5/5) | 0/5 ok | — |
| dense | 96 | 1024 | cap (5/5) | cap (5/5) | 0/5 ok | — |
| dense | 128 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | — |
| dense | 192 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | — |
| dense | 256 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | — |
| unimodular | 32 | 64 | 0.467682 | 0.0052717 | 0.00691427 | 67.79× |
| unimodular | 64 | 64 | 2.23055 | 0.0471314 | 0.0319924 | 69.75× |
| unimodular | 96 | 64 | cap (5/5) | 0.14216 | 0.109944 | — |
| unimodular | 128 | 64 | cap (5/5) | 0.342308 | 0.25236 | — |
| unimodular | 192 | 64 | cap (5/5) | 1.15739 | 0.984651 | — |
| unimodular | 256 | 64 | cap (5/5) | 2.51448 | 2.5387 | — |

## hex-modular-matrix-collector-check

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 50; Lean 4.34.0-rc2, python-flint 0.9.0. Protocol median: 11.074 µs.

Load before: `94.53 155.06 255.17 88/7483 781804`; after: `93.86 151.94 252.55 90/7483 784256`. [Complete exports and source fingerprints](data/hex-modular-matrix-collector-check.json).

| Family | n | b | Modular s | Bareiss s | FLINT s | Hex / FLINT |
|---|---:|---:|---:|---:|---:|---:|
| structured | 16 | 8 | 0.0144186 | 5.2471e-05 | 0.000131595 | 119.64× |

## hex-modular-matrix-large-integers

Host `chungus2`, AMD EPYC 9455 48-Core Processor, CPU 75; Lean 4.34.0-rc2, python-flint 0.9.0. Protocol median: 6.774 µs.

Load before: `37.96 66.72 52.34 30/6811 2951596`; after: `14.61 26.04 42.62 15/6888 3130637`. [Complete exports and source fingerprints](data/hex-modular-matrix-large-integers.json).

| Family | n | b | Modular s | Bareiss s | FLINT s | Hex / FLINT |
|---|---:|---:|---:|---:|---:|---:|
| dense | 256 | 64 | cap (5/5) | cap (5/5) | 0.200001 | — |
| dense | 32 | 1024 | 4/5 ok | 0.190938 | 0.135085 | — |
| dense | 64 | 1024 | cap (5/5) | cap (5/5) | 1.03037 | — |
| dense | 96 | 1024 | cap (5/5) | cap (5/5) | 2.98346 | — |
| dense | 128 | 1024 | cap (5/5) | cap (5/5) | 4.58511 | — |
| dense | 192 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | — |
| dense | 256 | 1024 | cap (5/5) | cap (5/5) | cap (5/5) | — |

## Attribution and verification

A diagnostic `perf` profile at structured dimension 128 attributes 18.75% of self samples to `lean_apply_2`, 8.75% to `lean_apply_1`, 6.26% to the row-add closure and 4.60% to array construction. Allocation, reference counting and submatrix construction are also visible. This supports focusing future optimization on specialization and buffer operations; it does not establish their achievable speedup. The unpinned profile is separate from the comparison. Its output reports 23 lost samples; no recorded samples were filtered.

[Profile summary](data/hex-modular-matrix-profile.txt), [profile invocation export](data/hex-modular-matrix-profile.json), and [small smoke-anchor calibration](data/hex-modular-matrix-smoke.json). The three CI anchors pin the complete determinant-result hashes. All completed common comparator results agree by complete-result hash; small, singular, composite-modulus, bad-prime and forced-fallback cases are also checked by the conformance suite and FLINT fixtures.

Reproduce with `lake build hexmodularmatrix_bench`, then `HEX_FLINT_BENCH_PYTHON=<python-with-flint> python3 scripts/bench/modmat_flint.py <output.json>`. Render retained datasets with `scripts/bench/modmat_report.py`.
