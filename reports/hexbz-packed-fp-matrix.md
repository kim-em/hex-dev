# A packed finite-field matrix for Berlekamp's fixed space (issue #9132)

Issue #9128 replaced the prime planner's repeated full splitting with a bounded
degree-pattern scout, so the modular share of a factorization had to be
remeasured before any matrix specialization was justified. This page is that
remeasurement, and it is a **go**.

On `cyclo_phi385` the Berlekamp matrix and its kernel are **46.5% of total
factor time** and **97.2% of the selected prime's Berlekamp split**; on
`cyclo_phi128_x_phi165`, 45.7% and 93.2%; on `cyclo_phi64_x_phi105`, 32.3% and
88.6%. Issue #9132 asks for 25% of total factor time on a material row, or
40% of its selected-prime Berlekamp time. Three cyclotomic rows clear the first
bar and 18 of 24 rows clear the second.

Inside that share the cost is one stage. On `cyclo_phi385`, row addition is
311.179 ms of the 315.202 ms Gauss-Jordan run; pivot search is
6.412 us, the nullspace basis 1.014 ms, and the conversion of basis
vectors back to polynomials 7.291 us. Column construction and the two
representation conversions together are 8.583 ms.

A prototype packed representation -- one contiguous row-major buffer of machine
words with the modulus held in a register -- was measured against the generic
path on the same matrices in the same process, and checked entry for entry
against `Hex.Matrix.nullspace` on all 24 instances. It reduces `cyclo_phi385`'s
row reduction from 315.324 ms to 8.775 ms, a
**27.7x** speedup including the cost of packing, and projects a
**1.75x** end-to-end improvement on that row.

Every number here is reproducible from the committed record by the commands in
[Regeneration](#regeneration).

## Revision and protocol

- Source revision `7539be444dc7c920cd4838768632cd5ec09c6e59` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured
  2026-08-03. The host was shared with other work throughout, so absolute
  wall times are not comparable with the issue #9127 baseline taken on a quiet
  machine. Everything this page concludes from is a **ratio between variants
  measured back to back in one process on one pinned core**, which that sharing
  does not disturb; where absolute times are compared across sections, both the
  numerator and the denominator come from this one record.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- The driver pins itself to one idle logical CPU before spawning any service, so
  every measured descendant inherits that affinity. This run used CPU 1.
- Phase profile: one warm-up call, then 5 timed calls below one second and
  one otherwise. Scout and counterfactual prices: median of 3 calls, merged
  per candidate. Kernel attribution: median of 3 calls, merged field by field
  after asserting that the repeats agree on everything deterministic.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-phase-profile-7539be44-chungus2.json` | `286167b99665e99fc5cc3e22ae8dd914b5e3d7bb4715844a0b681663bae1d5c1` |

`hexbz_factor_service` SHA-256 `f552f4887f98defedf5310a1999b3c2239cb7008b4f9c0857c47bbfffacdfd36`.

## How the diagnostic works

`bench/HexBench/FactorService.lean` gains one entry, `--entry kernelProfile`. It
computes the production prime plan, then walks the fixed-space kernel at the
selected prime stage by stage, calling the production function each stage names:
the Frobenius power `X^p mod f`, the column-polynomial recurrence, the conversion
of those columns into `Hex.Matrix`, the diagonal decrement that forms `Q_f - I`,
Gauss-Jordan pivot search, row swap and scale, row addition, the nullspace basis,
and the conversion of basis vectors back to polynomials. Like the scout prices,
none of this is work the production cascade does: it repeats the modular work at
the already-selected prime, after the plan is computed.

Gauss-Jordan is the one place the diagnostic does not call the production
function verbatim. `Hex.Matrix.rowReduce`'s loop reports only its final
`RowEchelonData`, so `countedRowReduce` mirrors `rowReduceLoop` column for column
-- same pivot rule, same elimination order, same elementary operations from
`HexMatrix.Elementary` -- while marking the clock between stages. Marks are taken
once per pivot column rather than once per row operation, so the clock reads cost
`O(n)` rather than `O(n^2)`.

### Validation

- The counted mirror's rank, echelon form, and pivot columns agree with
  `Hex.Matrix.rowReduce` on **24 of 24** instances, and its wall time tracks the
  production row reduction: on `cyclo_phi385` 315.951 ms against
  315.324 ms, a ratio of 1.002.
- The transform-free mirror produces the same echelon form and pivot columns as
  the mirror that keeps the transform, on **24 of 24**.
- Each of the three packed variants reproduces `Hex.Matrix.nullspace`'s basis
  entry for entry, on **24 of 24**. A variant that was fast because it was
  wrong could not be reported as fast.
- The pre-existing checks are unchanged and still pass on the wider sample: the
  counted recombination mirror agrees with the production `factorTrace` on leaf
  count, selected prime, completed subset cardinalities, and returned factor
  degrees on **367 of 367** instances, and the scouted degree pattern agrees with
  the Berlekamp split on **144 of 144** candidates.

### Three measurement hazards

The first two were found by numbers that could not be true, and both would
silently corrupt any re-measurement that ignores them.

*Let-floating.* A pure `let` whose result is first used later is moved to that
use by the compiler, so a stage's cost lands in whichever later stage first
demands its value. Before this was handled, the Frobenius power, the column
polynomials, and the whole matrix construction all measured under 100 ns on a
240x240 matrix. Every stage result is now pushed into an `IO.Ref` before the next
clock read.

*Aliasing.* `Hex.Matrix`'s elementary operations update the flat backing buffer
in place only while the matrix is uniquely referenced. One shared
`fixedSpaceMatrix` handed to several variants makes every variant but the last
copy the whole matrix per row operation -- measured at 2.742 s against 304 ms for
the same run. Each timed consumer now gets its own freshly built matrix, and the
build is timed separately so the extra builds can be subtracted.

*The length index.* `Vector` operations take the length as a runtime argument,
and for this kernel that length is `m - Hex.Matrix.rowReduce_rank M`; demanding
it runs a second full row reduction. The diagnostic reads the basis out as an
`Array` before touching it. **Production does not pay this today**:
`berlekampSplit` measures 336.194 ms against `fixedSpaceKernelVectors`'
326.745 ms on `cyclo_phi385`, so the `Vector.map` in `fixedSpaceKernel`
costs 9.449 ms, not a second 315.324 ms reduction. It is a trap for
the implementation to avoid, not a bug to fix.

## The measurement threshold

`matrix + kernel` is the Berlekamp matrix construction plus the row reduction and
nullspace at the selected prime, timed adjacently in one process by the scout
section; `Berlekamp split` is a full `berlekampFactor` at the same prime, timed
in the same place. `total factor` is the phase profile's own total for the
production cascade. Planning overhead is already excluded: these are costs at the
*selected* prime, not costs of the walk.

| instance | matrix | prime | total factor | matrix + kernel | Berlekamp split | share of total | share of split |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32x32 | 29 | 80.419 ms | 1.582 ms | 3.628 ms | 2.0% | 43.6% |
| `sd5_shift1` | 32x32 | 29 | 68.920 ms | 2.293 ms | 3.738 ms | 3.3% | 61.3% |
| `sd5_shift2` | 32x32 | 29 | 72.762 ms | 2.284 ms | 5.265 ms | 3.1% | 43.4% |
| `sd4_x_sd4shift1` | 32x32 | 29 | 19.497 ms | 2.268 ms | 4.472 ms | 11.6% | 50.7% |
| `sd5_x_phi11` | 42x42 | 29 | 168.061 ms | 4.617 ms | 9.100 ms | 2.7% | 50.7% |
| `xpow48_minus1` | 48x48 | 11 | 19.072 ms | 743.513 us | 2.171 ms | 3.9% | 34.2% |
| `xpow105_minus1` | 105x105 | 17 | 74.120 ms | 4.930 ms | 10.007 ms | 6.7% | 49.3% |
| `xpow120_minus1` | 120x120 | 7 | 482.882 ms | 3.821 ms | 17.399 ms | 0.8% | 22.0% |
| `cyclo_phi179` | 178x178 | 3 | 74.388 ms | 13.994 ms | 14.833 ms | 18.8% | 94.3% |
| `cyclo_phi64_x_phi105` | 80x80 | 11 | 60.762 ms | 19.616 ms | 22.137 ms | 32.3% | 88.6% |
| `cyclo_phi128_x_phi165` | 144x144 | 7 | 198.625 ms | 90.702 ms | 97.278 ms | 45.7% | 93.2% |
| `cyclo_phi385` | 240x240 | 3 | 437.956 ms | 203.769 ms | 209.697 ms | 46.5% | 97.2% |
| `wilkinson_40` | 40x40 | 47 | 13.537 ms | 254.558 us | 1.894 ms | 1.9% | 13.4% |
| `wilkinson_48` | 48x48 | 61 | 25.353 ms | 371.091 us | 2.916 ms | 1.5% | 12.7% |
| `wilkinson_56` | 56x56 | 67 | 34.532 ms | 578.668 us | 4.475 ms | 1.7% | 12.9% |
| `chebyshev_T24` (control) | 24x24 | 5 | 510.767 us | 306.304 us | 346.283 us | 60.0% | 88.5% |
| `chebyshev_U24` (control) | 24x24 | 3 | 655.893 us | 248.779 us | 325.332 us | 37.9% | 76.5% |
| `legendre_P30` (control) | 30x30 | 67 | 9.354 ms | 1.756 ms | 2.403 ms | 18.8% | 73.1% |
| `legendre_P38` (control) | 38x38 | 79 | 4.589 ms | 3.562 ms | 3.801 ms | 77.6% | 93.7% |
| `cyclo_phi17` (control) | 16x16 | 3 | 127.629 us | 98.857 us | 101.421 us | 77.5% | 97.5% |
| `cyclo_phi41` (control) | 40x40 | 3 | 2.786 ms | 468.945 us | 711.054 us | 16.8% | 66.0% |
| `xpow24_minus1` (control) | 24x24 | 11 | 3.224 ms | 199.056 us | 628.662 us | 6.2% | 31.7% |
| `randprod_10` (control) | 20x20 | 7 | 792.034 us | 436.307 us | 549.254 us | 55.1% | 79.4% |
| `randprod_21` (control) | 24x24 | 17 | 1.710 ms | 1.019 ms | 1.235 ms | 59.6% | 82.4% |

9 of 24 rows clear the 25%-of-total bar and 18 of 24 clear the 40%-of-split bar.
Three of the four named cyclotomic rows clear the first; the fourth,
`cyclo_phi179` at 18.8%, clears the second at 94.3%.

The rows that clear neither are the three Wilkinson rows, `xpow120_minus1`, and
`xpow24_minus1`. The Wilkinson rows are a structural exception rather than a near
miss: their selected prime splits the image into linear factors, so `Q_f - I` is
the zero matrix, the rank is 0, and Gauss-Jordan performs **no row additions at
all**. Their Berlekamp time is the equal-degree splitting that follows the
kernel, not the kernel. No matrix representation can move them, and none should
be expected to. `xpow120_minus1` is the opposite case: 482.882 ms of which
recombination is the overwhelming majority, against a 120x120 matrix that costs
3.821 ms.

## Stage attribution

The seven attributions issue #9132 asks for. `conversion` is the cost of reading
the column polynomials into the generic `Hex.Matrix` representation and
`diagonal` the in-place decrement that forms `Q_f - I`; both are differences
between nested spans, because `berlekampMatrix` recomputes the Frobenius power
and the column polynomials before converting them and `fixedSpaceMatrix`
recomputes `berlekampMatrix` before decrementing. `basis` is the nullspace-basis
construction, measured within each execution as `Hex.Matrix.nullspace` less
`Hex.Matrix.rowReduce` on two separately built copies of the same matrix; a
leading minus marks the one row where that difference is below the noise floor of
two adjacent 130 ms stages. Small allocations are Lean's per-thread counter --
the runtime publishes counts, not bytes -- so peak residency is reported
separately as the process high-water mark from `/proc/self/status`.

| instance | column polys | conversion | diagonal | pivot search | swap + scale | row addition | basis | to polynomials | small allocs | peak RSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 1.174 ms | 20.741 us | 18.096 us | 793 ns | 36.734 us | 507.312 us | 30.515 us | 4.787 us | 31,866 | 59.6 MiB |
| `sd5_shift1` | 1.531 ms | 14.109 us | 19.930 us | 811 ns | 36.650 us | 1.034 ms | 45.597 us | 4.687 us | 62,044 | 59.8 MiB |
| `sd5_shift2` | 1.522 ms | 25.267 us | 17.787 us | 765 ns | 36.122 us | 1.033 ms | 39.719 us | 4.797 us | 62,818 | 60.0 MiB |
| `sd4_x_sd4shift1` | 1.534 ms | 19.019 us | 17.085 us | 851 ns | 36.334 us | 1.042 ms | 44.827 us | 4.587 us | 61,400 | 59.9 MiB |
| `sd5_x_phi11` | 2.736 ms | 20.761 us | 38.387 us | 1.162 us | 73.577 us | 2.730 ms | 76.444 us | 5.498 us | 166,053 | 60.3 MiB |
| `xpow48_minus1` | 451.790 us | 54.520 us | 35.153 us | 1.210 us | 89.671 us | 175.871 us | 53.910 us | 7.180 us | 18,071 | 60.6 MiB |
| `xpow105_minus1` | 3.173 ms | 218.073 us | 185.516 us | 2.756 us | 595.561 us | 1.580 ms | 217.191 us | 7.601 us | 142,211 | 62.0 MiB |
| `xpow120_minus1` | 1.956 ms | 331.132 us | 224.532 us | 3.014 us | 619.279 us | 1.278 ms | 444.899 us | 28.592 us | 127,473 | 62.4 MiB |
| `cyclo_phi179` | 2.410 ms | 719.947 us | 502.015 us | 4.599 us | 1.988 ms | 14.195 ms | 244.613 us | 3.756 us | 1,015,884 | 64.8 MiB |
| `cyclo_phi64_x_phi105` | 3.515 ms | 143.963 us | 111.456 us | 2.025 us | 373.063 us | 23.016 ms | 249.169 us | 4.156 us | 1,413,149 | 64.5 MiB |
| `cyclo_phi128_x_phi165` | 7.331 ms | 486.663 us | 439.012 us | 3.991 us | 1.336 ms | 129.945 ms | -290.441 us | 6.389 us | 7,725,927 | 64.5 MiB |
| `cyclo_phi385` | 6.329 ms | 1.291 ms | 962.556 us | 6.412 us | 3.984 ms | 311.179 ms | 1.014 ms | 7.291 us | 17,647,557 | 68.6 MiB |
| `wilkinson_40` | 74.851 us | 32.658 us | 31.967 us | 1.022 us | 0 ns | 0 ns | 40.701 us | 18.868 us | 1,810 | 68.6 MiB |
| `wilkinson_48` | 104.005 us | 48.092 us | 38.648 us | 1.191 us | 0 ns | 0 ns | 56.634 us | 26.569 us | 2,554 | 68.6 MiB |
| `wilkinson_56` | 142.922 us | 72.898 us | 48.532 us | 1.473 us | 0 ns | 0 ns | 75.963 us | 35.102 us | 3,426 | 68.6 MiB |
| `chebyshev_T24` (control) | 107.580 us | 12.498 us | 10.206 us | 580 ns | 36.904 us | 221.300 us | 6.901 us | 1.312 us | 14,709 | 68.6 MiB |
| `chebyshev_U24` (control) | 72.317 us | 12.137 us | 9.944 us | 591 ns | 34.884 us | 193.946 us | 14.032 us | 1.292 us | 13,180 | 68.6 MiB |
| `legendre_P30` (control) | 1.107 ms | 14.841 us | 15.683 us | 792 ns | 48.885 us | 706.570 us | 26.871 us | 2.023 us | 43,334 | 68.6 MiB |
| `legendre_P38` (control) | 2.247 ms | 23.313 us | 39.750 us | 973 ns | 91.850 us | 1.729 ms | 8.864 us | 1.442 us | 104,644 | 68.6 MiB |
| `cyclo_phi17` (control) | 26.389 us | 5.437 us | 5.027 us | 421 ns | 18.296 us | 72.889 us | 4.556 us | 661 ns | 5,139 | 68.6 MiB |
| `cyclo_phi41` (control) | 134.430 us | 40.850 us | 21.932 us | 1.020 us | 93.445 us | 330.384 us | 26.840 us | 1.793 us | 26,424 | 68.6 MiB |
| `xpow24_minus1` (control) | 135.621 us | 8.924 us | 10.595 us | 601 ns | 18.289 us | 29.102 us | 16.404 us | 3.325 us | 3,338 | 68.6 MiB |
| `randprod_10` (control) | 157.023 us | 8.943 us | 7.101 us | 461 ns | 23.409 us | 352.368 us | 14.822 us | 1.082 us | 21,354 | 68.6 MiB |
| `randprod_21` (control) | 546.080 us | 5.379 us | 16.283 us | 611 ns | 29.692 us | 615.582 us | 30.506 us | 1.703 us | 37,396 | 68.6 MiB |

Row addition is the whole cost. On `cyclo_phi385` it is 98.7% of the Gauss-Jordan
run and 95.2% of the fixed-space kernel; pivot search is 6.412 us, four
orders of magnitude below it, and the two conversions plus the basis and its
polynomial readback come to 3.276 ms against 311.179 ms. Column
construction -- 240 polynomial products and monic reductions -- is 6.329 ms and
becomes the kernel's largest remaining cost once row addition is specialized.

The row-addition counters explain the two shapes among the cyclotomic rows.
`cyclo_phi385` performs 17,948 row additions and skips 38,456 more on an
already-zero coefficient; `cyclo_phi179` performs only 1,114 and skips
30,038, which is why its 178x178 matrix costs less than
`cyclo_phi64_x_phi105`'s 80x80.

## What a packed representation buys

Three packed variants, all storing the matrix as one contiguous row-major buffer
and holding the modulus in a machine word:

* **packed word** -- `UInt64` entries, Barrett reciprocal;
* **packed half-word** -- `UInt32` entries, Barrett reciprocal. Faithful because
  `ZMod64.Bounds` caps the modulus at `2^31`, and on a 64-bit runtime
  `lean_box_uint32` is a tagged immediate while `lean_box_uint64` allocates;
* **packed half-word, division** -- the same `UInt32` storage with a hardware
  remainder instead of the reciprocal.

All three compute the rank and the full nullspace basis, and all three are
checked against `Hex.Matrix.nullspace`. `pack` is the cost of reading the generic
matrix into the buffer, and `speedup` is the production row reduction against
packing plus reducing.

| instance | generic, with transform | generic, echelon only | packed word | packed half-word | packed half-word, division | pack | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 554.362 us | 324.601 us | 34.400 us | 26.139 us | 25.137 us | 39.178 us | 8.5x |
| `sd5_shift1` | 1.113 ms | 606.119 us | 82.472 us | 51.346 us | 51.807 us | 38.987 us | 12.3x |
| `sd5_shift2` | 1.080 ms | 603.555 us | 85.728 us | 51.516 us | 52.137 us | 39.389 us | 11.9x |
| `sd4_x_sd4shift1` | 1.075 ms | 596.875 us | 85.297 us | 51.527 us | 51.567 us | 38.818 us | 11.9x |
| `sd5_x_phi11` | 2.837 ms | 1.535 ms | 233.686 us | 138.276 us | 137.263 us | 70.394 us | 13.6x |
| `xpow48_minus1` | 277.832 us | 221.749 us | 27.260 us | 25.428 us | 23.835 us | 93.689 us | 2.3x |
| `xpow105_minus1` | 2.109 ms | 1.560 ms | 156.251 us | 145.426 us | 143.142 us | 477.999 us | 3.4x |
| `xpow120_minus1` | 1.890 ms | 1.504 ms | 153.919 us | 140.839 us | 138.926 us | 630.886 us | 2.4x |
| `cyclo_phi179` | 16.151 ms | 9.570 ms | 714.579 us | 678.907 us | 672.938 us | 1.421 ms | 7.7x |
| `cyclo_phi64_x_phi105` | 23.395 ms | 12.224 ms | 1.600 ms | 971.640 us | 995.145 us | 269.068 us | 18.9x |
| `cyclo_phi128_x_phi165` | 130.389 ms | 65.881 ms | 8.015 ms | 4.830 ms | 4.908 ms | 925.783 us | 22.7x |
| `cyclo_phi385` | 315.324 ms | 159.168 ms | 11.917 ms | 8.775 ms | 8.747 ms | 2.628 ms | 27.7x |
| `wilkinson_40` | 40.850 us | 42.152 us | 6.139 us | 5.869 us | 4.076 us | 62.723 us | 0.6x |
| `wilkinson_48` | 57.996 us | 59.899 us | 6.509 us | 6.369 us | 5.568 us | 93.108 us | 0.6x |
| `wilkinson_56` | 80.409 us | 81.881 us | 8.442 us | 7.872 us | 7.321 us | 128.420 us | 0.6x |
| `chebyshev_T24` (control) | 254.697 us | 165.705 us | 18.417 us | 15.453 us | 14.762 us | 21.021 us | 7.0x |
| `chebyshev_U24` (control) | 219.024 us | 148.299 us | 16.414 us | 13.730 us | 12.469 us | 20.671 us | 6.4x |
| `legendre_P30` (control) | 749.512 us | 441.825 us | 43.705 us | 33.660 us | 32.869 us | 34.180 us | 11.0x |
| `legendre_P38` (control) | 1.804 ms | 1.033 ms | 91.005 us | 71.686 us | 70.905 us | 56.894 us | 14.0x |
| `cyclo_phi17` (control) | 86.057 us | 63.194 us | 8.122 us | 6.920 us | 6.019 us | 8.052 us | 5.7x |
| `cyclo_phi41` (control) | 409.026 us | 294.347 us | 31.847 us | 28.753 us | 27.451 us | 62.863 us | 4.5x |
| `xpow24_minus1` (control) | 49.773 us | 45.497 us | 6.960 us | 6.219 us | 5.539 us | 20.560 us | 1.9x |
| `randprod_10` (control) | 370.860 us | 222.179 us | 27.160 us | 18.487 us | 18.117 us | 13.490 us | 11.6x |
| `randprod_21` (control) | 639.429 us | 373.814 us | 47.551 us | 31.157 us | 31.106 us | 20.650 us | 12.3x |

The win decomposes cleanly on `cyclo_phi385`:

| step | time | factor |
|---|---:|---:|
| production `Hex.Matrix.rowReduce` | 315.324 ms | -- |
| drop the transform the nullspace never reads | 159.168 ms | 1.98x |
| contiguous words, modulus in a register | 11.917 ms | 13.36x |
| `UInt32` entries instead of `UInt64` | 8.775 ms | 1.36x |
| Barrett reciprocal instead of hardware remainder | 8.747 ms | 1.00x |

Two of these deserve comment.

**The transform is half the elementary-operation work, and it is dead.**
`Hex.Matrix.rowReduce` maintains an `n x n` transform `T` with `T * M = echelon`
in lockstep with the echelon form, applying every swap, scale, and row addition
twice. `Hex.Matrix.nullspace` reads only `rank`, `echelon`, and `pivotCols`. That
factor of 1.98 is available without any change of representation.

**A Barrett reciprocal is not worth carrying.** Against a hardware remainder it
is 1.00x on `cyclo_phi385` and slower on 19 of the 24 rows. What
matters is holding the modulus as a machine word in the loop rather than reaching
it through `ZMod64.mul`, whose `@[extern]` contract takes the modulus as a boxed
`Nat` and converts it on every multiply.

Allocation follows the same shape:

| instance | generic with transform | generic echelon only | packed word | packed half-word |
|---|---:|---:|---:|---:|
| `sd5` | 31,866 | 17,591 | 3,842 | 1,466 |
| `sd5_shift1` | 62,044 | 32,793 | 10,540 | 1,232 |
| `sd5_shift2` | 62,818 | 33,183 | 10,701 | 1,226 |
| `sd4_x_sd4shift1` | 61,400 | 32,469 | 10,466 | 1,237 |
| `sd5_x_phi11` | 166,053 | 86,460 | 28,596 | 2,064 |
| `xpow48_minus1` | 18,071 | 13,028 | 4,001 | 3,867 |
| `xpow105_minus1` | 142,211 | 95,903 | 21,374 | 20,842 |
| `xpow120_minus1` | 127,473 | 89,910 | 24,895 | 24,501 |
| `cyclo_phi179` | 1,015,884 | 587,969 | 65,246 | 62,627 |
| `cyclo_phi64_x_phi105` | 1,413,149 | 723,226 | 163,862 | 8,060 |
| `cyclo_phi128_x_phi165` | 7,725,927 | 3,919,428 | 732,416 | 27,764 |
| `cyclo_phi385` | 17,647,557 | 8,975,874 | 672,203 | 97,269 |
| `wilkinson_40` | 1,810 | 1,807 | 1,777 | 1,777 |
| `wilkinson_48` | 2,554 | 2,551 | 2,513 | 2,513 |
| `wilkinson_56` | 3,426 | 3,423 | 3,377 | 3,377 |
| `chebyshev_T24` (control) | 14,709 | 8,826 | 1,587 | 1,081 |
| `chebyshev_U24` (control) | 13,180 | 7,993 | 1,455 | 1,071 |
| `legendre_P30` (control) | 43,334 | 23,741 | 4,509 | 1,412 |
| `legendre_P38` (control) | 104,644 | 56,191 | 8,966 | 2,323 |
| `cyclo_phi17` (control) | 5,139 | 3,296 | 650 | 527 |
| `cyclo_phi41` (control) | 26,424 | 17,021 | 3,363 | 3,077 |
| `xpow24_minus1` (control) | 3,338 | 2,543 | 986 | 942 |
| `randprod_10` (control) | 21,354 | 11,711 | 2,932 | 584 |
| `randprod_21` (control) | 37,396 | 20,041 | 5,850 | 744 |

`cyclo_phi385` goes from 17,647,557 small allocations to 97,269, a factor of
181. Peak resident set stays between 59.6 and 68.6 MiB throughout and is not a
constraint on any row.

## Projected end to end

Applying each row's measured packed ratio to its in-cascade row reduction, and
leaving the Berlekamp matrix construction unchanged:

| instance | total factor now | matrix + kernel now | matrix + kernel packed | projected total | projected gain |
|---|---:|---:|---:|---:|---:|
| `sd5` | 80.419 ms | 1.582 ms | 1.279 ms | 80.116 ms | 1.00x |
| `sd5_shift1` | 68.920 ms | 2.293 ms | 1.645 ms | 68.272 ms | 1.01x |
| `sd5_shift2` | 72.762 ms | 2.284 ms | 1.645 ms | 72.122 ms | 1.01x |
| `sd4_x_sd4shift1` | 19.497 ms | 2.268 ms | 1.646 ms | 18.876 ms | 1.03x |
| `sd5_x_phi11` | 168.061 ms | 4.617 ms | 2.936 ms | 166.380 ms | 1.01x |
| `xpow48_minus1` | 19.072 ms | 743.513 us | 629.130 us | 18.957 ms | 1.01x |
| `xpow105_minus1` | 74.120 ms | 4.930 ms | 3.983 ms | 73.172 ms | 1.01x |
| `xpow120_minus1` | 482.882 ms | 3.821 ms | 3.050 ms | 482.111 ms | 1.00x |
| `cyclo_phi179` | 74.388 ms | 13.994 ms | 4.969 ms | 65.363 ms | 1.14x |
| `cyclo_phi64_x_phi105` | 60.762 ms | 19.616 ms | 4.627 ms | 45.772 ms | 1.33x |
| `cyclo_phi128_x_phi165` | 198.625 ms | 90.702 ms | 11.867 ms | 119.790 ms | 1.66x |
| `cyclo_phi385` | 437.956 ms | 203.769 ms | 15.626 ms | 249.813 ms | 1.75x |
| `wilkinson_40` | 13.537 ms | 254.558 us | 276.329 us | 13.559 ms | 1.00x |
| `wilkinson_48` | 25.353 ms | 371.091 us | 414.492 us | 25.396 ms | 1.00x |
| `wilkinson_56` | 34.532 ms | 578.668 us | 635.518 us | 34.589 ms | 1.00x |
| `chebyshev_T24` (control) | 510.767 us | 306.304 us | 157.515 us | 361.978 us | 1.41x |
| `chebyshev_U24` (control) | 655.893 us | 248.779 us | 119.651 us | 526.765 us | 1.25x |
| `legendre_P30` (control) | 9.354 ms | 1.756 ms | 1.283 ms | 8.881 ms | 1.05x |
| `legendre_P38` (control) | 4.589 ms | 3.562 ms | 2.542 ms | 3.570 ms | 1.29x |
| `cyclo_phi17` (control) | 127.629 us | 98.857 us | 49.213 us | 77.985 us | 1.64x |
| `cyclo_phi41` (control) | 2.786 ms | 468.945 us | 258.293 us | 2.575 ms | 1.08x |
| `xpow24_minus1` (control) | 3.224 ms | 199.056 us | 182.325 us | 3.207 ms | 1.01x |
| `randprod_10` (control) | 792.034 us | 436.307 us | 199.699 us | 555.426 us | 1.43x |
| `randprod_21` (control) | 1.710 ms | 1.019 ms | 626.254 us | 1.318 ms | 1.30x |

The four named cyclotomic rows gain 1.14x to 1.75x. Nothing regresses
materially: the worst case is `wilkinson_40`, where a rank-0 or nearly-trivial
reduction still pays to be packed, and even there the overhead is 0.20% of that
row's total factor time. A production implementation removes it entirely by
building the packed matrix directly from the column polynomials instead of
converting an already-built generic one.

## Verdict, and the design it implies

**Go.** The threshold is met with room to spare, and the ceiling is large enough to
matter end to end.

The measurements narrow the design considerably from the issue's sketch.

1. **Build the packed matrix from the column polynomials, not from
   `Hex.Matrix`.** The conversion stage is 1.291 ms on `cyclo_phi385` and the
   pack step 2.628 ms; writing the columns straight into the packed buffer
   removes both, and removes the small-matrix overhead that is the only place
   this change costs anything.
2. **Store `UInt32` entries.** `ZMod64.Bounds` already caps the modulus at
   `2^31`, and the half-word variant is 1.36x the word variant precisely
   because boxing a `UInt32` does not allocate on a 64-bit runtime.
3. **Do not carry a Barrett context.** It buys 1.00x. Keep the modulus in a
   `UInt64` local and use the hardware remainder; that also keeps the
   reciprocal's proof obligations out of the correspondence.
4. **Do not compute the transform.** Berlekamp needs rank, echelon, and pivot
   columns. This is a 1.98x factor on its own and the cheapest part of the
   change to justify.
5. **Specialize row addition, pivot search, and the basis readback, and nothing
   else.** Every other stage is already negligible and should keep using the
   existing mathematical API unchanged.

The correspondence obligation is correspondingly narrow: a packed buffer, an
interpretation into `Matrix (ZMod64 p) n n`, entry agreement, one lemma per
elementary operation, and a simulation of the Gauss-Jordan loop, landing on a
single equality at the `fixedSpaceKernelVectors` boundary so that the Berlekamp
development keeps reasoning about ordinary matrices.

## Regeneration

```sh
lake build hexbz_factor_service
python3 scripts/bench/factor_phase_profile.py \
  --output reports/bench-results/hexbz-phase-profile-7539be44-chungus2.json
```

The driver pins itself to an idle core and exits non-zero if the counted mirror
disagrees with the production row reduction, if any packed variant disagrees with
`Hex.Matrix.nullspace`, if a scouted degree pattern disagrees with its split, or
if the recombination mirror disagrees with the production trace.
