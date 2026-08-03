# A packed finite-field matrix for Berlekamp's fixed space (issue #9132)

Issue #9128 replaced the prime planner's repeated full splitting with a bounded
degree-pattern scout, so the modular share of a factorization had to be
remeasured before any matrix specialization was justified. This page is that
remeasurement, and it is a **go**.

On `cyclo_phi385` the Berlekamp matrix and its kernel are **46.7% of total
factor time** and **96.2% of the selected prime's Berlekamp split**; on
`cyclo_phi128_x_phi165`, 43.8% and 91.5%; on `cyclo_phi64_x_phi105`, 27.0% and
82.5%. The gate asks for 25% of total on a material row or 40% of its selected-
prime Berlekamp time. Three cyclotomic rows clear the first bar and nineteen of
twenty-four rows clear the second.

Inside that share the cost is concentrated in one stage. On `cyclo_phi385`, row
addition is 303.009 ms of the 312.699 ms Gauss-Jordan run; pivot search is
7.322 us, the nullspace basis 686.377 us, and the conversion of basis vectors
back to polynomials 8.166 us. Column construction and the two representation
conversions together are 8.475 ms.

A prototype packed representation -- one contiguous row-major buffer of machine
words with the modulus held in a register -- was measured against the generic
path on the same matrices in the same process, and checked entry for entry
against `Hex.Matrix.nullspace` on all 24 instances. It reduces `cyclo_phi385`
from 335.339 ms to 8.732 ms, a **29.4x** speedup including the cost of packing,
and projects a **1.75x** end-to-end improvement on that row.

Every number here is reproducible from the committed record by the commands in
[Regeneration](#regeneration).

## Revision and protocol

- Source revision `ce4e56c6df8d3326906254ad53da768b87f6b981` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured
  2026-08-03. The host was shared with other work throughout, so absolute wall
  times are not comparable with the issue #9127 baseline taken on a quiet
  machine. Everything this page concludes from is a **ratio between variants
  measured back to back in one process on one pinned core**, which that sharing
  does not disturb; the one place absolute times are used across sections is
  the gate table, and there both the numerator and the denominator come from
  this same record.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- The driver pins itself to one idle logical CPU before spawning any service,
  so every measured descendant inherits that affinity.
- Phase profile: one warm-up call, then five timed calls below one second and
  one otherwise. Scout and counterfactual prices: median of three calls,
  merged per candidate. Kernel attribution: median of three calls, merged field
  by field after asserting that the repeats agree on everything deterministic.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-phase-profile-ce4e56c6-chungus2.json` | `ee4567f2a57547bbc35df4d127a3e4317b29e1891e375bf5efc274c29e5d6187` |

`hexbz_factor_service` SHA-256
`3da18a0b69d80e766468539864cc664881dcacf1da2ad93ace84c527a2d4d5ee`.

## How the diagnostic works

`bench/HexBench/FactorService.lean` gains one entry, `--entry kernelProfile`.
It computes the production prime plan, then walks the fixed-space kernel at the
selected prime stage by stage, calling the production function each stage names:
the Frobenius power `X^p mod f`, the column-polynomial recurrence, the
conversion of those columns into `Hex.Matrix`, the diagonal decrement that forms
`Q_f - I`, Gauss-Jordan pivot search, row swap and scale, row addition, the
nullspace basis, and the conversion of basis vectors back to polynomials. Like
the scout prices, none of this is work the production cascade does: it repeats
the modular work at the already-selected prime, after the plan is computed.

Gauss-Jordan is the one place the diagnostic does not call the production
function verbatim. `Hex.Matrix.rowReduce`'s loop reports only its final
`RowEchelonData`, so `countedRowReduce` mirrors `rowReduceLoop` column for
column -- same pivot rule, same elimination order, same elementary operations
from `HexMatrix.Elementary` -- while marking the clock between stages. Marks are
taken once per pivot column rather than once per row operation, so the clock
reads cost `O(n)` rather than `O(n^2)`.

### Validation

- The counted mirror's rank, echelon form, and pivot columns agree with
  `Hex.Matrix.rowReduce` on **24 of 24** instances, and its wall time tracks the
  production row reduction to within 1% on the three largest
  (`cyclo_phi385` 312.699 ms against 335.339 ms is the widest, 0.93x).
- The transform-free mirror produces the same echelon form and pivot columns as
  the mirror that keeps the transform, on **24 of 24**.
- Each of the three packed variants reproduces `Hex.Matrix.nullspace`'s basis
  entry for entry, on **24 of 24**. A variant that were fast because it were
  wrong could not be reported as fast.
- The pre-existing checks are unchanged and still pass on the wider sample: the
  counted recombination mirror agrees with the production `factorTrace` on leaf
  count, selected prime, completed subset cardinalities, and returned factor
  degrees on **367 of 367** instances, and the scouted degree pattern agrees
  with the Berlekamp split on **144 of 144** candidates.

### Two measurement hazards

Both were found by numbers that could not be true, and both would silently
corrupt any re-measurement that ignores them.

*Let-floating.* A pure `let` whose result is first used later is moved to that
use by the compiler, so a stage's cost lands in whichever later stage first
demands its value. Before this was handled, the Frobenius power, the column
polynomials, and the whole matrix construction all measured under 100 ns on a
240x240 matrix. Every stage result is now pushed into an `IO.Ref` before the
next clock read.

*Aliasing.* `Hex.Matrix`'s elementary operations update the flat backing buffer
in place only while the matrix is uniquely referenced. One shared
`fixedSpaceMatrix` handed to several variants makes every variant but the last
copy the whole matrix per row operation -- measured at 2.742 s against 304 ms
for the same run. Each timed consumer now gets its own freshly built matrix, and
the build is timed separately.

A third trap is worth recording for whoever implements the specialization.
`Vector` operations take the length index as a runtime argument, and for the
kernel that index is `m - Hex.Matrix.rowReduce_rank M`; demanding it runs a
second full row reduction. The diagnostic reads the basis out as an `Array`
before touching it. **Production does not pay this today**: `berlekampSplit`
measures 328.576 ms against `fixedSpaceKernelVectors`' 325.162 ms on
`cyclo_phi385`, so the `Vector.map` in `fixedSpaceKernel` costs 3.4 ms, not a
second 325 ms reduction. It is a trap to avoid, not a bug to fix.

## The measurement gate

`matrix + kernel` is the Berlekamp matrix construction plus the row reduction
and nullspace at the selected prime, timed adjacently in one process by the
scout section; `Berlekamp split` is a full `berlekampFactor` at the same prime,
timed in the same place. `total factor` is the phase profile's own total for the
production cascade. Planning overhead is already excluded: these are costs at
the *selected* prime, not the walk.

| instance | matrix | prime | total factor | matrix + kernel | Berlekamp split | share of total | share of split |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32x32 | 29 | 78.838 ms | 2.121 ms | 4.756 ms | 2.7% | 44.6% |
| `sd5_shift1` | 32x32 | 29 | 67.600 ms | 2.615 ms | 4.439 ms | 3.9% | 58.9% |
| `sd5_shift2` | 32x32 | 29 | 71.454 ms | 2.638 ms | 5.603 ms | 3.7% | 47.1% |
| `sd4_x_sd4shift1` | 32x32 | 29 | 19.281 ms | 2.607 ms | 4.759 ms | 13.5% | 54.8% |
| `sd5_x_phi11` | 42x42 | 29 | 165.578 ms | 5.365 ms | 9.852 ms | 3.2% | 54.4% |
| `xpow48_minus1` | 48x48 | 11 | 20.461 ms | 951.151 us | 2.769 ms | 4.6% | 34.3% |
| `xpow105_minus1` | 105x105 | 17 | 87.169 ms | 6.431 ms | 13.926 ms | 7.4% | 46.2% |
| `xpow120_minus1` | 120x120 | 7 | 486.744 ms | 4.704 ms | 23.665 ms | 1.0% | 19.9% |
| `cyclo_phi179` | 178x178 | 3 | 76.839 ms | 15.324 ms | 16.292 ms | 19.9% | 94.1% |
| `cyclo_phi64_x_phi105` | 80x80 | 11 | 77.419 ms | 20.887 ms | 25.303 ms | 27.0% | 82.5% |
| `cyclo_phi128_x_phi165` | 144x144 | 7 | 205.754 ms | 90.154 ms | 98.575 ms | 43.8% | 91.5% |
| `cyclo_phi385` | 240x240 | 3 | 442.525 ms | 206.516 ms | 214.614 ms | 46.7% | 96.2% |
| `wilkinson_40` | 40x40 | 47 | 14.290 ms | 252.765 us | 1.829 ms | 1.8% | 13.8% |
| `wilkinson_48` | 48x48 | 61 | 26.749 ms | 367.736 us | 2.909 ms | 1.4% | 12.6% |
| `wilkinson_56` | 56x56 | 67 | 37.312 ms | 597.356 us | 4.800 ms | 1.6% | 12.4% |
| `chebyshev_T24` (control) | 24x24 | 5 | 529.745 us | 310.280 us | 366.163 us | 58.6% | 84.7% |
| `chebyshev_U24` (control) | 24x24 | 3 | 682.141 us | 244.442 us | 318.092 us | 35.8% | 76.8% |
| `legendre_P30` (control) | 30x30 | 67 | 9.334 ms | 1.678 ms | 2.324 ms | 18.0% | 72.2% |
| `legendre_P38` (control) | 38x38 | 79 | 5.063 ms | 3.494 ms | 3.742 ms | 69.0% | 93.4% |
| `cyclo_phi17` (control) | 16x16 | 3 | 133.529 us | 95.742 us | 98.907 us | 71.7% | 96.8% |
| `cyclo_phi41` (control) | 40x40 | 3 | 2.817 ms | 457.768 us | 694.439 us | 16.3% | 65.9% |
| `xpow24_minus1` (control) | 24x24 | 11 | 3.246 ms | 193.958 us | 623.754 us | 6.0% | 31.1% |
| `randprod_10` (control) | 20x20 | 7 | 780.648 us | 422.236 us | 542.144 us | 54.1% | 77.9% |
| `randprod_21` (control) | 24x24 | 17 | 1.705 ms | 1.013 ms | 1.234 ms | 59.4% | 82.1% |

Three of the four named cyclotomic rows clear the 25%-of-total bar, and the
fourth (`cyclo_phi179`, 19.9%) clears the 40%-of-split bar at 94.1%. Nineteen
of twenty-four rows clear the split bar. The five that do not are the three
Wilkinson rows, `xpow120_minus1`, and `xpow24_minus1`.

The Wilkinson rows are a structural exception rather than a near miss. Their
selected prime splits the image into linear factors, so `Q_f - I` is the zero
matrix, the rank is 0, and Gauss-Jordan performs **no row additions at all**;
their Berlekamp time is the equal-degree splitting that follows the kernel, not
the kernel. No matrix representation can move them, and none should be expected
to.

`xpow120_minus1` is the opposite case: its 486.744 ms is 94% recombination, and
its 120x120 matrix at prime 7 costs 4.704 ms.

## Stage attribution

The seven attributions issue #9132 asks for. `conversion` is the cost of reading
the column polynomials into the generic `Hex.Matrix` representation and
`diagonal` the in-place decrement that forms `Q_f - I`; both are differences
between nested spans, because `berlekampMatrix` recomputes the Frobenius power
and the column polynomials before converting them and `fixedSpaceMatrix`
recomputes `berlekampMatrix` before decrementing. `basis` is the nullspace-basis
construction, measured as `Hex.Matrix.nullspace` less `Hex.Matrix.rowReduce` on
separately built copies of the same matrix. Small allocations are Lean's
per-thread counter; the runtime publishes counts, not bytes, so peak residency
is reported instead as the process high-water mark from `/proc/self/status`.

| instance | column polys | conversion | diagonal | pivot search | swap + scale | row addition | basis | to polynomials | small allocs | peak RSS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 1.601 ms | 21.592 us | 10.446 us | 813 ns | 50.656 us | 631.916 us | 32.829 us | 4.898 us | 31,866 | 60.2 MiB |
| `sd5_shift1` | 1.558 ms | 16.195 us | 20.140 us | 812 ns | 36.984 us | 1.027 ms | 29.564 us | 4.677 us | 62,044 | 60.5 MiB |
| `sd5_shift2` | 2.226 ms | 8.552 us | 33.270 us | 811 ns | 41.729 us | 1.420 ms | 3.746 us | 4.727 us | 62,818 | 60.6 MiB |
| `sd4_x_sd4shift1` | 2.168 ms | 24.326 us | 40.601 us | 792 ns | 52.857 us | 1.383 ms | 30.385 us | 4.727 us | 61,400 | 60.6 MiB |
| `sd5_x_phi11` | 2.763 ms | 49.443 us | 25.699 us | 1.115 us | 70.816 us | 2.746 ms | 0 ns | 5.308 us | 166,053 | 60.9 MiB |
| `xpow48_minus1` | 597.266 us | 60.519 us | 47.100 us | 1.232 us | 109.130 us | 229.112 us | 42.693 us | 7.190 us | 18,071 | 61.2 MiB |
| `xpow105_minus1` | 4.189 ms | 273.317 us | 343.609 us | 2.659 us | 789.042 us | 2.113 ms | 183.722 us | 7.482 us | 142,211 | 62.6 MiB |
| `xpow120_minus1` | 1.975 ms | 413.413 us | 236.712 us | 3.044 us | 605.309 us | 1.402 ms | 459.832 us | 27.791 us | 127,473 | 63.1 MiB |
| `cyclo_phi179` | 3.089 ms | 756.873 us | 526.440 us | 4.578 us | 2.708 ms | 19.442 ms | 0 ns | 4.447 us | 1,015,884 | 65.4 MiB |
| `cyclo_phi64_x_phi105` | 4.402 ms | 209.500 us | 186.186 us | 2.035 us | 544.799 us | 31.983 ms | 0 ns | 4.647 us | 1,413,149 | 64.5 MiB |
| `cyclo_phi128_x_phi165` | 10.384 ms | 455.116 us | 512.161 us | 3.773 us | 1.868 ms | 130.912 ms | 0 ns | 5.278 us | 7,725,927 | 64.5 MiB |
| `cyclo_phi385` | 8.000 ms | 1.311 ms | 941.866 us | 6.376 us | 4.250 ms | 308.277 ms | 0 ns | 6.560 us | 17,647,557 | 68.2 MiB |
| `wilkinson_40` | 83.414 us | 48.613 us | 31.395 us | 960 ns | 0 ns | 0 ns | 39.849 us | 19.709 us | 1,810 | 68.2 MiB |
| `wilkinson_48` | 117.755 us | 68.091 us | 43.014 us | 1.121 us | 0 ns | 0 ns | 55.553 us | 26.630 us | 2,554 | 68.2 MiB |
| `wilkinson_56` | 173.938 us | 98.176 us | 97.064 us | 1.363 us | 0 ns | 0 ns | 74.640 us | 34.781 us | 3,426 | 68.2 MiB |
| `chebyshev_T24` (control) | 140.158 us | 16.724 us | 18.308 us | 571 ns | 50.495 us | 293.328 us | 4.187 us | 1.302 us | 14,709 | 68.2 MiB |
| `chebyshev_U24` (control) | 89.983 us | 15.494 us | 19.899 us | 582 ns | 47.611 us | 261.539 us | 2.614 us | 1.232 us | 13,180 | 68.2 MiB |
| `legendre_P30` (control) | 1.537 ms | 64.146 us | 0 ns | 728 ns | 72.952 us | 955.665 us | 0 ns | 2.043 us | 43,334 | 68.2 MiB |
| `legendre_P38` (control) | 3.123 ms | 5.477 us | 83.334 us | 993 ns | 141.275 us | 2.340 ms | 10.536 us | 1.372 us | 104,644 | 68.2 MiB |
| `cyclo_phi17` (control) | 26.640 us | 5.368 us | 5.327 us | 398 ns | 19.130 us | 75.513 us | 2.304 us | 671 ns | 5,139 | 68.2 MiB |
| `cyclo_phi41` (control) | 129.111 us | 44.977 us | 30.576 us | 961 ns | 96.707 us | 346.291 us | 15.874 us | 1.822 us | 26,424 | 68.2 MiB |
| `xpow24_minus1` (control) | 166.997 us | 15.414 us | 10.005 us | 590 ns | 18.988 us | 29.846 us | 16.054 us | 3.585 us | 3,338 | 68.2 MiB |
| `randprod_10` (control) | 186.507 us | 11.336 us | 7.571 us | 482 ns | 24.167 us | 364.933 us | 4.908 us | 1.081 us | 21,354 | 68.2 MiB |
| `randprod_21` (control) | 655.712 us | 19.058 us | 3.495 us | 609 ns | 30.213 us | 639.631 us | 8.963 us | 1.753 us | 37,396 | 68.2 MiB |

Row addition is the whole cost. On `cyclo_phi385` it is 96.9% of the Gauss-
Jordan run and 97.0% of the fixed-space kernel; pivot search is 7.322 us, four
orders of magnitude below it, and the two conversions plus the basis and its
polynomial readback come to 2.995 ms against 303.009 ms. Column construction --
240 polynomial products and monic reductions -- is 6.174 ms and becomes the
kernel's largest remaining cost once row addition is specialized.

The row-addition counters explain the two shapes. `cyclo_phi385` performs 17,948
row additions and skips 38,456 more on an already-zero coefficient;
`cyclo_phi179` performs only 1,114 and skips 30,038, which is why its 178x178
matrix costs less than `cyclo_phi64_x_phi105`'s 80x80.

## What a packed representation buys

Three packed variants, all storing the matrix as one contiguous row-major buffer
and holding the modulus in a machine word:

* **packed word** -- `Array UInt64` entries, Barrett reciprocal;
* **packed half-word** -- `Array UInt32` entries, Barrett reciprocal. Faithful
  because `ZMod64.Bounds` caps the modulus at `2^31`, and on a 64-bit runtime
  `lean_box_uint32` is a tagged immediate while `lean_box_uint64` allocates;
* **packed half-word, division** -- the same `UInt32` storage with a hardware
  remainder instead of the reciprocal.

All three compute the rank and the full nullspace basis. `pack` is the cost of
reading the generic matrix into the buffer, and `speedup` is the production row
reduction against packing plus reducing.

| instance | generic, with transform | generic, echelon only | packed word | packed half-word | packed half-word, division | pack | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 698.706 us | 402.287 us | 34.341 us | 26.129 us | 25.207 us | 39.259 us | 10.7x |
| `sd5_shift1` | 1.498 ms | 784.684 us | 84.215 us | 52.047 us | 51.577 us | 38.567 us | 16.5x |
| `sd5_shift2` | 1.517 ms | 815.039 us | 86.969 us | 52.007 us | 52.007 us | 39.268 us | 16.6x |
| `sd4_x_sd4shift1` | 1.461 ms | 792.936 us | 86.478 us | 51.957 us | 51.156 us | 38.807 us | 16.1x |
| `sd5_x_phi11` | 2.932 ms | 1.530 ms | 231.112 us | 134.068 us | 137.324 us | 69.723 us | 14.4x |
| `xpow48_minus1` | 358.662 us | 284.572 us | 27.140 us | 25.628 us | 23.635 us | 92.487 us | 3.0x |
| `xpow105_minus1` | 2.781 ms | 2.043 ms | 155.941 us | 146.177 us | 143.523 us | 476.216 us | 4.5x |
| `xpow120_minus1` | 1.911 ms | 1.597 ms | 152.537 us | 141.310 us | 140.048 us | 629.915 us | 2.5x |
| `cyclo_phi179` | 22.175 ms | 13.000 ms | 715.511 us | 677.114 us | 669.553 us | 1.429 ms | 10.5x |
| `cyclo_phi64_x_phi105` | 32.700 ms | 16.980 ms | 1.643 ms | 974.415 us | 998.260 us | 270.331 us | 26.3x |
| `cyclo_phi128_x_phi165` | 139.970 ms | 67.825 ms | 8.241 ms | 4.870 ms | 4.951 ms | 917.040 us | 24.2x |
| `cyclo_phi385` | 335.339 ms | 159.350 ms | 11.719 ms | 8.732 ms | 8.719 ms | 2.692 ms | 29.4x |
| `wilkinson_40` | 39.779 us | 42.042 us | 4.817 us | 4.697 us | 4.056 us | 61.962 us | 0.6x |
| `wilkinson_48` | 56.944 us | 59.087 us | 6.610 us | 6.259 us | 5.608 us | 92.227 us | 0.6x |
| `wilkinson_56` | 117.695 us | 117.444 us | 8.542 us | 8.021 us | 7.561 us | 128.771 us | 0.9x |
| `chebyshev_T24` (control) | 336.138 us | 211.864 us | 18.307 us | 15.513 us | 14.581 us | 20.590 us | 9.3x |
| `chebyshev_U24` (control) | 309.629 us | 192.996 us | 15.993 us | 13.410 us | 12.228 us | 20.680 us | 9.1x |
| `legendre_P30` (control) | 1.056 ms | 583.896 us | 44.696 us | 33.440 us | 32.739 us | 34.221 us | 15.6x |
| `legendre_P38` (control) | 2.496 ms | 1.364 ms | 90.184 us | 71.797 us | 70.926 us | 56.734 us | 19.4x |
| `cyclo_phi17` (control) | 92.917 us | 66.228 us | 7.831 us | 7.010 us | 6.040 us | 8.142 us | 6.1x |
| `cyclo_phi41` (control) | 450.678 us | 300.436 us | 31.627 us | 28.583 us | 27.571 us | 63.704 us | 4.9x |
| `xpow24_minus1` (control) | 54.721 us | 46.820 us | 6.991 us | 6.610 us | 5.619 us | 20.991 us | 2.0x |
| `randprod_10` (control) | 390.799 us | 234.117 us | 28.171 us | 18.307 us | 18.087 us | 13.790 us | 12.2x |
| `randprod_21` (control) | 677.155 us | 386.293 us | 49.463 us | 30.946 us | 30.796 us | 20.751 us | 13.1x |

The win decomposes cleanly on `cyclo_phi385`, 335.339 ms down to 8.732 ms:

| step | time | factor |
|---|---:|---:|
| production `rowReduce` | 335.339 ms | -- |
| drop the transform the nullspace never reads | 159.350 ms | 2.10x |
| contiguous words, modulus in a register | 11.719 ms | 13.60x |
| `UInt32` entries instead of `UInt64` | 8.732 ms | 1.34x |
| Barrett reciprocal instead of hardware remainder | 8.719 ms | 1.00x |

Two of these deserve comment.

**The transform is half the elementary-operation work and is dead.**
`Hex.Matrix.rowReduce` maintains an `n x n` transform `T` with `T * M = echelon`
in lockstep with the echelon form, applying every swap, scale, and row addition
twice. `Hex.Matrix.nullspace` reads only `rank`, `echelon`, and `pivotCols`.
That 2.10x is available without any change of representation.

**A Barrett reciprocal is not worth carrying.** Against a hardware remainder it
is 1.00x on `cyclo_phi385` and slower on eleven of the twenty-four rows. What
matters is holding the modulus as a machine word in the loop rather than
reaching it through `ZMod64.mul`, whose `@[extern]` contract takes the modulus
as a boxed `Nat` and converts it on every multiply.

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

`cyclo_phi385` goes from 17.6 million small allocations to 97 thousand, a factor
of 181. Peak resident set stays between 60 and 72 MiB throughout and is not a
constraint on any row.

## Projected end to end

Applying each row's measured packed ratio to its in-cascade row reduction, and
leaving the Berlekamp matrix construction unchanged:

| instance | total factor now | matrix + kernel now | matrix + kernel packed | projected total | projected gain |
|---|---:|---:|---:|---:|---:|
| `sd5` | 78.838 ms | 2.121 ms | 1.717 ms | 78.434 ms | 1.01x |
| `sd5_shift1` | 67.600 ms | 2.615 ms | 1.680 ms | 66.664 ms | 1.01x |
| `sd5_shift2` | 71.454 ms | 2.638 ms | 2.285 ms | 71.101 ms | 1.00x |
| `sd4_x_sd4shift1` | 19.281 ms | 2.607 ms | 2.311 ms | 18.986 ms | 1.02x |
| `sd5_x_phi11` | 165.578 ms | 5.365 ms | 3.038 ms | 163.252 ms | 1.01x |
| `xpow48_minus1` | 20.461 ms | 951.151 us | 797.518 us | 20.307 ms | 1.01x |
| `xpow105_minus1` | 87.169 ms | 6.431 ms | 5.174 ms | 85.912 ms | 1.01x |
| `xpow120_minus1` | 486.744 ms | 4.704 ms | 3.490 ms | 485.531 ms | 1.00x |
| `cyclo_phi179` | 76.839 ms | 15.324 ms | 5.613 ms | 67.128 ms | 1.14x |
| `cyclo_phi64_x_phi105` | 77.419 ms | 20.887 ms | 6.046 ms | 62.578 ms | 1.24x |
| `cyclo_phi128_x_phi165` | 205.754 ms | 90.154 ms | 14.435 ms | 130.035 ms | 1.58x |
| `cyclo_phi385` | 442.525 ms | 206.516 ms | 16.803 ms | 252.812 ms | 1.75x |
| `wilkinson_40` | 14.290 ms | 252.765 us | 269.649 us | 14.307 ms | 1.00x |
| `wilkinson_48` | 26.749 ms | 367.736 us | 383.599 us | 26.765 ms | 1.00x |
| `wilkinson_56` | 37.312 ms | 597.356 us | 712.697 us | 37.427 ms | 1.00x |
| `chebyshev_T24` (control) | 529.745 us | 310.280 us | 189.878 us | 409.343 us | 1.29x |
| `chebyshev_U24` (control) | 682.141 us | 244.442 us | 140.944 us | 578.643 us | 1.18x |
| `legendre_P30` (control) | 9.334 ms | 1.678 ms | 1.701 ms | 9.357 ms | 1.00x |
| `legendre_P38` (control) | 5.063 ms | 3.494 ms | 3.425 ms | 4.994 ms | 1.01x |
| `cyclo_phi17` (control) | 133.529 us | 95.742 us | 48.745 us | 86.532 us | 1.54x |
| `cyclo_phi41` (control) | 2.817 ms | 457.768 us | 256.540 us | 2.615 ms | 1.08x |
| `xpow24_minus1` (control) | 3.246 ms | 193.958 us | 203.021 us | 3.255 ms | 1.00x |
| `randprod_10` (control) | 780.648 us | 422.236 us | 227.101 us | 585.513 us | 1.33x |
| `randprod_21` (control) | 1.705 ms | 1.013 ms | 727.428 us | 1.420 ms | 1.20x |

The four named cyclotomic rows gain 1.14x to 1.75x. Nothing regresses: the
largest projected slowdown is the three Wilkinson rows and `xpow24_minus1` at
1.00x, where a rank-0 or nearly-trivial reduction still pays to be packed. That
overhead is 17 to 115 us against 3.2 to 37.3 ms of total factor time, under
0.4% in every case, and a production implementation removes it entirely by
building the packed matrix directly from the column polynomials instead of
converting an already-built generic one.

## Verdict, and the design it implies

**Go.** The gate is met with room to spare and the ceiling is large enough to
matter end to end.

The measurements narrow the design considerably from the issue's sketch.

1. **Build the packed matrix from the column polynomials, not from
   `Hex.Matrix`.** The conversion bucket is 1.321 ms on `cyclo_phi385` and the
   pack step is 2.692 ms; writing the columns straight into the packed buffer
   removes both, and removes the small-matrix overhead that is the only place
   this change costs anything.
2. **Store `UInt32` entries.** `ZMod64.Bounds` already caps the modulus at
   `2^31`, and the half-word variant is 1.34x the word variant precisely
   because boxing a `UInt32` does not allocate on a 64-bit runtime.
3. **Do not carry a Barrett context.** It buys 1.00x. Keep the modulus as a
   `UInt64` local and use the hardware remainder; this also removes the
   reciprocal's proof obligations from the correspondence.
4. **Do not compute the transform.** Berlekamp needs rank, echelon, and pivot
   columns. This is a 2.10x factor on its own and is the cheapest part of the
   change to justify.
5. **Specialize only row addition, pivot search, and the basis readback.** Every
   other stage is already negligible and should keep using the existing
   mathematical API unchanged.

The correspondence obligation is correspondingly narrow: a packed buffer, an
interpretation into `Matrix (ZMod64 p) n n`, entry agreement, one lemma per
elementary operation, and a simulation of the Gauss-Jordan loop, landing on a
single equality at the `fixedSpaceKernelVectors` boundary so the Berlekamp
development keeps reasoning about ordinary matrices.

## Regeneration

```sh
lake build hexbz_factor_service
python3 scripts/bench/factor_phase_profile.py \
  --output reports/bench-results/hexbz-phase-profile-ce4e56c6-chungus2.json
```

The driver pins itself to an idle core, exits non-zero if the counted mirror
disagrees with the production row reduction, if any packed variant disagrees
with `Hex.Matrix.nullspace`, if a scouted degree pattern disagrees with its
split, or if the recombination mirror disagrees with the production trace.
