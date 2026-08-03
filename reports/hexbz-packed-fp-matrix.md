# A packed finite-field matrix for Berlekamp's fixed space (issue #9132)

Issue #9128 replaced the prime planner's repeated full splitting with a bounded
degree-pattern scout, so the modular share of a factorization had to be
remeasured before any matrix specialization was justified. This page is that
remeasurement, and it is a **go**.

On `cyclo_phi385` the row reduction and nullspace basis at the selected prime
are **46.1% of total factor time** and **94.3% of that prime's Berlekamp
split**; on `cyclo_phi128_x_phi165`, 44.1% and 88.6%; on
`cyclo_phi64_x_phi105`, 27.2% and 74.9%. Issue #9132 asks for 25% of total factor
time on a material row, or 40% of its selected-prime Berlekamp time; 8 of
24 rows clear the first and 10 of 24 clear the second.

The numerator here is deliberately **the row reduction and basis alone**, not
the whole modular kernel. Berlekamp matrix construction is a polynomial
computation -- one Frobenius power and `n` products with monic reductions --
that a packed matrix representation does not accelerate, so counting it would
inflate the share of exactly the work under discussion. The in-cascade
measurement gives the whole kernel in one span, so the construction fraction is
taken from the kernel section, which times the build on its own; both columns
are shown. That correction is small on the large cyclotomic rows (2.6% of the
kernel on `cyclo_phi385`) and large on the small ones (58.0% on `legendre_P38`).

Inside that share the cost is one stage. On `cyclo_phi385`, row addition is
301.268 ms of the 305.201 ms Gauss-Jordan run; pivot search is 6.386 us, the nullspace
basis 550.256 us, and the conversion of basis vectors back to polynomials
7.021 us.

A prototype packed representation -- one contiguous row-major buffer with the
modulus held in a machine-word local -- was measured against the generic path on
the same matrices in the same process, and checked entry for entry against
`Hex.Matrix.nullspace` on all 24 instances. It reduces `cyclo_phi385`'s row
reduction from 311.525 ms to 15.761 ms, a **16.8x** speedup including the
cost of packing, and projects a **1.72x** end-to-end improvement on that row.

Every number here is reproducible from the committed record by the commands in
[Regeneration](#regeneration). Section
[What the measurements do not establish](#what-the-measurements-do-not-establish)
states the limits of the evidence, and they are not small.

## Revision and protocol

- Source revision `47aa704800d77e72afdbe72dc9ec12605396775c` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured
  2026-08-03. The host was shared with other work throughout.
- The driver pins itself to one logical CPU before spawning any service, so
  every measured descendant inherits that affinity. This run used CPU 1.
- Phase profile: one warm-up call, then 5 timed calls below one second and
  one otherwise. Scout and counterfactual prices: median of 3 calls, merged
  per candidate. Kernel attribution: median of 3 calls, merged field by field
  after asserting that the repeats agree on everything deterministic.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-phase-profile-47aa7048-chungus2.json` | `84337b3442997e8aa74278348f424b44202ce00a06a9f437641861255ed09fb4` |

`hexbz_factor_service` SHA-256 `e33c56e6b3286ffdbd931f61581c2ea9b8a3f667f222dd07eef00f58890e8db0`.
Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.

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

Each timed consumer receives its own freshly built fixed-space matrix, forced
past the compiler's code motion and timed on its own, because `Hex.Matrix`'s
elementary operations update the flat backing buffer in place only while the
matrix is uniquely referenced.

### Validation

- The counted mirror's rank, echelon form, and pivot columns agree with
  `Hex.Matrix.rowReduce` on **24 of 24** instances. Its wall time tracks the
  production row reduction with a median ratio of **1.024** across all 24
  rows, minimum 0.858 and maximum 1.730; the per-row ratios are in the
  packed-pricing table below. The extremes are the sub-100-us rows, where a
  handful of clock reads is a visible fraction of the run.
- The transform-free mirror produces the same echelon form and pivot columns as
  the mirror that keeps the transform, on **24 of 24**.
- Each of the four packed variants reproduces `Hex.Matrix.nullspace`'s basis
  entry for entry, on **24 of 24**. A variant that was fast because it was
  wrong could not be reported as fast.
- The pre-existing checks still pass on the wider sample: the counted
  recombination mirror agrees with the production `factorTrace` on leaf count,
  selected prime, completed subset cardinalities, and returned factor degrees on
  **367 of 367** instances, and the scouted degree pattern agrees with the
  Berlekamp split on **144 of 144** candidates.

### Four measurement hazards

All four were found by numbers that could not be true, and each would silently
corrupt a re-measurement that ignored it.

*Let-floating.* A pure `let` whose result is first used later is moved to that
use by the compiler, so a stage's cost lands in whichever later stage first
demands its value. Before this was handled, the Frobenius power, the column
polynomials, and the whole matrix construction all measured under 100 ns on a
240x240 matrix.

*Common-subexpression elimination through the forcing barrier.* Pushing a scalar
projection of each stage into an `IO.Ref` is not enough when the same pure
expression appears more than once: the compiler shares the projections and floats
the builds. The second, third and fourth `fixedSpaceMatrix` rebuilds measured
about 130 ns until each build was given a salt read from the ref at runtime.
Their cost had been charged to the consumer under test.

*Aliasing.* `Hex.Matrix`'s elementary operations update the flat backing buffer in
place only while the matrix is uniquely referenced. One shared `fixedSpaceMatrix`
handed to several variants makes every variant but the last copy the whole matrix
per row operation, measured at 2.742 s against 304 ms for the same run.

*The length index.* `Vector` operations take the length as a runtime argument, and
for this kernel that length is `m - Hex.Matrix.rowReduce_rank M`; demanding it
runs a second full row reduction. The diagnostic reads the basis out as an
`Array` before touching it. Production does not pay this today, but it is a trap
for the implementation to avoid.

## The measurement threshold

`fixed-space kernel` is the whole modular kernel at the selected prime --
construction, row reduction, and nullspace basis -- timed in one span by the
scout section. It is split into `construction` and `reduction + basis` by the
construction fraction the kernel section measures, because a packed
representation accelerates only the second. `Berlekamp split` is a full
`berlekampFactor` at the same prime, timed in the same place, and `total factor`
is the phase profile's own total for the production cascade. Planning overhead is
excluded: these are costs at the *selected* prime, not costs of the walk.

| instance | matrix | prime | total factor | fixed-space kernel | construction | reduction + basis | share of total | Berlekamp split | share of split |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32x32 | 29 | 77.583 ms | 1.603 ms | 1.105 ms | 498.328 us | 0.6% | 3.556 ms | 14.0% |
| `sd5_shift1` | 32x32 | 29 | 67.368 ms | 2.266 ms | 1.357 ms | 909.473 us | 1.4% | 3.659 ms | 24.9% |
| `sd5_shift2` | 32x32 | 29 | 70.001 ms | 2.273 ms | 1.350 ms | 923.471 us | 1.3% | 5.152 ms | 17.9% |
| `sd4_x_sd4shift1` | 32x32 | 29 | 18.966 ms | 2.284 ms | 1.377 ms | 906.127 us | 4.8% | 4.437 ms | 20.4% |
| `sd5_x_phi11` | 42x42 | 29 | 164.715 ms | 4.649 ms | 2.339 ms | 2.309 ms | 1.4% | 9.147 ms | 25.2% |
| `xpow48_minus1` | 48x48 | 11 | 19.330 ms | 748.610 us | 504.969 us | 243.640 us | 1.3% | 2.135 ms | 11.4% |
| `xpow105_minus1` | 105x105 | 17 | 75.332 ms | 4.948 ms | 3.137 ms | 1.811 ms | 2.4% | 9.962 ms | 18.2% |
| `xpow120_minus1` | 120x120 | 7 | 508.038 ms | 3.771 ms | 2.146 ms | 1.626 ms | 0.3% | 17.423 ms | 9.3% |
| `cyclo_phi179` | 178x178 | 3 | 74.597 ms | 14.019 ms | 2.566 ms | 11.454 ms | 15.4% | 15.047 ms | 76.1% |
| `cyclo_phi64_x_phi105` | 80x80 | 11 | 60.512 ms | 19.052 ms | 2.575 ms | 16.477 ms | 27.2% | 21.997 ms | 74.9% |
| `cyclo_phi128_x_phi165` | 144x144 | 7 | 198.630 ms | 93.260 ms | 5.575 ms | 87.685 ms | 44.1% | 98.991 ms | 88.6% |
| `cyclo_phi385` | 240x240 | 3 | 434.770 ms | 205.938 ms | 5.393 ms | 200.544 ms | 46.1% | 212.632 ms | 94.3% |
| `wilkinson_40` | 40x40 | 47 | 13.187 ms | 255.439 us | 212.573 us | 42.865 us | 0.3% | 1.818 ms | 2.4% |
| `wilkinson_48` | 48x48 | 61 | 24.918 ms | 366.003 us | 303.040 us | 62.962 us | 0.3% | 2.875 ms | 2.2% |
| `wilkinson_56` | 56x56 | 67 | 34.052 ms | 574.282 us | 488.575 us | 85.706 us | 0.3% | 4.389 ms | 2.0% |
| `chebyshev_T24` (control) | 24x24 | 5 | 514.132 us | 297.961 us | 103.468 us | 194.492 us | 37.8% | 335.537 us | 58.0% |
| `chebyshev_U24` (control) | 24x24 | 3 | 658.556 us | 246.105 us | 100.420 us | 145.684 us | 22.1% | 321.526 us | 45.3% |
| `legendre_P30` (control) | 30x30 | 67 | 9.279 ms | 1.663 ms | 1.037 ms | 625.435 us | 6.7% | 2.303 ms | 27.2% |
| `legendre_P38` (control) | 38x38 | 79 | 4.567 ms | 3.493 ms | 2.025 ms | 1.468 ms | 32.2% | 3.721 ms | 39.5% |
| `cyclo_phi17` (control) | 16x16 | 3 | 129.422 us | 96.343 us | 29.764 us | 66.578 us | 51.4% | 99.928 us | 66.6% |
| `cyclo_phi41` (control) | 40x40 | 3 | 2.795 ms | 455.666 us | 148.828 us | 306.837 us | 11.0% | 688.922 us | 44.5% |
| `xpow24_minus1` (control) | 24x24 | 11 | 3.226 ms | 192.846 us | 147.779 us | 45.066 us | 1.4% | 614.652 us | 7.3% |
| `randprod_10` (control) | 20x20 | 7 | 777.673 us | 430.878 us | 137.505 us | 293.372 us | 37.7% | 539.210 us | 54.4% |
| `randprod_21` (control) | 24x24 | 17 | 1.697 ms | 1.007 ms | 476.449 us | 530.173 us | 31.2% | 1.219 ms | 43.5% |

8 of 24 rows clear the 25%-of-total bar and 10 of 24 clear the 40%-of-split
bar. Three of the four named cyclotomic rows clear the first; the fourth,
`cyclo_phi179` at 15.4%, clears the second at 76.1%.

The Wilkinson rows are a structural exception rather than a near miss: their
selected prime splits the image into linear factors, so `Q_f - I` is the zero
matrix, the rank is 0, and Gauss-Jordan performs **no row additions at all**.
Their Berlekamp time is the equal-degree splitting that follows the kernel. No
matrix representation can move them, and none should be expected to.

## Stage attribution

The seven attributions issue #9132 asks for. `conversion` is the cost of reading
the column polynomials into the generic `Hex.Matrix` representation and
`diagonal` the in-place decrement that forms `Q_f - I`; both are differences
between nested spans, because `berlekampMatrix` recomputes the Frobenius power
and the column polynomials before converting them and `fixedSpaceMatrix`
recomputes `berlekampMatrix` before decrementing. `basis` is the nullspace-basis
construction, measured within each execution as `Hex.Matrix.nullspace` less
`Hex.Matrix.rowReduce` on two separately built copies. A leading minus marks a
difference that came out negative, which means the stage is below the noise floor
of the two spans it is the difference of, not that it is free.

Memory is the one attribution this diagnostic does not deliver as asked. Lean's
runtime publishes a per-thread count of small allocations, not allocated bytes,
and it does not account for large objects; the counts below are therefore counts.
Peak residency is not reported per row at all: `/proc/self/status`'s `VmHWM` is a
high-water mark for the whole long-lived service process, so after the largest
row it simply plateaus (68.6 MiB on this run) and attributes nothing. Getting
allocated bytes and per-variant peak residency needs a fresh process per variant
and an allocator-level counter, which this driver does not have.

| instance | column polys | conversion | diagonal | pivot search | swap + scale | row addition | basis | to polynomials | small allocs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 1.175 ms | 27.039 us | 20.791 us | 830 ns | 37.114 us | 503.836 us | 22.964 us | 4.627 us | 31,866 |
| `sd5_shift1` | 1.525 ms | 23.425 us | 15.513 us | 852 ns | 36.592 us | 1.017 ms | 43.765 us | 4.617 us | 62,044 |
| `sd5_shift2` | 1.512 ms | 17.496 us | 21.211 us | 862 ns | 35.781 us | 1.039 ms | 46.329 us | 4.537 us | 62,818 |
| `sd4_x_sd4shift1` | 1.523 ms | 22.153 us | 19.019 us | 884 ns | 36.283 us | 997.830 us | 43.754 us | 4.457 us | 61,400 |
| `sd5_x_phi11` | 2.684 ms | 36.404 us | 123.143 us | 1.173 us | 71.455 us | 2.697 ms | 79.168 us | 5.328 us | 166,053 |
| `xpow48_minus1` | 465.199 us | 53.479 us | 35.584 us | 1.322 us | 92.140 us | 179.856 us | 58.817 us | 6.750 us | 18,071 |
| `xpow105_minus1` | 3.176 ms | 244.582 us | 174.819 us | 2.753 us | 604.170 us | 1.568 ms | 219.646 us | 7.351 us | 142,211 |
| `xpow120_minus1` | 1.958 ms | 358.012 us | 206.236 us | 3.039 us | 615.045 us | 1.294 ms | 459.722 us | 28.252 us | 127,473 |
| `cyclo_phi179` | 2.384 ms | 732.476 us | 514.353 us | 4.578 us | 1.981 ms | 14.295 ms | 320.085 us | 3.625 us | 1,015,884 |
| `cyclo_phi64_x_phi105` | 3.544 ms | 120.629 us | 107.440 us | 2.107 us | 374.264 us | 23.278 ms | 173.377 us | 5.158 us | 1,413,149 |
| `cyclo_phi128_x_phi165` | 7.478 ms | 430.238 us | 346.734 us | 3.893 us | 1.309 ms | 129.048 ms | 2.848 ms | 6.239 us | 7,725,927 |
| `cyclo_phi385` | 6.196 ms | 1.256 ms | 931.833 us | 6.386 us | 3.926 ms | 301.268 ms | -550.256 us | 7.021 us | 17,647,557 |
| `wilkinson_40` | 74.230 us | 34.241 us | 24.936 us | 1.008 us | 0 ns | 0 ns | 39.559 us | 18.477 us | 1,810 |
| `wilkinson_48` | 103.804 us | 49.794 us | 42.813 us | 1.183 us | 0 ns | 0 ns | 57.515 us | 26.099 us | 2,554 |
| `wilkinson_56` | 139.046 us | 65.738 us | 54.752 us | 1.311 us | 0 ns | 0 ns | 74.490 us | 34.110 us | 3,426 |
| `chebyshev_T24` (control) | 104.896 us | 11.778 us | 10.935 us | 602 ns | 37.316 us | 218.778 us | 10.385 us | 1.182 us | 14,709 |
| `chebyshev_U24` (control) | 110.824 us | 17.646 us | 10.776 us | 760 ns | 57.075 us | 309.771 us | 12.628 us | 1.433 us | 13,180 |
| `legendre_P30` (control) | 1.088 ms | 12.840 us | 16.404 us | 861 ns | 49.944 us | 685.037 us | 26.019 us | 2.084 us | 43,334 |
| `legendre_P38` (control) | 2.235 ms | 29.463 us | 32.568 us | 951 ns | 93.349 us | 1.703 ms | 24.547 us | 1.442 us | 104,644 |
| `cyclo_phi17` (control) | 26.329 us | 5.499 us | 5.267 us | 391 ns | 18.854 us | 73.359 us | 3.946 us | 581 ns | 5,139 |
| `cyclo_phi41` (control) | 134.450 us | 36.163 us | 29.534 us | 1.093 us | 96.571 us | 335.579 us | 31.598 us | 1.722 us | 26,424 |
| `xpow24_minus1` (control) | 133.949 us | 11.928 us | 14.051 us | 632 ns | 19.425 us | 30.147 us | 16.343 us | 3.385 us | 3,338 |
| `randprod_10` (control) | 157.283 us | 7.320 us | 8.373 us | 509 ns | 23.742 us | 358.414 us | 12.698 us | 1.021 us | 21,354 |
| `randprod_21` (control) | 539.029 us | 16.404 us | -6.769 us | 610 ns | 29.784 us | 624.976 us | 24.716 us | 1.703 us | 37,396 |

Row addition is the whole cost. On `cyclo_phi385` it is 98.7% of the Gauss-Jordan
run; pivot search is 6.386 us, four orders of magnitude below it, and the two
conversions plus the basis and its polynomial readback come to
2.745 ms against 301.268 ms. Column construction is 6.196 ms and becomes the
kernel's largest remaining cost once row addition is specialized.

The row-addition counters explain the two shapes among the cyclotomic rows.
`cyclo_phi385` performs 17,948 row additions and skips 38,456 more on an
already-zero coefficient; `cyclo_phi179` performs only 1,114 and skips
30,038, which is why its 178x178 matrix costs less than
`cyclo_phi64_x_phi105`'s 80x80.

## What a packed representation buys

Four packed variants, all storing the matrix as one contiguous row-major buffer
and holding the modulus in a `UInt64` local:

* **immediate `UInt64`** -- `UInt64` entries, Barrett reciprocal;
* **immediate `UInt32`** -- `UInt32` entries, Barrett reciprocal. Faithful
  because `ZMod64.Bounds` caps the modulus at `2^31`. The gain is *not* four-byte
  storage density: Lean's `Array` holds one machine-word slot per element either
  way. It is that `lean_box_uint32` is a tagged immediate on a 64-bit runtime
  while `lean_box_uint64` heap-allocates, so storing a residue stops allocating;
* **`UInt32`, hardware `%`** -- the same storage with a hardware remainder
  instead of the reciprocal;
* **`UInt32`, zero-skip** -- the same again, additionally skipping the multiply
  and store where the source-row entry is already zero.

The first three perform a full-width row addition at every entry, exactly as
`Hex.Matrix.rowAdd` does, so they price the representation and nothing else. The
fourth prices an algorithmic optimization the generic path does not have, and is
reported separately for that reason: on `cyclo_phi385` at `p = 3` roughly a third
of entries are zero, and skipping them is worth 1.70x on its own. All four
compute the rank and the full nullspace basis and all four are checked against
`Hex.Matrix.nullspace`. `speedup` is the production row reduction against packing
plus reducing.

| instance | generic, with transform | mirror / production | generic, echelon only | immediate `UInt64` | immediate `UInt32` | `UInt32`, hardware `%` | speedup | `UInt32`, zero-skip |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 561.933 us | 0.993 | 322.178 us | 67.079 us | 35.272 us | 35.242 us | 7.3x | 24.887 us |
| `sd5_shift1` | 1.065 ms | 1.007 | 595.202 us | 124.124 us | 61.431 us | 60.910 us | 10.3x | 51.446 us |
| `sd5_shift2` | 1.079 ms | 1.012 | 598.197 us | 124.064 us | 60.870 us | 60.520 us | 10.5x | 51.937 us |
| `sd4_x_sd4shift1` | 1.043 ms | 1.008 | 580.691 us | 121.880 us | 60.389 us | 60.569 us | 10.2x | 51.557 us |
| `sd5_x_phi11` | 2.839 ms | 0.985 | 1.508 ms | 328.797 us | 156.612 us | 155.791 us | 12.3x | 137.003 us |
| `xpow48_minus1` | 270.922 us | 1.135 | 227.668 us | 43.765 us | 46.419 us | 27.591 us | 1.7x | 24.887 us |
| `xpow105_minus1` | 2.085 ms | 1.105 | 1.565 ms | 322.047 us | 188.219 us | 186.687 us | 3.0x | 155.271 us |
| `xpow120_minus1` | 1.913 ms | 1.099 | 1.485 ms | 294.016 us | 174.478 us | 173.798 us | 2.3x | 150.853 us |
| `cyclo_phi179` | 16.221 ms | 1.027 | 9.612 ms | 2.161 ms | 1.064 ms | 1.075 ms | 6.3x | 723.743 us |
| `cyclo_phi64_x_phi105` | 24.192 ms | 0.981 | 12.335 ms | 2.818 ms | 1.281 ms | 1.304 ms | 15.4x | 1.006 ms |
| `cyclo_phi128_x_phi165` | 127.647 ms | 1.024 | 65.427 ms | 15.505 ms | 6.858 ms | 7.120 ms | 16.3x | 5.101 ms |
| `cyclo_phi385` | 311.525 ms | 0.982 | 155.580 ms | 38.173 ms | 15.761 ms | 15.917 ms | 16.8x | 9.254 ms |
| `wilkinson_40` | 44.516 us | 0.907 | 41.862 us | 4.897 us | 4.707 us | 4.136 us | 0.6x | 4.026 us |
| `wilkinson_48` | 66.098 us | 0.858 | 60.210 us | 6.480 us | 6.149 us | 5.649 us | 0.6x | 5.598 us |
| `wilkinson_56` | 87.540 us | 0.862 | 79.618 us | 8.733 us | 8.242 us | 7.551 us | 0.6x | 8.072 us |
| `chebyshev_T24` (control) | 246.515 us | 1.078 | 163.853 us | 32.188 us | 19.499 us | 18.648 us | 5.9x | 15.083 us |
| `chebyshev_U24` (control) | 221.248 us | 1.730 | 225.965 us | 40.700 us | 26.690 us | 22.824 us | 3.8x | 17.696 us |
| `legendre_P30` (control) | 738.966 us | 1.015 | 457.498 us | 92.236 us | 48.071 us | 47.280 us | 8.7x | 32.929 us |
| `legendre_P38` (control) | 1.778 ms | 1.023 | 1.009 ms | 212.855 us | 107.329 us | 107.789 us | 10.6x | 73.169 us |
| `cyclo_phi17` (control) | 86.649 us | 1.118 | 63.394 us | 12.558 us | 8.373 us | 7.661 us | 5.1x | 6.409 us |
| `cyclo_phi41` (control) | 418.360 us | 1.085 | 295.489 us | 57.556 us | 35.442 us | 35.192 us | 4.1x | 28.913 us |
| `xpow24_minus1` (control) | 51.507 us | 1.175 | 46.739 us | 9.434 us | 7.061 us | 6.118 us | 1.8x | 5.969 us |
| `randprod_10` (control) | 377.770 us | 1.032 | 223.872 us | 44.015 us | 23.184 us | 22.934 us | 10.0x | 18.337 us |
| `randprod_21` (control) | 648.141 us | 1.024 | 371.310 us | 74.770 us | 37.396 us | 37.145 us | 10.9x | 31.126 us |

The win decomposes on `cyclo_phi385`:

| step | time | factor |
|---|---:|---:|
| production `Hex.Matrix.rowReduce` | 311.525 ms | -- |
| drop the transform the nullspace never reads | 155.580 ms | 2.00x |
| contiguous buffer, modulus in a machine-word local | 38.173 ms | 4.08x |
| immediate `UInt32` entries instead of boxed `UInt64` | 15.761 ms | 2.42x |
| Barrett reciprocal instead of hardware remainder | 15.917 ms | 1.01x |
| *(separately)* skipping zero source entries | 9.254 ms | 1.70x |

Two of these deserve comment.

**The transform is half the elementary-operation work, and it is dead.**
`Hex.Matrix.rowReduce` maintains an `n x n` transform `T` with `T * M = echelon`
in lockstep with the echelon form, applying every swap, scale, and row addition
twice. `Hex.Matrix.nullspace` reads only `rank`, `echelon`, and `pivotCols`. That
factor of 2.00 is available without any change of representation.

**Boxing, not density, is what `UInt32` buys.** The entries occupy the same
machine-word array slots either way. What changes is that a `UInt32` residue is a
tagged immediate and a `UInt64` residue is a heap object, so the inner loop stops
allocating one object per multiply.

Allocation follows that shape:

| instance | generic with transform | generic echelon only | immediate `UInt64` | immediate `UInt32` |
|---|---:|---:|---:|---:|
| `sd5` | 31,866 | 17,591 | 8,858 | 1,466 |
| `sd5_shift1` | 62,044 | 32,793 | 16,080 | 1,232 |
| `sd5_shift2` | 62,818 | 33,183 | 16,266 | 1,226 |
| `sd4_x_sd4shift1` | 61,400 | 32,469 | 15,925 | 1,237 |
| `sd5_x_phi11` | 166,053 | 86,460 | 42,384 | 2,064 |
| `xpow48_minus1` | 18,071 | 13,028 | 7,083 | 3,867 |
| `xpow105_minus1` | 142,211 | 95,903 | 48,772 | 20,842 |
| `xpow120_minus1` | 127,473 | 89,910 | 48,141 | 24,501 |
| `cyclo_phi179` | 1,015,884 | 587,969 | 291,357 | 62,627 |
| `cyclo_phi64_x_phi105` | 1,413,149 | 723,226 | 355,100 | 8,060 |
| `cyclo_phi128_x_phi165` | 7,725,927 | 3,919,428 | 1,938,068 | 27,764 |
| `cyclo_phi385` | 17,647,557 | 8,975,874 | 4,446,309 | 97,269 |
| `wilkinson_40` | 1,810 | 1,807 | 1,777 | 1,777 |
| `wilkinson_48` | 2,554 | 2,551 | 2,513 | 2,513 |
| `wilkinson_56` | 3,426 | 3,423 | 3,377 | 3,377 |
| `chebyshev_T24` (control) | 14,709 | 8,826 | 4,129 | 1,081 |
| `chebyshev_U24` (control) | 13,180 | 7,993 | 3,687 | 1,071 |
| `legendre_P30` (control) | 43,334 | 23,741 | 11,552 | 1,412 |
| `legendre_P38` (control) | 104,644 | 56,191 | 27,175 | 2,323 |
| `cyclo_phi17` (control) | 5,139 | 3,296 | 1,551 | 527 |
| `cyclo_phi41` (control) | 26,424 | 17,021 | 8,397 | 3,077 |
| `xpow24_minus1` (control) | 3,338 | 2,543 | 1,470 | 942 |
| `randprod_10` (control) | 21,354 | 11,711 | 5,524 | 584 |
| `randprod_21` (control) | 37,396 | 20,041 | 9,576 | 744 |

`cyclo_phi385` goes from 17,647,557 small allocations to 97,269, a factor of
181.

## Projected end to end

Replacing each row's in-cascade row reduction and basis with the packed variant's
own measured pack, reduce, and readback times, keeping its Berlekamp matrix
construction, and leaving everything else in the cascade unchanged:

| instance | total factor now | fixed-space kernel now | packed replacement | projected total | projected gain |
|---|---:|---:|---:|---:|---:|
| `sd5` | 77.583 ms | 1.603 ms | 1.184 ms | 77.164 ms | 1.01x |
| `sd5_shift1` | 67.368 ms | 2.266 ms | 1.463 ms | 66.565 ms | 1.01x |
| `sd5_shift2` | 70.001 ms | 2.273 ms | 1.455 ms | 69.183 ms | 1.01x |
| `sd4_x_sd4shift1` | 18.966 ms | 2.284 ms | 1.482 ms | 18.164 ms | 1.04x |
| `sd5_x_phi11` | 164.715 ms | 4.649 ms | 2.575 ms | 162.641 ms | 1.01x |
| `xpow48_minus1` | 19.330 ms | 748.610 us | 671.265 us | 19.253 ms | 1.00x |
| `xpow105_minus1` | 75.332 ms | 4.948 ms | 3.845 ms | 74.228 ms | 1.01x |
| `xpow120_minus1` | 508.038 ms | 3.771 ms | 3.010 ms | 507.277 ms | 1.00x |
| `cyclo_phi179` | 74.597 ms | 14.019 ms | 5.175 ms | 65.753 ms | 1.13x |
| `cyclo_phi64_x_phi105` | 60.512 ms | 19.052 ms | 4.150 ms | 45.610 ms | 1.33x |
| `cyclo_phi128_x_phi165` | 198.630 ms | 93.260 ms | 13.429 ms | 118.799 ms | 1.67x |
| `cyclo_phi385` | 434.770 ms | 205.938 ms | 24.014 ms | 252.847 ms | 1.72x |
| `wilkinson_40` | 13.187 ms | 255.439 us | 285.761 us | 13.217 ms | 1.00x |
| `wilkinson_48` | 24.918 ms | 366.003 us | 410.329 us | 24.962 ms | 1.00x |
| `wilkinson_56` | 34.052 ms | 574.282 us | 636.393 us | 34.114 ms | 1.00x |
| `chebyshev_T24` (control) | 514.132 us | 297.961 us | 146.722 us | 362.893 us | 1.42x |
| `chebyshev_U24` (control) | 658.556 us | 246.105 us | 160.720 us | 573.171 us | 1.15x |
| `legendre_P30` (control) | 9.279 ms | 1.663 ms | 1.125 ms | 8.741 ms | 1.06x |
| `legendre_P38` (control) | 4.567 ms | 3.493 ms | 2.195 ms | 3.269 ms | 1.40x |
| `cyclo_phi17` (control) | 129.422 us | 96.343 us | 47.370 us | 80.449 us | 1.61x |
| `cyclo_phi41` (control) | 2.795 ms | 455.666 us | 253.663 us | 2.593 ms | 1.08x |
| `xpow24_minus1` (control) | 3.226 ms | 192.846 us | 178.395 us | 3.212 ms | 1.00x |
| `randprod_10` (control) | 777.673 us | 430.878 us | 176.313 us | 523.108 us | 1.49x |
| `randprod_21` (control) | 1.697 ms | 1.007 ms | 537.259 us | 1.228 ms | 1.38x |

The four named cyclotomic rows gain 1.13x to 1.72x. The worst row is
`wilkinson_40` at 1.00x.

This projection substitutes an absolute packed time measured in the kernel
section for an absolute generic time measured in the scout section. Those two
sections do not run adjacently, and the scout section measures the same
computation at 0.64x to 0.98x of what the kernel section measures for it
(median 0.84x), the gap widening with allocation volume, because the kernel
section has already run several full reductions and its heap is larger.
Since the generic path allocates two orders of magnitude more than the packed
path, that degradation should hurt the generic path more, so substituting the
packed absolute -- rather than scaling by a cross-section ratio -- is the
conservative reading of the two. It is still a model, not a measurement of an
integrated implementation.

## What the measurements do not establish

- **The two sections are not paired.** The threshold table's numerator and
  denominator come from different services run minutes apart on a shared host.
  The same computation costs 0.64x to 0.98x as much in one section as the
  other, which bounds how much that matters; the large cyclotomic margins
  survive it, the marginal rows are not decided by it.
- **The medians are field-wise.** Each duration is the median of three calls,
  merged field by field, so a reported ratio can combine numerator and
  denominator from different executions and no variance is reported. With three
  repeats there is no useful confidence interval.
- **The prototype is not a production-shaped function.** It uses `Array.get!`
  and `Array.set!` and carries no correspondence proof. The proof obligations
  need not cost runtime, but this has not been demonstrated by benchmarking a
  compiled function that carries them.
- **The corpus moduli are small.** Every selected prime here is between 3 and 79,
  far from the `2^31` bound the representation must support. Arithmetic
  behaviour, and in particular the reciprocal-versus-remainder comparison, may
  differ near that bound.
- **Ordering is fixed.** Generic variants always run before packed ones inside a
  call. Whether that favours or penalizes the packed variants is not established,
  and no counterbalancing was done.

## Verdict, and the design it implies

**Go.** The threshold is met with margin on the rows that matter, and the ceiling
is large enough to matter end to end. The specific factors below should be
re-measured against the real integrated implementation before they are quoted as
outcomes.

1. **Build the packed matrix from the column polynomials, not from
   `Hex.Matrix`.** The conversion stage is 1.256 ms on `cyclo_phi385` and the
   pack step 2.819 ms; writing the columns straight into the packed buffer
   removes both, and removes the small-matrix overhead that is the only place
   this change costs anything.
2. **Store `UInt32` entries.** `ZMod64.Bounds` already caps the modulus at
   `2^31`, and an immediate `UInt32` stops the inner loop allocating. That is
   2.42x here. It is a property of the 64-bit runtime's boxing rules, not of
   storage density, and it should be re-checked if that changes.
3. **Do not compute the transform.** Berlekamp needs rank, echelon, and pivot
   columns. This is 2.00x on its own, needs no change of representation, and
   is the cheapest part of the change to justify.
4. **Specialize the whole reduction loop**, not a chosen subset: pivot search,
   swap, scale, elimination, and the basis readback. Pivot search is negligible
   *now*, but swap and scale are 3.926 ms on `cyclo_phi385` against a packed
   reduction of 15.761 ms, so anything left generic dominates what remains
   once row addition is specialized.
5. **Treat the Barrett reciprocal as an open question, and default to leaving it
   out.** It measures 1.01x against a hardware remainder on this corpus, but the
   corpus moduli are tiny, three fixed-order repeats do not resolve differences
   this small, and the prototype's modular inversion still uses the reciprocal
   internally, so this is not a clean comparison. Leaving it out is a simplicity
   default that also keeps its proof obligations out of the correspondence; it is
   not a measured result.
6. **Take the zero-entry skip separately.** It is worth 1.70x on `cyclo_phi385`,
   it is orthogonal to the representation, and the generic path could adopt it
   too. It should be decided on its own evidence, including on dense matrices
   where it buys nothing.

The correspondence obligation is narrow: a packed buffer, an interpretation into
`Matrix (ZMod64 p) n n`, entry agreement, one lemma per elementary operation, and
a simulation of the Gauss-Jordan loop, landing on a single equality at the
`fixedSpaceKernelVectors` boundary so that the Berlekamp development keeps
reasoning about ordinary matrices.

## Regeneration

```sh
lake build hexbz_factor_service
python3 scripts/bench/factor_phase_profile.py \
  --output reports/bench-results/hexbz-phase-profile-47aa7048-chungus2.json
```

The driver pins itself to an idle core and exits non-zero if the counted mirror
disagrees with the production row reduction, if any packed variant disagrees with
`Hex.Matrix.nullspace`, if a scouted degree pattern disagrees with its split, or
if the recombination mirror disagrees with the production trace.
