# A packed finite-field matrix for Berlekamp's fixed space (issue #9132)

Issue #9128 replaced the prime planner's repeated full splitting with a bounded
degree-pattern scout, so the modular share of a factorization had to be
remeasured before any matrix specialization was justified. This page is that
remeasurement, and it is a **go**.

**The numbers below price a benchmark prototype, not shipped code.** The
specialization they justified has since landed;
[reports/hexbz-packed-fp-matrix-integration.md](hexbz-packed-fp-matrix-integration.md)
measures the implementation, and its factors are the ones to quote.

On `cyclo_phi385` the row reduction and nullspace basis at the selected prime
are **46.5% of total factor time** and **94.6% of that prime's Berlekamp
split**; on `cyclo_phi128_x_phi165`, 44.6% and 89.3%; on
`cyclo_phi64_x_phi105`, 29.2% and 79.2%. Issue #9132 asks for 25% of total factor
time on a material row, or 40% of its selected-prime Berlekamp time; 9 of
24 rows clear the first and 11 of 24 clear the second.

The numerator here is deliberately **the row reduction and basis alone**, not
the whole modular kernel. Berlekamp matrix construction is a polynomial
computation -- one Frobenius power and `n` products with monic reductions --
that a packed matrix representation does not accelerate, so counting it would
inflate the share of exactly the work under discussion. The in-cascade
measurement gives the whole kernel in one span, so the construction fraction is
taken from the kernel section, which times the build on its own; both columns
are shown. That correction is small on the large cyclotomic rows (2.9% of the
kernel on `cyclo_phi385`) and large on the small ones (57.3% on `legendre_P38`).

Inside that share the cost is one stage. On `cyclo_phi385`, row addition is
302.049 ms of the 306.315 ms Gauss-Jordan run; pivot search is 6.506 us, the nullspace
basis 1.987 ms, and the conversion of basis vectors back to polynomials
7.290 us.

A prototype packed representation -- one contiguous row-major buffer with the
modulus held in a machine-word local -- was measured against the generic path on
the same matrices in the same process, and checked entry for entry against
`Hex.Matrix.nullspace` on all 24 instances. It reduces `cyclo_phi385`'s row
reduction from 312.206 ms to 15.606 ms, a **17.0x** speedup including the
cost of packing, and projects a **1.73x** end-to-end improvement on that row.

Every number here is reproducible from the committed record by the commands in
[Regeneration](#regeneration). Section
[What the measurements do not establish](#what-the-measurements-do-not-establish)
states the limits of the evidence, and they are not small.

## Revision and protocol

- Source revision `0e1601a01e2590755d0664f64db96c8b73e8d2b6` (clean worktree),
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
| `reports/bench-results/hexbz-phase-profile-0e1601a0-chungus2.json` | `2048c0f8337a51a4b85b164c0779715596e0348005cf86ee0e498a136b0bdb61` |

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
  production row reduction with a median ratio of **1.019** across all 24
  rows, minimum 0.845 and maximum 1.180; the per-row ratios are in the
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

`Berlekamp split` is a full `berlekampFactor` at the selected prime, timed
in-cascade by the scout section, and `total factor` is the phase profile's own
total for the production cascade. `fixed-space kernel` is the split times the
kernel's share of it, that share being a ratio between two spans of the same
kernel-section execution; `construction` and `reduction + basis` then divide it
by the construction share the kernel section measures, because a packed
representation accelerates only the second.

Estimating the numerator as a within-section *share* of one in-cascade absolute,
rather than as a span differenced across the two sections, is what keeps it
robust: the scout section's own `berlekampMatrix` span measures nothing, because
its matrix build is a pure `let` that the compiler moves down into
`Matrix.nullspace`, and on a contended run its `rowReduction` span has been
observed exceeding the split that contains it. A share cannot exceed one.

Planning overhead is excluded throughout: these are costs at the *selected*
prime, not costs of the walk.

| instance | matrix | prime | total factor | fixed-space kernel | construction | reduction + basis | share of total | Berlekamp split | share of split |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32x32 | 29 | 78.761 ms | 1.691 ms | 1.169 ms | 521.550 us | 0.7% | 3.564 ms | 14.6% |
| `sd5_shift1` | 32x32 | 29 | 66.494 ms | 2.411 ms | 1.437 ms | 974.421 us | 1.5% | 3.691 ms | 26.4% |
| `sd5_shift2` | 32x32 | 29 | 70.635 ms | 2.493 ms | 1.474 ms | 1.019 ms | 1.4% | 5.209 ms | 19.6% |
| `sd4_x_sd4shift1` | 32x32 | 29 | 19.289 ms | 2.476 ms | 1.486 ms | 989.042 us | 5.1% | 4.511 ms | 21.9% |
| `sd5_x_phi11` | 42x42 | 29 | 167.727 ms | 5.057 ms | 2.514 ms | 2.543 ms | 1.5% | 9.135 ms | 27.8% |
| `xpow48_minus1` | 48x48 | 11 | 19.170 ms | 791.569 us | 529.559 us | 262.009 us | 1.4% | 2.121 ms | 12.4% |
| `xpow105_minus1` | 105x105 | 17 | 74.664 ms | 5.399 ms | 3.404 ms | 1.995 ms | 2.7% | 10.040 ms | 19.9% |
| `xpow120_minus1` | 120x120 | 7 | 481.771 ms | 4.332 ms | 2.452 ms | 1.880 ms | 0.4% | 17.266 ms | 10.9% |
| `cyclo_phi179` | 178x178 | 3 | 74.012 ms | 14.154 ms | 2.537 ms | 11.616 ms | 15.7% | 14.914 ms | 77.9% |
| `cyclo_phi64_x_phi105` | 80x80 | 11 | 60.451 ms | 20.371 ms | 2.717 ms | 17.654 ms | 29.2% | 22.284 ms | 79.2% |
| `cyclo_phi128_x_phi165` | 144x144 | 7 | 197.342 ms | 93.463 ms | 5.522 ms | 87.942 ms | 44.6% | 98.462 ms | 89.3% |
| `cyclo_phi385` | 240x240 | 3 | 435.313 ms | 208.320 ms | 6.110 ms | 202.210 ms | 46.5% | 213.642 ms | 94.6% |
| `wilkinson_40` | 40x40 | 47 | 13.242 ms | 267.834 us | 219.923 us | 47.910 us | 0.4% | 1.812 ms | 2.6% |
| `wilkinson_48` | 48x48 | 61 | 24.782 ms | 373.204 us | 308.703 us | 64.500 us | 0.3% | 2.868 ms | 2.2% |
| `wilkinson_56` | 56x56 | 67 | 34.025 ms | 592.766 us | 504.498 us | 88.267 us | 0.3% | 4.350 ms | 2.0% |
| `chebyshev_T24` (control) | 24x24 | 5 | 525.139 us | 302.272 us | 102.637 us | 199.634 us | 38.0% | 334.546 us | 59.7% |
| `chebyshev_U24` (control) | 24x24 | 3 | 660.189 us | 261.503 us | 77.019 us | 184.483 us | 27.9% | 322.508 us | 57.2% |
| `legendre_P30` (control) | 30x30 | 67 | 9.251 ms | 1.782 ms | 1.096 ms | 685.461 us | 7.4% | 2.358 ms | 29.1% |
| `legendre_P38` (control) | 38x38 | 79 | 4.651 ms | 3.615 ms | 2.072 ms | 1.543 ms | 33.2% | 3.810 ms | 40.5% |
| `cyclo_phi17` (control) | 16x16 | 3 | 128.981 us | 98.266 us | 28.853 us | 69.412 us | 53.8% | 98.266 us | 70.6% |
| `cyclo_phi41` (control) | 40x40 | 3 | 2.793 ms | 508.266 us | 162.268 us | 345.997 us | 12.4% | 692.236 us | 50.0% |
| `xpow24_minus1` (control) | 24x24 | 11 | 3.221 ms | 209.157 us | 157.679 us | 51.477 us | 1.6% | 623.364 us | 8.3% |
| `randprod_10` (control) | 20x20 | 7 | 767.318 us | 452.393 us | 139.869 us | 312.523 us | 40.7% | 545.189 us | 57.3% |
| `randprod_21` (control) | 24x24 | 17 | 1.686 ms | 1.048 ms | 484.168 us | 564.252 us | 33.5% | 1.227 ms | 46.0% |

9 of 24 rows clear the 25%-of-total bar and 11 of 24 clear the 40%-of-split
bar. Three of the four named cyclotomic rows clear the first; the fourth,
`cyclo_phi179` at 15.7%, clears the second at 77.9%.

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
| `sd5` | 1.157 ms | 107.490 us | 0 ns | 854 ns | 37.755 us | 501.365 us | 35.663 us | 4.627 us | 31,866 |
| `sd5_shift1` | 1.541 ms | 22.654 us | 17.055 us | 802 ns | 36.523 us | 1.042 ms | 54.772 us | 4.707 us | 62,044 |
| `sd5_shift2` | 1.536 ms | -25.357 us | 10.947 us | 761 ns | 36.686 us | 1.051 ms | 48.032 us | 4.667 us | 62,818 |
| `sd4_x_sd4shift1` | 1.526 ms | 22.703 us | 14.783 us | 812 ns | 36.343 us | 1.015 ms | 50.516 us | 4.687 us | 61,400 |
| `sd5_x_phi11` | 2.711 ms | 34.981 us | 26.078 us | 1.071 us | 73.059 us | 2.688 ms | 80.480 us | 5.468 us | 166,053 |
| `xpow48_minus1` | 457.759 us | 48.693 us | 39.367 us | 1.260 us | 93.158 us | 174.253 us | 59.479 us | 7.110 us | 18,071 |
| `xpow105_minus1` | 3.183 ms | 254.406 us | 175.911 us | 2.696 us | 620.644 us | 1.588 ms | 210.803 us | 7.481 us | 142,211 |
| `xpow120_minus1` | 1.974 ms | 357.841 us | 191.393 us | 3.008 us | 635.372 us | 1.295 ms | 439.713 us | 28.703 us | 127,473 |
| `cyclo_phi179` | 2.371 ms | 706.376 us | 519.121 us | 4.608 us | 2.016 ms | 14.485 ms | 393.314 us | 3.486 us | 1,015,884 |
| `cyclo_phi64_x_phi105` | 3.500 ms | 142.782 us | 98.366 us | 2.122 us | 374.437 us | 23.641 ms | -15.423 us | 4.276 us | 1,413,149 |
| `cyclo_phi128_x_phi165` | 7.309 ms | 406.364 us | 426.512 us | 3.898 us | 1.341 ms | 127.162 ms | 517.917 us | 6.470 us | 7,725,927 |
| `cyclo_phi385` | 6.412 ms | 1.362 ms | 2.061 ms | 6.506 us | 4.188 ms | 302.049 ms | 1.987 ms | 7.290 us | 17,647,557 |
| `wilkinson_40` | 72.768 us | 34.171 us | 26.249 us | 1.002 us | 0 ns | 0 ns | 41.673 us | 19.038 us | 1,810 |
| `wilkinson_48` | 102.151 us | 49.463 us | 39.169 us | 1.163 us | 0 ns | 0 ns | 54.471 us | 26.799 us | 2,554 |
| `wilkinson_56` | 139.397 us | 67.902 us | 54.971 us | 1.322 us | 0 ns | 0 ns | 73.179 us | 35.052 us | 3,426 |
| `chebyshev_T24` (control) | 106.458 us | 12.147 us | 11.607 us | 621 ns | 38.325 us | 225.325 us | 10.936 us | 1.192 us | 14,709 |
| `chebyshev_U24` (control) | 69.793 us | 12.519 us | 10.636 us | 631 ns | 35.613 us | 203.171 us | 11.407 us | 1.262 us | 13,180 |
| `legendre_P30` (control) | 1.094 ms | 20.280 us | 19.999 us | 780 ns | 50.318 us | 718.353 us | 24.256 us | 1.993 us | 43,334 |
| `legendre_P38` (control) | 2.210 ms | 28.172 us | 27.211 us | 992 ns | 93.829 us | 1.720 ms | 21.012 us | 1.342 us | 104,644 |
| `cyclo_phi17` (control) | 25.748 us | 5.609 us | 5.359 us | 409 ns | 19.349 us | 74.170 us | -1.031 us | 611 ns | 5,139 |
| `cyclo_phi41` (control) | 139.387 us | 29.523 us | 26.690 us | 1.052 us | 98.786 us | 334.674 us | 29.664 us | 1.663 us | 26,424 |
| `xpow24_minus1` (control) | 129.342 us | 11.678 us | 11.095 us | 600 ns | 19.730 us | 30.766 us | 16.285 us | 3.455 us | 3,338 |
| `randprod_10` (control) | 154.178 us | 7.111 us | 7.871 us | 490 ns | 24.527 us | 364.954 us | 12.519 us | 1.011 us | 21,354 |
| `randprod_21` (control) | 521.533 us | 12.008 us | 13.280 us | 582 ns | 30.384 us | 631.849 us | 22.915 us | 1.763 us | 37,396 |

Row addition is the whole cost. On `cyclo_phi385` it is 98.6% of the Gauss-Jordan
run; pivot search is 6.506 us, four orders of magnitude below it, and the two
conversions plus the basis and its polynomial readback come to
5.418 ms against 302.049 ms. Column construction is 6.412 ms and becomes the
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
of entries are zero, and skipping them is worth 1.69x on its own. All four
compute the rank and the full nullspace basis and all four are checked against
`Hex.Matrix.nullspace`. `speedup` is the production row reduction against packing
plus reducing.

| instance | generic, with transform | mirror / production | generic, echelon only | immediate `UInt64` | immediate `UInt32` | `UInt32`, hardware `%` | speedup | `UInt32`, zero-skip |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 548.934 us | 1.018 | 321.257 us | 68.722 us | 37.155 us | 34.692 us | 7.0x | 24.886 us |
| `sd5_shift1` | 1.085 ms | 1.010 | 611.126 us | 122.011 us | 60.429 us | 61.221 us | 10.7x | 51.266 us |
| `sd5_shift2` | 1.100 ms | 1.006 | 613.290 us | 124.164 us | 61.481 us | 61.601 us | 10.7x | 51.847 us |
| `sd4_x_sd4shift1` | 1.059 ms | 1.009 | 596.795 us | 121.049 us | 59.618 us | 60.480 us | 10.5x | 51.397 us |
| `sd5_x_phi11` | 2.832 ms | 0.984 | 1.523 ms | 326.655 us | 155.570 us | 158.795 us | 12.3x | 136.682 us |
| `xpow48_minus1` | 275.128 us | 1.095 | 225.904 us | 42.954 us | 28.192 us | 27.361 us | 2.2x | 24.817 us |
| `xpow105_minus1` | 2.142 ms | 1.091 | 1.583 ms | 318.032 us | 187.638 us | 185.995 us | 3.1x | 155.080 us |
| `xpow120_minus1` | 1.944 ms | 1.097 | 1.493 ms | 293.705 us | 176.211 us | 175.120 us | 2.3x | 150.744 us |
| `cyclo_phi179` | 16.470 ms | 1.024 | 9.757 ms | 2.162 ms | 1.067 ms | 1.078 ms | 6.4x | 721.690 us |
| `cyclo_phi64_x_phi105` | 24.487 ms | 0.984 | 12.671 ms | 2.805 ms | 1.271 ms | 1.313 ms | 15.7x | 1.004 ms |
| `cyclo_phi128_x_phi165` | 129.762 ms | 0.993 | 64.723 ms | 15.351 ms | 6.857 ms | 6.971 ms | 16.5x | 5.052 ms |
| `cyclo_phi385` | 312.206 ms | 0.983 | 157.651 ms | 37.644 ms | 15.606 ms | 15.918 ms | 17.0x | 9.249 ms |
| `wilkinson_40` | 47.370 us | 0.845 | 41.972 us | 4.787 us | 4.577 us | 4.146 us | 0.7x | 4.106 us |
| `wilkinson_48` | 64.405 us | 0.859 | 58.977 us | 6.840 us | 6.039 us | 5.629 us | 0.6x | 5.588 us |
| `wilkinson_56` | 88.131 us | 0.849 | 79.038 us | 8.603 us | 8.252 us | 7.732 us | 0.6x | 7.642 us |
| `chebyshev_T24` (control) | 255.548 us | 1.068 | 169.301 us | 32.248 us | 19.108 us | 18.738 us | 6.2x | 14.722 us |
| `chebyshev_U24` (control) | 226.596 us | 1.098 | 152.076 us | 28.202 us | 17.045 us | 16.434 us | 5.8x | 12.889 us |
| `legendre_P30` (control) | 768.340 us | 1.020 | 446.432 us | 90.203 us | 46.759 us | 46.498 us | 9.3x | 33.340 us |
| `legendre_P38` (control) | 1.797 ms | 1.022 | 1.035 ms | 210.131 us | 106.959 us | 107.500 us | 10.8x | 72.798 us |
| `cyclo_phi17` (control) | 92.757 us | 1.064 | 64.817 us | 12.758 us | 8.523 us | 7.721 us | 5.4x | 6.339 us |
| `cyclo_phi41` (control) | 419.953 us | 1.080 | 295.378 us | 57.325 us | 35.602 us | 35.081 us | 4.1x | 28.833 us |
| `xpow24_minus1` (control) | 52.087 us | 1.180 | 47.811 us | 9.234 us | 6.951 us | 6.239 us | 1.8x | 5.859 us |
| `randprod_10` (control) | 385.962 us | 1.028 | 231.263 us | 43.584 us | 22.724 us | 22.774 us | 10.4x | 18.097 us |
| `randprod_21` (control) | 662.011 us | 1.014 | 382.567 us | 74.501 us | 37.155 us | 37.135 us | 11.2x | 31.086 us |

The win decomposes on `cyclo_phi385`:

| step | time | factor |
|---|---:|---:|
| production `Hex.Matrix.rowReduce` | 312.206 ms | -- |
| drop the transform the nullspace never reads | 157.651 ms | 1.98x |
| contiguous buffer, modulus in a machine-word local | 37.644 ms | 4.19x |
| immediate `UInt32` entries instead of boxed `UInt64` | 15.606 ms | 2.41x |
| Barrett reciprocal instead of hardware remainder | 15.918 ms | 1.02x |
| *(separately)* skipping zero source entries | 9.249 ms | 1.69x |

Two of these deserve comment.

**The transform is half the elementary-operation work, and it is dead.**
`Hex.Matrix.rowReduce` maintains an `n x n` transform `T` with `T * M = echelon`
in lockstep with the echelon form, applying every swap, scale, and row addition
twice. `Hex.Matrix.nullspace` reads only `rank`, `echelon`, and `pivotCols`. That
factor of 1.98 is available without any change of representation.

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
| `sd5` | 78.761 ms | 1.691 ms | 1.251 ms | 78.322 ms | 1.01x |
| `sd5_shift1` | 66.494 ms | 2.411 ms | 1.541 ms | 65.624 ms | 1.01x |
| `sd5_shift2` | 70.635 ms | 2.493 ms | 1.579 ms | 69.721 ms | 1.01x |
| `sd4_x_sd4shift1` | 19.289 ms | 2.476 ms | 1.590 ms | 18.403 ms | 1.05x |
| `sd5_x_phi11` | 167.727 ms | 5.057 ms | 2.748 ms | 165.419 ms | 1.01x |
| `xpow48_minus1` | 19.170 ms | 791.569 us | 660.313 us | 19.039 ms | 1.01x |
| `xpow105_minus1` | 74.664 ms | 5.399 ms | 4.115 ms | 73.380 ms | 1.02x |
| `xpow120_minus1` | 481.771 ms | 4.332 ms | 3.323 ms | 480.762 ms | 1.00x |
| `cyclo_phi179` | 74.012 ms | 14.154 ms | 5.152 ms | 65.010 ms | 1.14x |
| `cyclo_phi64_x_phi105` | 60.451 ms | 20.371 ms | 4.283 ms | 44.364 ms | 1.36x |
| `cyclo_phi128_x_phi165` | 197.342 ms | 93.463 ms | 13.395 ms | 117.274 ms | 1.68x |
| `cyclo_phi385` | 435.313 ms | 208.320 ms | 24.557 ms | 251.550 ms | 1.73x |
| `wilkinson_40` | 13.242 ms | 267.834 us | 293.863 us | 13.268 ms | 1.00x |
| `wilkinson_48` | 24.782 ms | 373.204 us | 416.513 us | 24.825 ms | 1.00x |
| `wilkinson_56` | 34.025 ms | 592.766 us | 652.026 us | 34.084 ms | 1.00x |
| `chebyshev_T24` (control) | 525.139 us | 302.272 us | 145.020 us | 367.887 us | 1.43x |
| `chebyshev_U24` (control) | 660.189 us | 261.503 us | 117.519 us | 516.205 us | 1.28x |
| `legendre_P30` (control) | 9.251 ms | 1.782 ms | 1.181 ms | 8.651 ms | 1.07x |
| `legendre_P38` (control) | 4.651 ms | 3.615 ms | 2.240 ms | 3.276 ms | 1.42x |
| `cyclo_phi17` (control) | 128.981 us | 98.266 us | 46.569 us | 77.284 us | 1.67x |
| `cyclo_phi41` (control) | 2.793 ms | 508.266 us | 266.842 us | 2.552 ms | 1.09x |
| `xpow24_minus1` (control) | 3.221 ms | 209.157 us | 188.055 us | 3.200 ms | 1.01x |
| `randprod_10` (control) | 767.318 us | 452.393 us | 178.205 us | 493.130 us | 1.56x |
| `randprod_21` (control) | 1.686 ms | 1.048 ms | 544.638 us | 1.182 ms | 1.43x |

The four named cyclotomic rows gain 1.14x to 1.73x. The worst row is
`wilkinson_40` at 1.00x.

This projection substitutes an absolute packed time measured in the kernel
section for an absolute generic time measured in the scout section. Those two
sections do not run adjacently, and the scout section measures the same
computation at 0.67x to 1.00x of what the kernel section measures for it
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
  The same computation costs 0.67x to 1.00x as much in one section as the
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
   `Hex.Matrix`.** The conversion stage is 1.362 ms on `cyclo_phi385` and the
   pack step 2.800 ms; writing the columns straight into the packed buffer
   removes both, and removes the small-matrix overhead that is the only place
   this change costs anything.
2. **Store `UInt32` entries.** `ZMod64.Bounds` already caps the modulus at
   `2^31`, and an immediate `UInt32` stops the inner loop allocating. That is
   2.41x here. It is a property of the 64-bit runtime's boxing rules, not of
   storage density, and it should be re-checked if that changes.
3. **Do not compute the transform.** Berlekamp needs rank, echelon, and pivot
   columns. This is 1.98x on its own, needs no change of representation, and
   is the cheapest part of the change to justify.
4. **Specialize the whole reduction loop**, not a chosen subset: pivot search,
   swap, scale, elimination, and the basis readback. Pivot search is negligible
   *now*, but swap and scale are 4.188 ms on `cyclo_phi385` against a packed
   reduction of 15.606 ms, so anything left generic dominates what remains
   once row addition is specialized.
5. **Treat the Barrett reciprocal as an open question, and default to leaving it
   out.** It measures 1.02x against a hardware remainder on this corpus, but the
   corpus moduli are tiny, three fixed-order repeats do not resolve differences
   this small, and the prototype's modular inversion still uses the reciprocal
   internally, so this is not a clean comparison. Leaving it out is a simplicity
   default that also keeps its proof obligations out of the correspondence; it is
   not a measured result.
6. **Take the zero-entry skip separately.** It is worth 1.69x on `cyclo_phi385`,
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
  --output reports/bench-results/hexbz-phase-profile-0e1601a0-chungus2.json
```

The driver pins itself to an idle core and exits non-zero if the counted mirror
disagrees with the production row reduction, if any packed variant disagrees with
`Hex.Matrix.nullspace`, if a scouted degree pattern disagrees with its split, or
if the recombination mirror disagrees with the production trace.
