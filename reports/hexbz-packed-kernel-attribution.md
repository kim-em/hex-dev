# Where the integrated packed kernel's time goes (issue #9160)

[reports/hexbz-packed-fp-matrix-integration.md](hexbz-packed-fp-matrix-integration.md)
measured the landed packed kernel at **2.6x slower than the benchmark prototype
it was derived from**, on the same matrix, in the same process, performing the
same 17,948 row additions, and named candidate causes by inspection. This page
measures them, one at a time, against a named baseline each.

**One cause is 68% of the reduction; every other candidate is under 1%, and one
of them is a saving rather than a cost.** `Hex.Matrix.rowAdd` reads the source
row out with `Hex.Matrix.getRow` before writing, once per row addition. On
`cyclo_phi385` that copy is **31.378 ms of a 44.596 ms reduction, 70.4%**; on
`cyclo_phi128_x_phi165`, 14.370 ms of 20.087 ms, **71.5%**; on the small
`randprod_21`, 67.320 us of 105.736 us, **63.7%**. Amortizing it to one read per
pivot column, which is sound because the pivot row does not change while its
column is eliminated, leaves a reduction that is **0.82x to 0.83x the prototype's** on
the two heaviest rows.

Of the other candidates, measured one at a time against the same loop:
`Hex.Matrix.modifyEntries`'s `Fin.foldl` closure is **2.5% faster** than a flat
`Nat`-indexed write, not slower; the `List (Fin m)` pivot accumulation is
**0.2%**; and the `List.finRange n` elimination scan is **1.0%** on
`cyclo_phi385` but **21%** on `xpow105_minus1`, whose reduction is dominated by
already-zero columns rather than by arithmetic.

The inner modular multiply is an incremental **4.9% of the integrated reduction**
on `cyclo_phi385` and 16.6% of the copy-free one. Of the two open design points,
the entry width is settled and the reciprocal is measured at 1.4% to 2.2% where
it resolves; see [The two open design points](#the-two-open-design-points).

Nothing here is an optimization. The ladder rungs live in the bench module and
nothing reachable from `Hex.ZPoly.factorize` calls them.

## Revision and protocol

- Source revision `d01c714696f2d32b88c307dae31831bb1037a938` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured 2026-08-04.
  The host was shared with other work throughout. The driver pins itself to one
  idle logical CPU before spawning any service.
- Record `reports/bench-results/hexbz-phase-profile-d01c7146-chungus2.json`,
  SHA-256
  `2e726ea18cc81f5759ca1cdae6e10726df859b6ed3eb193a3c761d337f003a8d`;
  `hexbz_factor_service` SHA-256
  `08e97cd78d046896181f7af216717505c67c01354c30b1055e685491e0781779`; corpus
  `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- **Eight repeats per instance, in one process, with the ladder rungs and the
  prototype variants both run in alternating directions** (recorded per repeat
  as `ladderForward`, `[true, false, true, false, ...]`, so the four forward and
  four reverse calls are balanced under a median). Every rung's and every
  variant's reduction is kept per repeat in `reduceNanosSamples`, so **every
  difference below is a median of within-repeat paired differences**, reported
  with the full range of those eight differences. A range that crosses zero
  means the protocol does not resolve that effect on that row, and that is said
  rather than rounded to "free".
- **Every rung, the stage mirror and the four prototype variants are compared
  against `Hex.Matrix.nullspace` on all 24 rows, and the driver exits non-zero
  on any disagreement**; this run agreed on 24 of 24. Every deterministic count
  and rank the kernel record carries is asserted equal across the eight repeats
  before any duration is merged.

Unlike the integration report, every comparison here is *within one run*: the
ladder rungs, the stage mirror and the prototype variants are priced back to
back in the same process on the same instance.

## How the attribution works

Three instruments, all in `bench/HexBench/BerlekampKernel.lean`.

**The stage mirror.** `countedPackedReduce` mirrors
`Hex.Berlekamp.Packed.reduceLoop` column for column, calling the production
`Packed.findPivot?`, `Matrix.rowSwap`, `Packed.rowScale`, `Packed.invMod` and
`Packed.eliminateColumn`, and reads the clock once per pivot column. It is
checked against the production `Packed.reduce` on every call, on echelon buffer
and pivot-column list.

**The comparison graph.** `ladderLoop` is the same loop with its column
elimination passed in as an argument, called once per pivot column and never in
the inner loop. **The rungs are a graph, not a chain**: each names its own
baseline, and the differences do not sum.

| rung | baseline | what changes |
|---|---|---|
| `integrated` | -- | nothing: `Hex.Berlekamp.Packed.reduce` itself, no mirror, no parameter |
| `mirrored` | `integrated` | `Packed.eliminateColumn` runs through `ladderLoop` instead of `Packed.reduceLoop`. The control for the ladder's own scaffolding |
| `hoistedPivotRow` | `mirrored` | the pivot row is read once per column instead of once per row addition |
| `arrayPivots` | `hoistedPivotRow` | the pivot columns accumulate in an `Array` with `push` rather than a `List` with `concat` |
| `flatRowWrite` | `hoistedPivotRow` | the destination row is written by a `Nat`-indexed loop over the flat buffer rather than by `Matrix.modifyEntries`'s `Fin.foldl`. **The outer scan and the pivot list are unchanged** |
| `flatBothLoops` | `flatRowWrite` | the outer column scan is a `Nat` range rather than `List.finRange n` |
| `flatBuffer` | `flatBothLoops` | the prototype's `reduce32` on the packed buffer: pivot search, swap, scale, inversion, pivot storage and pivot-row access change at once. **A residual comparison, not an attribution** |

`integrated` against `mirrored` is the control for the ladder's own loop, and
every ladder difference is taken against `mirrored` or below, never against
`integrated`, so the ladder's overhead cancels.

**The multiply.** Three bodies, in each of two loop shapes (the `modifyEntries`
shape of `eliminateHoisted`, and the flat shape of `eliminateFlat`):

- `salted` performs the multiply on an operand salted by a runtime zero read
  from an `IO.Ref`;
- `saltedMin` performs the same multiply, then increments the product by the
  same runtime zero and selects the smaller of the two;
- `doubled` performs a **second modular multiply** where `saltedMin` performs
  the increment, and selects between the two products.

All three compute the same reduction, checked entry for entry like every other
rung, because the salt is zero; the compiler cannot see that, so no product is
folded away as a common subexpression, and the generated C for `doubled` does
contain two `lean_uint64_mod` calls. `doubled - saltedMin` is therefore one
modular multiply against one `UInt32` addition, per inner-loop entry.
`saltedMin - salted` prices the select together with that addition, and it is
**not small** -- see the multiply section -- which is why it is subtracted
rather than left inside the multiply's number.

### The five traps

- **Let-floating.** This one bit. The first version of the stage mirror charged
  236 columns of elimination **11 us against a 46 ms wall**: `let e :=
  eliminateColumn ...` is consumed only by the tail call, so the compiler moved
  it past the clock read. The mirror now pushes an entry of the eliminated
  buffer into an `IO.Ref` before reading the clock. The generic
  `countedRowReduce` never had the problem because its elimination returns a
  pair and the destructuring pattern match cannot be floated.
- **CSE through a scalar forcing barrier.** Each force carries a
  runtime-varying operand, `probePacked`'s `salt`, for the reason `probeEntry`
  documents. Every rung's pre-mark force is the same expression, one packed
  entry, so no rung's timed span carries a different forcing cost.
- **Aliasing.** Every rung, the stage mirror and every prototype variant get
  their own freshly built buffer. `Matrix.getRow` materializes a new vector, so
  a hoisted source row does not share the matrix's backing buffer, and the
  bottom rung consumes `A.data.toArray` without retaining `A`.
- **The length index.** No rung mentions
  `basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)`; the pivot
  columns are carried as a list or array and the basis as a plain `Array`.
- **Marking inside the elimination loop.** Marks are taken once per pivot
  column, never per row operation. On rows where a column's work is under a
  microsecond this is what shows up as the residual; see below.

## The stage split

`wall` is the mirror's own reduction span; `staged` is the sum of the three
stages the production loop has. The `O(n)` pass that counts how many row
additions the next stage will perform is **instrument, not a production stage**,
so it is marked and reported on its own rather than charged to swap-and-scale.
The residual is `wall - staged - count`: the loop's recursion, its counter
records, and the clock reads themselves.

| instance | n | p | pivot search | swap + scale | eliminate | staged | count (instrument) | wall | residual |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32 | 29 | 847 ns | 4.616 us | 83.964 us | 89.447 us | 7.163 us | 99.502 us | 2.91% |
| `sd5_shift1` | 32 | 29 | 827 ns | 4.435 us | 168.305 us | 173.598 us | 7.055 us | 183.522 us | 1.56% |
| `sd5_shift2` | 32 | 29 | 825 ns | 4.509 us | 170.673 us | 175.962 us | 6.974 us | 186.171 us | 1.74% |
| `sd4_x_sd4shift1` | 32 | 29 | 810 ns | 4.564 us | 164.475 us | 169.928 us | 7.170 us | 180.072 us | 1.65% |
| `sd5_x_phi11` | 42 | 29 | 1.182 us | 8.063 us | 441.440 us | 450.643 us | 13.588 us | 468.384 us | 0.89% |
| `xpow48_minus1` | 48 | 11 | 1.286 us | 9.888 us | 35.609 us | 46.793 us | 17.120 us | 68.686 us | 6.95% |
| `xpow105_minus1` | 105 | 17 | 2.659 us | 54.036 us | 291.265 us | 347.824 us | 103.913 us | 466.351 us | 3.13% |
| `xpow120_minus1` | 120 | 7 | 3.071 us | 55.422 us | 248.724 us | 307.401 us | 103.790 us | 429.401 us | 4.24% |
| `cyclo_phi179` | 178 | 3 | 4.699 us | 164.013 us | 2.424 ms | 2.594 ms | 326.468 us | 2.976 ms | 1.87% |
| `cyclo_phi64_x_phi105` | 80 | 11 | 2.165 us | 33.890 us | 3.816 ms | 3.852 ms | 68.842 us | 3.937 ms | 0.39% |
| `cyclo_phi128_x_phi165` | 144 | 7 | 4.008 us | 107.075 us | 19.944 ms | 20.055 ms | 233.459 us | 20.332 ms | 0.21% |
| `cyclo_phi385` | 240 | 3 | 6.560 us | 295.605 us | 44.271 ms | 44.572 ms | 667.648 us | 45.331 ms | 0.20% |
| `wilkinson_40` | 40 | 47 | 976 ns | 0 ns | 0 ns | 976 ns | 0 ns | 6.354 us | 84.64% |
| `wilkinson_48` | 48 | 61 | 1.175 us | 0 ns | 0 ns | 1.175 us | 0 ns | 8.488 us | 86.16% |
| `wilkinson_56` | 56 | 67 | 1.401 us | 0 ns | 0 ns | 1.401 us | 0 ns | 10.696 us | 86.90% |
| `chebyshev_T24` (control) | 24 | 5 | 634 ns | 4.728 us | 39.745 us | 45.136 us | 8.165 us | 55.432 us | 3.84% |
| `chebyshev_U24` (control) | 24 | 3 | 666 ns | 4.428 us | 34.360 us | 39.486 us | 7.272 us | 48.697 us | 3.98% |
| `legendre_P30` (control) | 30 | 67 | 891 ns | 6.284 us | 116.001 us | 123.080 us | 9.859 us | 136.051 us | 2.29% |
| `legendre_P38` (control) | 38 | 79 | 1.125 us | 10.817 us | 273.619 us | 285.541 us | 17.750 us | 309.539 us | 2.02% |
| `cyclo_phi17` (control) | 16 | 3 | 415 ns | 2.569 us | 13.805 us | 16.764 us | 3.904 us | 22.133 us | 6.62% |
| `cyclo_phi41` (control) | 40 | 3 | 1.094 us | 10.160 us | 61.403 us | 72.639 us | 18.308 us | 94.841 us | 4.11% |
| `xpow24_minus1` (control) | 24 | 11 | 656 ns | 2.698 us | 6.829 us | 10.212 us | 4.096 us | 16.599 us | 13.80% |
| `randprod_10` (control) | 20 | 7 | 541 ns | 3.154 us | 59.763 us | 63.558 us | 5.252 us | 70.725 us | 2.71% |
| `randprod_21` (control) | 24 | 17 | 660 ns | 3.875 us | 103.139 us | 107.676 us | 6.124 us | 116.212 us | 2.08% |

As shares of the three production stages:

| instance | pivot | swap+scale | eliminate |
|---|---:|---:|---:|
| `sd5` | 0.95% | 5.16% | 93.87% |
| `sd5_shift1` | 0.48% | 2.55% | 96.95% |
| `sd5_shift2` | 0.47% | 2.56% | 96.99% |
| `sd4_x_sd4shift1` | 0.48% | 2.69% | 96.79% |
| `sd5_x_phi11` | 0.26% | 1.79% | 97.96% |
| `xpow48_minus1` | 2.75% | 21.13% | 76.10% |
| `xpow105_minus1` | 0.76% | 15.54% | 83.74% |
| `xpow120_minus1` | 1.00% | 18.03% | 80.91% |
| `cyclo_phi179` | 0.18% | 6.32% | 93.47% |
| `cyclo_phi64_x_phi105` | 0.06% | 0.88% | 99.06% |
| `cyclo_phi128_x_phi165` | 0.02% | 0.53% | 99.45% |
| `cyclo_phi385` | 0.01% | 0.66% | 99.32% |
| `wilkinson_40` | 100.00% | 0.00% | 0.00% |
| `wilkinson_48` | 100.00% | 0.00% | 0.00% |
| `wilkinson_56` | 100.00% | 0.00% | 0.00% |
| `chebyshev_T24` (control) | 1.40% | 10.48% | 88.06% |
| `chebyshev_U24` (control) | 1.69% | 11.21% | 87.02% |
| `legendre_P30` (control) | 0.72% | 5.11% | 94.25% |
| `legendre_P38` (control) | 0.39% | 3.79% | 95.82% |
| `cyclo_phi17` (control) | 2.48% | 15.32% | 82.35% |
| `cyclo_phi41` (control) | 1.51% | 13.99% | 84.53% |
| `xpow24_minus1` (control) | 6.42% | 26.42% | 66.87% |
| `randprod_10` (control) | 0.85% | 4.96% | 94.03% |
| `randprod_21` (control) | 0.61% | 3.60% | 95.79% |

The three rows the deliverable names: **`cyclo_phi385` residual 0.20%**,
**`cyclo_phi128_x_phi165` residual 0.21%**, **`randprod_21` (24x24 at p = 17)
residual 2.08%**. Elimination is 99.32%, 99.45% and 95.79% of those staged
totals; swap and scale is 0.66%, 0.53% and 3.60%; pivot search is 0.01%, 0.02%
and 0.61%. Pivot search exceeds 2% only on `xpow48_minus1`,
`cyclo_phi17` and `xpow24_minus1`, whose whole reductions are 8 to 45 us, and is
100% of the Wilkinson rows, which have no pivots at all.

**The counting pass is a residual confound, not just an overhead.** It is
reported separately, but it still reads the pivot column's entries immediately
before the elimination writes those rows, so it warms `n` of the `n * m` words
the elimination touches. On the rows where the elimination dominates that is 240
reads against 4.3 million read-modify-writes; on `xpow48_minus1`, where it is
17 us against a 36 us elimination, it is not negligible, and the stage
proportions of the sparse rows should be read as the mirror's, not as clean
production proportions. Removing that confound needs the counts to come from a
separate replay on a separate buffer, which this instrument does not do.

**The three Wilkinson rows are the instrument, not the loop.** Their fixed-space
matrix is zero, so no column has a pivot, no row is ever added, and the only
stage that runs is pivot search. The 5 to 9 us residual is 2 clock reads per
free column over 40 to 56 columns at roughly 60 ns a read.

## The whole span

The `integrated` rung splits `fixedSpaceKernelVectors` into the same three
stages the prototype's column has: build, reduce, read the basis back. `build`
is `Packed.fixedSpace`, which contains the Frobenius power and the
column-polynomial recurrence.

| instance | build | reduce | readback | sum | fixedSpaceKernelVectors | residual |
|---|---:|---:|---:|---:|---:|---:|
| `sd5` | 1.274 ms | 87.549 us | 33.109 us | 1.394 ms | 1.385 ms | +0.7% |
| `sd5_shift1` | 1.633 ms | 171.819 us | 32.598 us | 1.837 ms | 1.821 ms | +0.9% |
| `sd5_shift2` | 1.595 ms | 174.668 us | 32.478 us | 1.802 ms | 1.793 ms | +0.5% |
| `sd4_x_sd4shift1` | 1.600 ms | 168.414 us | 32.708 us | 1.801 ms | 1.789 ms | +0.7% |
| `sd5_x_phi11` | 2.853 ms | 446.837 us | 52.918 us | 3.356 ms | 3.333 ms | +0.7% |
| `xpow48_minus1` | 543.530 us | 44.561 us | 72.597 us | 660.614 us | 626.438 us | +5.5% |
| `xpow105_minus1` | 3.507 ms | 342.602 us | 206.000 us | 4.055 ms | 4.021 ms | +0.8% |
| `xpow120_minus1` | 2.319 ms | 302.553 us | 574.537 us | 3.190 ms | 3.028 ms | +5.3% |
| `cyclo_phi179` | 3.096 ms | 2.593 ms | 185.350 us | 5.885 ms | 5.794 ms | +1.6% |
| `cyclo_phi64_x_phi105` | 3.670 ms | 3.856 ms | 104.965 us | 7.655 ms | 7.623 ms | +0.4% |
| `cyclo_phi128_x_phi165` | 7.886 ms | 20.087 ms | 237.106 us | 28.170 ms | 28.102 ms | +0.2% |
| `cyclo_phi385` | 7.375 ms | 44.596 ms | 421.164 us | 52.405 ms | 52.560 ms | -0.3% |
| `wilkinson_40` | 185.795 us | 3.576 us | 80.900 us | 270.326 us | 219.946 us | +22.9% |
| `wilkinson_48` | 267.251 us | 5.012 us | 120.684 us | 393.548 us | 315.112 us | +24.9% |
| `wilkinson_56` | 431.804 us | 6.680 us | 166.321 us | 605.162 us | 501.072 us | +20.8% |
| `chebyshev_T24` (control) | 119.136 us | 43.033 us | 7.311 us | 170.217 us | 167.173 us | +1.8% |
| `chebyshev_U24` (control) | 82.953 us | 37.190 us | 8.558 us | 128.686 us | 125.676 us | +2.4% |
| `legendre_P30` (control) | 1.204 ms | 120.028 us | 16.734 us | 1.342 ms | 1.332 ms | +0.7% |
| `legendre_P38` (control) | 2.400 ms | 283.305 us | 15.017 us | 2.701 ms | 2.708 ms | -0.3% |
| `cyclo_phi17` (control) | 33.565 us | 15.298 us | 2.674 us | 51.717 us | 51.040 us | +1.3% |
| `cyclo_phi41` (control) | 167.568 us | 69.438 us | 21.582 us | 257.927 us | 253.996 us | +1.5% |
| `xpow24_minus1` (control) | 148.595 us | 8.763 us | 19.083 us | 176.221 us | 167.393 us | +5.3% |
| `randprod_10` (control) | 166.356 us | 62.012 us | 6.605 us | 234.963 us | 232.054 us | +1.3% |
| `randprod_21` (control) | 569.960 us | 105.736 us | 12.122 us | 688.085 us | 683.203 us | +0.7% |

The three stages sum to the production span within about a percent on the rows
the deliverable names, and within 5.5% on every row except the three Wilkinson
ones.

The Wilkinson overshoot is a known confound, not an unattributed cost. Each rung
converts its basis to `Nat` residues so it can be compared entry for entry
against `Hex.Matrix.nullspace`, and production does not do that. It is
`kernelDimension * n` conversions, which is 960 on `cyclo_phi385` and irrelevant
there, but the Wilkinson rows have rank 0 and therefore `kernelDimension = n`,
so it is 1,600 to 3,136 conversions plus one array per basis vector, against a
whole span of 222 to 503 us.

## The comparison graph

Reduction time only; build and readback are excluded from every rung.

| instance | integrated | mirrored | hoistedPivotRow | arrayPivots | flatRowWrite | flatBothLoops | flatBuffer |
|---|---|---|---|---|---|---|---|
| `sd5` | 87.549 us | 87.614 us | 35.177 us | 35.483 us | 38.137 us | 34.240 us | 34.636 us |
| `sd5_shift1` | 171.819 us | 172.100 us | 56.879 us | 57.390 us | 62.908 us | 58.642 us | 60.780 us |
| `sd5_shift2` | 174.668 us | 174.208 us | 57.640 us | 57.830 us | 63.929 us | 59.763 us | 61.421 us |
| `sd4_x_sd4shift1` | 168.414 us | 168.339 us | 56.528 us | 56.944 us | 62.979 us | 58.622 us | 60.544 us |
| `sd5_x_phi11` | 446.837 us | 446.076 us | 141.284 us | 141.805 us | 162.751 us | 153.657 us | 158.254 us |
| `xpow48_minus1` | 44.561 us | 44.881 us | 40.790 us | 40.650 us | 42.402 us | 31.792 us | 27.471 us |
| `xpow105_minus1` | 342.602 us | 343.639 us | 272.959 us | 266.460 us | 284.952 us | 211.088 us | 186.161 us |
| `xpow120_minus1` | 302.553 us | 302.238 us | 266.079 us | 261.723 us | 274.476 us | 201.649 us | 175.155 us |
| `cyclo_phi179` | 2.593 ms | 2.590 ms | 1.277 ms | 1.237 ms | 1.343 ms | 1.116 ms | 1.086 ms |
| `cyclo_phi64_x_phi105` | 3.856 ms | 3.866 ms | 1.113 ms | 1.106 ms | 1.225 ms | 1.186 ms | 1.308 ms |
| `cyclo_phi128_x_phi165` | 20.087 ms | 20.092 ms | 5.721 ms | 5.706 ms | 6.260 ms | 6.094 ms | 7.008 ms |
| `cyclo_phi385` | 44.596 ms | 44.588 ms | 13.217 ms | 13.114 ms | 14.313 ms | 13.866 ms | 16.015 ms |
| `wilkinson_40` | 3.576 us | 3.661 us | 3.545 us | 3.736 us | 3.485 us | 3.485 us | 4.596 us |
| `wilkinson_48` | 5.012 us | 5.047 us | 4.982 us | 5.168 us | 4.937 us | 4.937 us | 6.074 us |
| `wilkinson_56` | 6.680 us | 6.720 us | 6.625 us | 6.810 us | 6.619 us | 6.610 us | 8.112 us |
| `chebyshev_T24` (control) | 43.033 us | 42.923 us | 23.590 us | 23.785 us | 25.082 us | 20.585 us | 18.852 us |
| `chebyshev_U24` (control) | 37.190 us | 37.385 us | 21.326 us | 21.261 us | 22.593 us | 18.797 us | 16.684 us |
| `legendre_P30` (control) | 120.028 us | 120.519 us | 47.345 us | 47.835 us | 51.987 us | 46.438 us | 47.375 us |
| `legendre_P38` (control) | 283.305 us | 282.518 us | 104.294 us | 103.108 us | 116.297 us | 105.571 us | 109.988 us |
| `cyclo_phi17` (control) | 15.298 us | 15.488 us | 10.385 us | 10.460 us | 10.410 us | 8.542 us | 7.726 us |
| `cyclo_phi41` (control) | 69.438 us | 69.483 us | 47.740 us | 47.480 us | 50.565 us | 39.509 us | 34.641 us |
| `xpow24_minus1` (control) | 8.763 us | 8.928 us | 8.908 us | 9.238 us | 9.224 us | 7.100 us | 6.103 us |
| `randprod_10` (control) | 62.012 us | 62.152 us | 24.256 us | 24.441 us | 26.809 us | 24.171 us | 23.109 us |
| `randprod_21` (control) | 105.736 us | 106.092 us | 37.875 us | 38.026 us | 42.027 us | 38.227 us | 37.976 us |

### One change at a time

Each column is the **median of the eight within-repeat differences**, with the
full range of those eight in brackets. A range that crosses zero means the
protocol does not resolve that effect on that row.

**These are differences against different baselines and they do not sum.**
`arrayPivots` and `flatRowWrite` are each one change from `hoistedPivotRow`, in
different directions; `flatBothLoops` is one change from `flatRowWrite`. Each
column answers "what does this one choice cost against the loop it sits in", and
only the first decomposes the whole gap.

| instance | source-row copy | List.concat pivots | modifyEntries closure | List.finRange outer scan | residual vs prototype |
|---|---|---|---|---|---|
| `sd5` | 53.114 us [48.693 us, 56.073 us] | 330 ns [-1.311 us, 2.492 us] | -3.150 us [-3.815 us, -51 ns] | 4.051 us [1.051 us, 4.877 us] | -496 ns [-1.702 us, 2.133 us] |
| `sd5_shift1` | 115.065 us [111.375 us, 119.447 us] | -320 ns [-1.843 us, 3.716 us] | -6.119 us [-7.101 us, -1.242 us] | 4.116 us [2.473 us, 6.099 us] | -2.694 us [-6.439 us, -1.232 us] |
| `sd5_shift2` | 116.707 us [111.715 us, 117.955 us] | -114 ns [-1.281 us, 4.828 us] | -6.524 us [-7.020 us, -170 ns] | 4.216 us [2.414 us, 6.340 us] | -1.992 us [-3.315 us, -1.062 us] |
| `sd4_x_sd4shift1` | 112.011 us [110.323 us, 114.580 us] | -491 ns [-1.122 us, 682 ns] | -6.795 us [-24.826 us, -4.106 us] | 4.317 us [2.404 us, 23.585 us] | -1.918 us [-5.489 us, -1.422 us] |
| `sd5_x_phi11` | 304.637 us [300.536 us, 310.811 us] | -596 ns [-1.962 us, 1.111 us] | -20.566 us [-22.744 us, -17.716 us] | 8.649 us [3.595 us, 14.993 us] | -7.581 us [-11.486 us, -2.184 us] |
| `xpow48_minus1` | 3.791 us [3.596 us, 4.677 us] | -176 ns [-2.994 us, 1.463 us] | -1.642 us [-4.637 us, -1.171 us] | 10.445 us [6.059 us, 14.271 us] | 4.231 us [3.946 us, 9.233 us] |
| `xpow105_minus1` | 70.325 us [67.410 us, 76.824 us] | 7.085 us [1.862 us, 9.324 us] | -11.041 us [-14.551 us, -7.632 us] | 73.109 us [68.653 us, 75.262 us] | 24.476 us [21.501 us, 29.523 us] |
| `xpow120_minus1` | 36.028 us [32.518 us, 42.865 us] | 5.338 us [2.764 us, 6.900 us] | -9.488 us [-13.391 us, -5.257 us] | 72.938 us [72.557 us, 76.715 us] | 26.468 us [22.133 us, 28.892 us] |
| `cyclo_phi179` | 1.318 ms [1.214 ms, 1.374 ms] | 38.988 us [29.364 us, 65.698 us] | -65.647 us [-84.596 us, -45.527 us] | 228.303 us [214.227 us, 257.522 us] | 27.351 us [-3.004 us, 38.086 us] |
| `cyclo_phi64_x_phi105` | 2.750 ms [2.669 ms, 2.789 ms] | 5.312 us [-150.854 us, 14.472 us] | -120.123 us [-129.451 us, -86.479 us] | 42.457 us [16.074 us, 46.720 us] | -124.725 us [-141.740 us, -98.656 us] |
| `cyclo_phi128_x_phi165` | 14.370 ms [14.135 ms, 14.832 ms] | 16.770 us [741 ns, 58.887 us] | -537.522 us [-600.641 us, -494.392 us] | 154.774 us [126.107 us, 203.211 us] | -935.602 us [-1.049 ms, -851.353 us] |
| `cyclo_phi385` | 31.378 ms [28.430 ms, 33.003 ms] | 93.373 us [55.152 us, 146.397 us] | -1.104 ms [-1.172 ms, -959.142 us] | 432.376 us [289.058 us, 516.856 us] | -2.164 ms [-2.396 ms, -2.039 ms] |
| `wilkinson_40` | 49 ns [-29 ns, 421 ns] | -160 ns [-271 ns, 30 ns] | 60 ns [-20 ns, 1.382 us] | 0 ns [-90 ns, 20 ns] | -1.111 us [-1.382 us, -781 ns] |
| `wilkinson_48` | 75 ns [-110 ns, 621 ns] | -195 ns [-330 ns, -80 ns] | 40 ns [0 ns, 110 ns] | 0 ns [-190 ns, 11 ns] | -1.111 us [-1.542 us, -921 ns] |
| `wilkinson_56` | 100 ns [-10 ns, 390 ns] | -190 ns [-341 ns, -90 ns] | -4 ns [-2.824 us, 31 ns] | 10 ns [-100 ns, 2.844 us] | -1.462 us [-2.143 us, -1.302 us] |
| `chebyshev_T24` (control) | 18.994 us [14.772 us, 19.779 us] | 210 ns [-1.123 us, 3.966 us] | -1.272 us [-2.454 us, 2.984 us] | 4.587 us [3.676 us, 4.898 us] | 1.727 us [150 ns, 2.643 us] |
| `chebyshev_U24` (control) | 15.989 us [15.833 us, 22.464 us] | 4 ns [-791 ns, 631 ns] | -1.347 us [-1.723 us, -911 ns] | 3.785 us [3.456 us, 4.318 us] | 2.118 us [1.772 us, 2.653 us] |
| `legendre_P30` (control) | 72.878 us [71.635 us, 74.330 us] | -846 ns [-3.366 us, 913 ns] | -4.080 us [-5.348 us, -3.455 us] | 5.588 us [4.396 us, 6.469 us] | -1.331 us [-2.744 us, -191 ns] |
| `legendre_P38` (control) | 179.516 us [175.819 us, 336.940 us] | 1.502 us [-672 ns, 3.165 us] | -11.728 us [-14.452 us, -9.504 us] | 10.591 us [6.380 us, 13.470 us] | -3.946 us [-15.953 us, -1.913 us] |
| `cyclo_phi17` (control) | 5.173 us [2.053 us, 10.856 us] | 395 ns [-982 ns, 2.273 us] | -35 ns [-561 ns, 2.663 us] | 1.893 us [1.813 us, 2.053 us] | 756 ns [580 ns, 1.172 us] |
| `cyclo_phi41` (control) | 21.892 us [20.892 us, 29.984 us] | 10 ns [-1.803 us, 1.923 us] | -2.449 us [-3.264 us, -2.013 us] | 11.071 us [10.455 us, 11.627 us] | 4.662 us [4.026 us, 5.258 us] |
| `xpow24_minus1` (control) | -54 ns [-322 ns, 251 ns] | -280 ns [-1.162 us, 520 ns] | -301 ns [-751 ns, 160 ns] | 2.123 us [2.014 us, 2.313 us] | 1.036 us [871 ns, 1.141 us] |
| `randprod_10` (control) | 37.656 us [36.915 us, 41.973 us] | -195 ns [-862 ns, 490 ns] | -2.504 us [-5.047 us, -2.144 us] | 2.663 us [2.033 us, 5.037 us] | 1.067 us [-2.854 us, 1.272 us] |
| `randprod_21` (control) | 67.320 us [64.335 us, 71.345 us] | -200 ns [-1.423 us, 3.655 us] | -3.785 us [-4.557 us, -752 ns] | 3.385 us [-130 ns, 4.567 us] | 215 ns [-3.785 us, 3.426 us] |

On `cyclo_phi385`, against a 44.596 ms `integrated` reduction:

| change | baseline | paired median | fraction of `integrated` | resolved? |
|---|---|---:|---:|---|
| source-row copy | `mirrored` | 31.378 ms | **70.4%** | 8/8 repeats same sign |
| pivot accumulation, `List.concat` against `Array.push` | `hoistedPivotRow` | 93.373 us | 0.21% | 8/8 same sign |
| row-write mechanism, `Matrix.modifyEntries` against a flat `Nat`-indexed loop | `hoistedPivotRow` | **-1.104 ms** | **-2.5%** | 8/8 same sign |
| outer column scan, `List.finRange` against a `Nat` range | `flatRowWrite` | 432.376 us | 0.97% | 8/8 same sign |
| residual against the prototype | `flatBothLoops` | -2.164 ms | -4.9% | 8/8 same sign |

### The source-row copy is the gap

| instance | `integrated` | `mirrored - hoistedPivotRow` (paired median) | fraction of `integrated` | ops per column scan |
|---|---:|---:|---:|---:|
| `sd5` | 87.549 us | 53.114 us | 60.7% | 13.9 |
| `sd5_shift1` | 171.819 us | 115.065 us | 67.0% | 29.0 |
| `sd5_shift2` | 174.668 us | 116.707 us | 66.8% | 29.4 |
| `sd4_x_sd4shift1` | 168.414 us | 112.011 us | 66.5% | 28.6 |
| `sd5_x_phi11` | 446.837 us | 304.637 us | 68.2% | 38.3 |
| `xpow48_minus1` | 44.561 us | 3.791 us | 8.5% | 1.3 |
| `xpow105_minus1` | 342.602 us | 70.325 us | 20.5% | 1.9 |
| `xpow120_minus1` | 302.553 us | 36.028 us | 11.9% | 1.4 |
| `cyclo_phi179` | 2.593 ms | 1.318 ms | 50.8% | 6.4 |
| `cyclo_phi64_x_phi105` | 3.856 ms | 2.750 ms | 71.3% | 61.9 |
| `cyclo_phi128_x_phi165` | 20.087 ms | 14.370 ms | 71.5% | 97.4 |
| `cyclo_phi385` | 44.596 ms | 31.378 ms | 70.4% | 76.4 |
| `wilkinson_40` | 3.576 us | 49 ns | 1.4% | 0.0 |
| `wilkinson_48` | 5.012 us | 75 ns | 1.5% | 0.0 |
| `wilkinson_56` | 6.680 us | 100 ns | 1.5% | 0.0 |
| `chebyshev_T24` (control) | 43.033 us | 18.994 us | 44.1% | 5.6 |
| `chebyshev_U24` (control) | 37.190 us | 15.989 us | 43.0% | 5.1 |
| `legendre_P30` (control) | 120.028 us | 72.878 us | 60.7% | 14.2 |
| `legendre_P38` (control) | 283.305 us | 179.516 us | 63.4% | 18.2 |
| `cyclo_phi17` (control) | 15.298 us | 5.173 us | 33.8% | 3.6 |
| `cyclo_phi41` (control) | 69.438 us | 21.892 us | 31.5% | 2.9 |
| `xpow24_minus1` (control) | 8.763 us | -54 ns | -0.6% | 1.0 |
| `randprod_10` (control) | 62.012 us | 37.656 us | 60.7% | 15.3 |
| `randprod_21` (control) | 105.736 us | 67.320 us | 63.7% | 21.7 |

The share tracks the row's ratio of inner-loop entry operations to column scans,
`rowAdds * n` against `rowAdds + rowAddsSkipped`: 76 on `cyclo_phi385`, 97 on
`cyclo_phi128_x_phi165`, 22 on `randprod_21`, but 1.9 on `xpow105_minus1` and
1.0 on `xpow24_minus1`. The copy is `n` words per row addition, so it is charged
only where row additions happen, and rows whose columns are mostly already zero
never pay it.

This is the *net* saving from hoisting, not the gross cost of the copies: the
hoisted rung still reads the pivot row once per pivot column, unconditionally,
including on columns where every elimination is skipped.

It is also the one effect large enough to be insensitive to the order the rungs
run in. Stratified by direction, on `cyclo_phi385` it is 31.905 ms on the
forward calls and 31.041 ms on the reverse ones; the whole direction effect is
smaller than the repeat spread.

### The other candidates

**The row-write mechanism is not a cost; it is a saving.** Writing the flat
backing buffer directly, with the outer scan and the pivot list held fixed, is
slower on every row that does arithmetic: 1.104 ms on `cyclo_phi385` (2.5% of
the reduction, 8.4% of the hoisted one), 538 us on `cyclo_phi128_x_phi165`
(2.7% and 9.4%), and the sign is the same on all eight repeats of both.

This is a **coarse mechanism swap, not a closure cost**. `modifyEntries` runs a
`Fin.foldl` whose index carries its bound as an erased proof, so each read and
write is unchecked, while the flat loop is `Nat`-indexed and every
`Vector.set!` and `Array.getElem!` tests its bound and carries a panic branch;
the coefficient read at the top of the elimination changes with it. The two
cannot be separated -- a flat write with `Fin` indices *is* `modifyEntries` --
so the honest statement is that the mechanism as a whole is 2.5% cheaper in the
production form. The direction is what matters here: this candidate is not part
of the 2.6x gap.

**The `List (Fin m)` pivot accumulation is 0.21%.** `List.concat` is
`O(length)` per pivot, so it is `O(rank^2)` cons cells across a reduction,
28,000 on `cyclo_phi385`. Switching to `Array.push` saves 93 us of 46 ms. It is
also a coarse swap rather than an exact price for `List.concat`: the two rungs
differ in the whole pivot-column representation, including the `Fin` list the
readback then walks. It is resolved in sign on `cyclo_phi385`,
`cyclo_phi128_x_phi165`, `xpow105_minus1` and `xpow120_minus1`, and unresolved
on several small rows. Either way it is under a quarter of a percent.

**The `List.finRange n` column scan is 1% where arithmetic dominates and about
20% where it does not.** On `cyclo_phi385` it is 432 us of 44.6 ms. On
`xpow105_minus1` it is 73.109 us of a 343 us reduction, **21%**; on
`xpow120_minus1`, 72.938 us of 303 us, **24%**; on `cyclo_phi41`, 11.071 us of
69 us, **16%**. Those are exactly the rows whose entry-operation to column-scan
ratio is between 1.0 and 2.9: the scan is paid per column entry, the arithmetic
per row entry.

**The bottom rung is a residual, not an attribution.** `reduce32` changes pivot
search, swap, scale, inversion, pivot storage and pivot-row access all at once,
and carries its `useBarrett` and `skipZero` flags as runtime `Bool`s tested
inside the inner loop. It is here because it reproduces the prototype column the
2.6x was measured against, and because `flatBothLoops - flatBuffer` is then the
part of the gap the graph does not explain. On the two heaviest rows that
residual is *negative*: the shipped loop's scaffolding, with the copy hoisted
and both loops flattened, beats the prototype's by 13% and 13%.

### The basis readback

Not part of the reduction, and a second real finding, with two confounds stated
up front. `Packed.nullspaceArray` searches the pivot-column *list* for every
output entry, so its total is `O(m * rank + kernelDim * m * rank)`;
`basisOfBuffer32` scans the pivot-column `Array` once for the free columns and
then scatters only the pivot entries, `O(m * rank + kernelDim * (m + rank))`.
Both pay the free-column scan; they differ in what they do per output entry.
They are different algorithms, not the same algorithm with different constants,
and the `nullspaceArray` column additionally carries the `ZMod64`-to-`Nat`
conversion the rungs do for cross-checking. The factor below is therefore an
end-to-end comparison of two readbacks, not the price of a list.

| instance | kernel dim | rank | nullspaceArray + Nat | basisOfBuffer32 | factor | share of span |
|---|---:|---:|---:|---:|---:|---:|
| `sd5` | 16 | 16 | 33.109 us | 1.963 us | 16.9x | 2.4% |
| `sd5_shift1` | 16 | 16 | 32.598 us | 1.978 us | 16.5x | 1.8% |
| `sd5_shift2` | 16 | 16 | 32.478 us | 1.963 us | 16.5x | 1.8% |
| `sd4_x_sd4shift1` | 16 | 16 | 32.708 us | 2.003 us | 16.3x | 1.8% |
| `sd5_x_phi11` | 17 | 25 | 52.918 us | 3.239 us | 16.3x | 1.6% |
| `xpow48_minus1` | 19 | 29 | 72.597 us | 3.840 us | 18.9x | 11.6% |
| `xpow105_minus1` | 14 | 91 | 206.000 us | 12.007 us | 17.2x | 5.1% |
| `xpow120_minus1` | 39 | 81 | 574.537 us | 19.729 us | 29.1x | 19.0% |
| `cyclo_phi179` | 2 | 176 | 185.350 us | 21.792 us | 8.5x | 3.2% |
| `cyclo_phi64_x_phi105` | 10 | 70 | 104.965 us | 7.541 us | 13.9x | 1.4% |
| `cyclo_phi128_x_phi165` | 8 | 136 | 237.106 us | 17.882 us | 13.3x | 0.8% |
| `cyclo_phi385` | 4 | 236 | 421.164 us | 33.865 us | 12.4x | 0.8% |
| `wilkinson_40` | 40 | 0 | 80.900 us | 1.582 us | 51.1x | 36.8% |
| `wilkinson_48` | 48 | 0 | 120.684 us | 2.429 us | 49.7x | 38.3% |
| `wilkinson_56` | 56 | 0 | 166.321 us | 2.994 us | 55.6x | 33.2% |
| `chebyshev_T24` (control) | 3 | 21 | 7.311 us | 977 ns | 7.5x | 4.4% |
| `chebyshev_U24` (control) | 4 | 20 | 8.558 us | 1.061 us | 8.1x | 6.8% |
| `legendre_P30` (control) | 7 | 23 | 16.734 us | 1.717 us | 9.7x | 1.3% |
| `legendre_P38` (control) | 3 | 35 | 15.017 us | 2.273 us | 6.6x | 0.6% |
| `cyclo_phi17` (control) | 1 | 15 | 2.674 us | 510 ns | 5.2x | 5.2% |
| `cyclo_phi41` (control) | 5 | 35 | 21.582 us | 2.048 us | 10.5x | 8.5% |
| `xpow24_minus1` (control) | 13 | 11 | 19.083 us | 1.291 us | 14.8x | 11.4% |
| `randprod_10` (control) | 4 | 16 | 6.605 us | 856 ns | 7.7x | 2.8% |
| `randprod_21` (control) | 7 | 17 | 12.122 us | 1.202 us | 10.1x | 1.8% |

On the rows where the reduction dominates the readback is under 1% of the span
and does not matter. On high-nullity rows it is a fifth to a third of it.

## The inner modular multiply

`doubled - saltedMin` is one modular multiply against one `UInt32` addition, per
inner-loop entry, over the same entries, in the same loop, with the same control
flow and the same row additions. It is measured in both loop shapes, so that
transferring it between shapes is a measurement rather than an assumption.

| instance | inner multiplies | modifyEntries shape | flat shape | ns/multiply (modifyEntries) | ns/multiply (flat) | increment / `integrated` | increment / `hoistedPivotRow` |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 6,880 | 3.646 us [230 ns, 4.236 us] | 3.085 us [2.094 us, 8.482 us] | 0.53 ns | 0.45 ns | 4.2% | 10.4% |
| `sd5_shift1` | 14,368 | 8.113 us [7.551 us, 13.490 us] | 5.278 us [2.274 us, 6.850 us] | 0.56 ns | 0.37 ns | 4.7% | 14.3% |
| `sd5_shift2` | 14,560 | 8.086 us [5.147 us, 10.946 us] | 5.388 us [1.272 us, 6.830 us] | 0.56 ns | 0.37 ns | 4.6% | 14.0% |
| `sd4_x_sd4shift1` | 14,208 | 7.846 us [7.632 us, 12.399 us] | 6.154 us [1.943 us, 6.700 us] | 0.55 ns | 0.43 ns | 4.7% | 13.9% |
| `sd5_x_phi11` | 39,270 | 21.146 us [17.776 us, 28.222 us] | 16.414 us [12.589 us, 17.887 us] | 0.54 ns | 0.42 ns | 4.7% | 15.0% |
| `xpow48_minus1` | 1,824 | 1.248 us [491 ns, 4.077 us] | 1.266 us [841 ns, 1.922 us] | 0.68 ns | 0.69 ns | 2.8% | 3.1% |
| `xpow105_minus1` | 18,375 | 10.685 us [8.482 us, 20.280 us] | 7.386 us [7.021 us, 12.169 us] | 0.58 ns | 0.40 ns | 3.1% | 3.9% |
| `xpow120_minus1` | 13,920 | 8.172 us [3.665 us, 14.020 us] | 6.785 us [-3.816 us, 7.702 us] | 0.59 ns | 0.49 ns | 2.7% | 3.1% |
| `cyclo_phi179` | 198,292 | 101.991 us [93.038 us, 114.970 us] | 74.115 us [63.143 us, 89.873 us] | 0.51 ns | 0.37 ns | 3.9% | 8.0% |
| `cyclo_phi64_x_phi105` | 342,160 | 174.214 us [138.636 us, 189.671 us] | 125.371 us [108.461 us, 147.488 us] | 0.51 ns | 0.37 ns | 4.5% | 15.7% |
| `cyclo_phi128_x_phi165` | 1,893,456 | 979.798 us [960.253 us, 1.010 ms] | 687.600 us [636.284 us, 780.247 us] | 0.52 ns | 0.36 ns | 4.9% | 17.1% |
| `cyclo_phi385` | 4,307,520 | 2.200 ms [1.896 ms, 2.226 ms] | 1.491 ms [1.328 ms, 1.652 ms] | 0.51 ns | 0.35 ns | 4.9% | 16.6% |
| `wilkinson_40` | 0 | -25 ns | 105 ns | -- | -- | -- | -- |
| `wilkinson_48` | 0 | 6 ns | 100 ns | -- | -- | -- | -- |
| `wilkinson_56` | 0 | 10 ns | 110 ns | -- | -- | -- | -- |
| `chebyshev_T24` (control) | 2,688 | 1.557 us [772 ns, 6.590 us] | 1.256 us [911 ns, 7.171 us] | 0.58 ns | 0.47 ns | 3.6% | 6.6% |
| `chebyshev_U24` (control) | 2,352 | 1.428 us [1.172 us, 1.583 us] | 866 ns [630 ns, 1.132 us] | 0.61 ns | 0.37 ns | 3.8% | 6.7% |
| `legendre_P30` (control) | 9,450 | 4.898 us [1.333 us, 5.208 us] | 3.756 us [3.055 us, 4.617 us] | 0.52 ns | 0.40 ns | 4.1% | 10.3% |
| `legendre_P38` (control) | 23,560 | 12.343 us [8.161 us, 15.393 us] | 10.150 us [8.572 us, 16.814 us] | 0.52 ns | 0.43 ns | 4.4% | 11.8% |
| `cyclo_phi17` (control) | 800 | 486 ns [240 ns, 610 ns] | 476 ns [220 ns, 27.151 us] | 0.61 ns | 0.59 ns | 3.2% | 4.7% |
| `cyclo_phi41` (control) | 4,000 | 2.458 us [2.144 us, 2.935 us] | 1.999 us [-4.116 us, 5.007 us] | 0.61 ns | 0.50 ns | 3.5% | 5.1% |
| `xpow24_minus1` (control) | 264 | 220 ns [40 ns, 511 ns] | 316 ns [-90 ns, 621 ns] | 0.83 ns | 1.20 ns | 3.6% | 3.5% |
| `randprod_10` (control) | 4,660 | 2.559 us [2.433 us, 2.675 us] | 1.668 us [1.413 us, 2.383 us] | 0.55 ns | 0.36 ns | 4.1% | 10.5% |
| `randprod_21` (control) | 8,472 | 4.582 us [1.252 us, 26.619 us] | 3.295 us [220 ns, 4.096 us] | 0.54 ns | 0.39 ns | 4.3% | 12.1% |

Per multiply the two shapes do not agree: **0.51 ns in the `modifyEntries` shape
and 0.35 ns in the flat shape** on `cyclo_phi385`, and a 1.3x to 1.5x spread on
every heavy row. The last two columns divide the larger of the two by
the reduction: **4.9% of the integrated reduction on `cyclo_phi385` and 16.6% of
the copy-free one**, 4.9% and 17.1% on `cyclo_phi128_x_phi165`. They are
labelled `increment / reduction`, not `share`, for the reason below.

**Those percentages are an incremental two-divide throughput measurement divided
by a reduction time. They are not a causal share, and taking the larger of the
two shapes does not make them a bound.** Two effects push the increment in
opposite directions and neither is quantified: the two divides in the doubled
rung are independent, so the core overlaps them and the increment measures less
than an isolated divide would cost; and the doubled rung holds one more live
value, which costs something the control does not pay. The right reading is
"removing the divide is worth something of this order", not "the divide is this
fraction of the reduction".

The control that makes it that much is the select:

| instance | saltedMin - salted (the select) | salted - flatBothLoops (the salt) |
|---|---:|---:|
| `sd5` | 2.369 us [1.683 us, 3.124 us] | -40 ns [-3.264 us, 911 ns] |
| `sd5_shift1` | 4.938 us [3.877 us, 7.120 us] | 480 ns [40 ns, 2.524 us] |
| `sd5_shift2` | 5.228 us [3.546 us, 8.934 us] | 220 ns [-2.012 us, 2.003 us] |
| `sd4_x_sd4shift1` | 3.841 us [3.084 us, 7.621 us] | 256 ns [-1.822 us, 1.763 us] |
| `sd5_x_phi11` | 11.632 us [9.044 us, 16.885 us] | -10 ns [-8.413 us, 5.458 us] |
| `xpow48_minus1` | 602 ns [-4.757 us, 1.162 us] | -240 ns [-5.278 us, 5.318 us] |
| `xpow105_minus1` | 6.870 us [4.377 us, 8.993 us] | -155 ns [-7.240 us, 2.393 us] |
| `xpow120_minus1` | 5.133 us [-330 ns, 13.881 us] | -106 ns [-1.152 us, 3.194 us] |
| `cyclo_phi179` | 74.906 us [57.024 us, 86.558 us] | -9.393 us [-17.746 us, 19.949 us] |
| `cyclo_phi64_x_phi105` | 129.256 us [87.821 us, 149.282 us] | -1.032 us [-35.893 us, 38.256 us] |
| `cyclo_phi128_x_phi165` | 745.089 us [665.636 us, 851.242 us] | 2.585 us [-60.979 us, 74.311 us] |
| `cyclo_phi385` | 1.770 ms [1.611 ms, 1.882 ms] | 9.243 us [-34.631 us, 148.531 us] |
| `wilkinson_40` | 15 ns [-10 ns, 100 ns] | -6 ns [-90 ns, 30 ns] |
| `wilkinson_48` | 0 ns [-191 ns, 110 ns] | 20 ns [-201 ns, 191 ns] |
| `wilkinson_56` | 15 ns [-19 ns, 70 ns] | -0 ns [-90 ns, 30 ns] |
| `chebyshev_T24` (control) | 986 ns [722 ns, 1.402 us] | -121 ns [-411 ns, 181 ns] |
| `chebyshev_U24` (control) | 1.011 us [691 ns, 1.282 us] | 106 ns [-430 ns, 220 ns] |
| `legendre_P30` (control) | 2.869 us [721 ns, 3.435 us] | -65 ns [-1.151 us, 2.744 us] |
| `legendre_P38` (control) | 5.027 us [-1.422 us, 8.503 us] | 1.363 us [-3.355 us, 10.155 us] |
| `cyclo_phi17` (control) | 305 ns [71 ns, 640 ns] | 6 ns [-141 ns, 220 ns] |
| `cyclo_phi41` (control) | 1.307 us [-15.133 us, 6.530 us] | 55 ns [-341 ns, 16.034 us] |
| `xpow24_minus1` (control) | 260 ns [-3.595 us, 371 ns] | -44 ns [-231 ns, 3.836 us] |
| `randprod_10` (control) | 1.702 us [1.493 us, 2.123 us] | -110 ns [-611 ns, 110 ns] |
| `randprod_21` (control) | 2.979 us [1.893 us, 5.678 us] | 360 ns [-3.626 us, 1.011 us] |

The select together with the increment it selects against is **1.770 ms on
`cyclo_phi385`, larger than the multiply itself**. Charging it to the
multiply, as a doubled-against-plain comparison would, overstates the multiply
by about a factor of two; an earlier version of this measurement did exactly
that. The two are not separated further here, so "the select" below always means
"the select and its `UInt32` increment". The salt is free: its paired range
straddles zero on most rows and its median is a fraction of a percent of the
reduction on every row.

## The two open design points

#9150's verification left two of the prototype's five design factors
unre-measured against the integrated implementation. This run prices both, in
the same process on the same matrices, on the prototype's two storage widths and
two multiply routines, with the four variants run in the same alternating
directions as the ladder and their per-repeat reductions kept, so the
comparisons below are paired.

| instance | UInt64 + Barrett | UInt32 + Barrett | UInt32 + hardware `%` | UInt64/UInt32 | `%`/Barrett |
|---|---:|---:|---:|---:|---:|
| `sd5` | 60.535 us | 35.137 us | 34.711 us | 1.72x | 0.99x |
| `sd5_shift1` | 109.302 us | 61.216 us | 60.654 us | 1.79x | 0.99x |
| `sd5_shift2` | 109.752 us | 62.337 us | 62.608 us | 1.76x | 1.00x |
| `sd4_x_sd4shift1` | 105.045 us | 61.361 us | 61.546 us | 1.71x | 1.00x |
| `sd5_x_phi11` | 285.478 us | 159.195 us | 161.123 us | 1.79x | 1.01x |
| `xpow48_minus1` | 40.244 us | 28.131 us | 27.601 us | 1.43x | 0.98x |
| `xpow105_minus1` | 300.615 us | 185.755 us | 187.227 us | 1.62x | 1.01x |
| `xpow120_minus1` | 270.932 us | 175.239 us | 175.645 us | 1.55x | 1.00x |
| `cyclo_phi179` | 1.914 ms | 1.081 ms | 1.094 ms | 1.77x | 1.01x |
| `cyclo_phi64_x_phi105` | 2.445 ms | 1.300 ms | 1.329 ms | 1.88x | 1.02x |
| `cyclo_phi128_x_phi165` | 13.173 ms | 6.994 ms | 7.136 ms | 1.88x | 1.02x |
| `cyclo_phi385` | 31.730 ms | 15.974 ms | 16.120 ms | 1.99x | 1.01x |
| `wilkinson_40` | 4.978 us | 4.737 us | 4.376 us | 1.05x | 0.92x |
| `wilkinson_48` | 6.710 us | 6.169 us | 5.959 us | 1.09x | 0.97x |
| `wilkinson_56` | 8.648 us | 8.443 us | 8.473 us | 1.02x | 1.00x |
| `chebyshev_T24` (control) | 31.336 us | 19.319 us | 18.923 us | 1.62x | 0.98x |
| `chebyshev_U24` (control) | 27.035 us | 17.125 us | 16.800 us | 1.58x | 0.98x |
| `legendre_P30` (control) | 85.832 us | 47.976 us | 47.976 us | 1.79x | 1.00x |
| `legendre_P38` (control) | 185.315 us | 109.407 us | 109.292 us | 1.69x | 1.00x |
| `cyclo_phi17` (control) | 12.774 us | 8.022 us | 7.826 us | 1.59x | 0.98x |
| `cyclo_phi41` (control) | 53.464 us | 35.297 us | 35.042 us | 1.51x | 0.99x |
| `xpow24_minus1` (control) | 9.344 us | 6.775 us | 6.234 us | 1.38x | 0.92x |
| `randprod_10` (control) | 41.621 us | 23.309 us | 23.239 us | 1.79x | 1.00x |
| `randprod_21` (control) | 72.297 us | 38.472 us | 38.407 us | 1.88x | 1.00x |

Paired within each repeat, which is what the conclusions below rest on:

| instance | `%` - Barrett (median [min, max]) | as % of Barrett | `%`-Barrett sign consistent? | UInt64 - UInt32 (median [min, max]) | as % of UInt32 | UInt64 sign consistent? |
|---|---:|---:|---|---:|---:|---|
| `sd5` | -536 ns [-3.766 us, 652 ns] | -1.53% | no | 25.368 us [22.003 us, 27.191 us] | +72.2% | yes |
| `sd5_shift1` | -80 ns [-1.332 us, 430 ns] | -0.13% | no | 48.101 us [46.038 us, 49.624 us] | +78.6% | yes |
| `sd5_shift2` | 836 ns [-3.355 us, 2.283 us] | +1.34% | no | 47.420 us [40.750 us, 51.266 us] | +76.1% | yes |
| `sd4_x_sd4shift1` | 186 ns [-3.646 us, 11.618 us] | +0.30% | no | 42.738 us [39.358 us, 50.134 us] | +69.7% | yes |
| `sd5_x_phi11` | -271 ns [-9.594 us, 3.306 us] | -0.17% | no | 124.769 us [115.002 us, 129.383 us] | +78.4% | yes |
| `xpow48_minus1` | -596 ns [-2.344 us, 261 ns] | -2.12% | no | 12.354 us [11.306 us, 14.061 us] | +43.9% | yes |
| `xpow105_minus1` | 1.111 us [-281 ns, 5.007 us] | +0.60% | no | 115.196 us [108.591 us, 128.982 us] | +62.0% | yes |
| `xpow120_minus1` | -30 ns [-4.597 us, 6.099 us] | -0.02% | no | 94.861 us [88.431 us, 98.326 us] | +54.1% | yes |
| `cyclo_phi179` | 14.066 us [-10.526 us, 18.918 us] | +1.30% | no | 825.693 us [750.143 us, 906.634 us] | +76.4% | yes |
| `cyclo_phi64_x_phi105` | 27.897 us [2.976 us, 33.199 us] | +2.15% | yes | 1.144 ms [1.098 ms, 1.177 ms] | +88.0% | yes |
| `cyclo_phi128_x_phi165` | 100.644 us [29.113 us, 191.844 us] | +1.44% | yes | 6.170 ms [6.066 ms, 6.409 ms] | +88.2% | yes |
| `cyclo_phi385` | 137.789 us [-246.395 us, 358.401 us] | +0.86% | no | 15.725 ms [15.430 ms, 15.933 ms] | +98.4% | yes |
| `wilkinson_40` | -406 ns [-2.183 us, 450 ns] | -8.57% | no | 336 ns [-30 ns, 1.042 us] | +7.1% | no |
| `wilkinson_48` | 5 ns [-1.942 us, 100 ns] | +0.08% | no | 264 ns [-790 ns, 1.642 us] | +4.3% | no |
| `wilkinson_56` | 4 ns [-652 ns, 671 ns] | +0.05% | no | 300 ns [-231 ns, 971 ns] | +3.6% | no |
| `chebyshev_T24` (control) | -126 ns [-1.532 us, 10.245 us] | -0.65% | no | 11.522 us [9.023 us, 14.411 us] | +59.6% | yes |
| `chebyshev_U24` (control) | -304 ns [-1.031 us, 260 ns] | -1.78% | no | 9.645 us [7.432 us, 12.237 us] | +56.3% | yes |
| `legendre_P30` (control) | 15 ns [-801 ns, 1.292 us] | +0.03% | no | 37.806 us [30.856 us, 44.926 us] | +78.8% | yes |
| `legendre_P38` (control) | -215 ns [-10.466 us, 1.022 us] | -0.20% | no | 77.210 us [65.447 us, 85.246 us] | +70.6% | yes |
| `cyclo_phi17` (control) | -280 ns [-1.142 us, 3.275 us] | -3.50% | no | 4.311 us [2.955 us, 5.567 us] | +53.7% | yes |
| `cyclo_phi41` (control) | -400 ns [-1.122 us, 561 ns] | -1.13% | no | 18.332 us [16.145 us, 19.930 us] | +51.9% | yes |
| `xpow24_minus1` (control) | -570 ns [-4.556 us, 190 ns] | -8.42% | no | 2.574 us [-1.863 us, 3.515 us] | +38.0% | no |
| `randprod_10` (control) | -260 ns [-1.012 us, 572 ns] | -1.12% | no | 18.212 us [13.861 us, 26.940 us] | +78.1% | yes |
| `randprod_21` (control) | -136 ns [-912 ns, 5.018 us] | -0.35% | no | 33.840 us [24.727 us, 38.607 us] | +88.0% | yes |

**`UInt32` versus `UInt64` entries: settled, in the shipped direction, on every
row that does any real arithmetic.** The paired difference is +38% to +98% of
the `UInt32` time, and the same sign on all eight repeats of 20 of the 24 rows.
The four where it is not are the three rank-0 Wilkinson rows, which perform no
row additions and whose paired range straddles zero at +3.6% to +7.1%, and
`xpow24_minus1`, whose whole reduction is 6 us on 11 row additions. The
prototype's 2.42x re-measures a little lower here, on a different day and a
busier host, but in the same direction and for the same reason, which is boxing:
`lean_box_uint32` is a tagged immediate on a 64-bit runtime and
`lean_box_uint64` allocates. This remains a comparison of `reduce64` against
`reduce32`, not of two integrated implementations, so it is strong corroborating
evidence for the shipped choice rather than a re-measurement of it. Since the
shipped code already stores `UInt32`, there is nothing to build either way.

**Barrett reciprocal versus hardware remainder: resolved on two rows, at 1.4%
to 2.2% in Barrett's favour, and unresolved everywhere else.** The paired
difference is the same sign on all eight repeats on exactly two of 24 rows:
`cyclo_phi64_x_phi105` (+2.15%) and `cyclo_phi128_x_phi165` (+1.44%), both
against the hardware remainder. On `cyclo_phi385` the paired median is +0.86%
but the range runs from -246 us to +358 us, so it is not resolved; on the other
21 rows the median is between -3.5% and +1.3% and the range crosses zero on
every one. The unweighted median across rows is 0.999 and the time-weighted
ratio is 1.012, and the direction-stratified table shows the sign of the small
rows' difference flipping with the call order, which is what an unresolved
effect looks like.

So the reciprocal is not a tie: where this protocol resolves it, Barrett is
ahead, by **1.4% to 2.2% of a whole reduction**. That is the number, and it is
small.

**Neither variant should be built now.** For the entry width there is nothing to
build. For the reciprocal, 1.4% to 2.2% of a reduction, on two of 24 rows, buys
a second compiled reduction loop plus the reciprocal's proof obligations inside
the correspondence, against a source-row copy that costs 68% to 72% on those
same rows. That is an engineering judgement about ordering, not a claim that the
reciprocal is worthless; if the copy is ever removed, the multiply's incremental
cost rises from about 5% of the reduction to about 17%, and the reciprocal is
worth re-opening then, with a paired measurement designed for a two-percent
effect rather than one that resolves it on two rows out of 24.

The one thing this leaves open about the multiply is the modulus range. Every
number here is on moduli 3 to 79, far from the `2^31` bound `ZMod64.Bounds`
allows, and the hardware divider's cost is data-dependent. A corpus with moduli
near `2^31` could move both of these conclusions; nothing in this run speaks to
it.

## Order effects and repeat spread

The paired ranges above are the primary uncertainty statement. Two summaries
support them. First, the same differences stratified by call direction:

call directions: [True, False, True, False, True, False, True, False]

| instance | copy delta fwd | copy delta rev | `%`-Barrett fwd | `%`-Barrett rev |
|---|---:|---:|---:|---:|
| `sd5` | 54.180 us | 52.938 us | -2.134 us | 211 ns |
| `sd5_shift1` | 116.042 us | 114.895 us | -806 ns | 190 ns |
| `sd5_shift2` | 114.344 us | 117.504 us | 866 ns | 836 ns |
| `sd4_x_sd4shift1` | 112.416 us | 112.011 us | -450 ns | 702 ns |
| `sd5_x_phi11` | 303.029 us | 305.142 us | 516 ns | -271 ns |
| `xpow48_minus1` | 3.691 us | 4.196 us | -1.567 us | 126 ns |
| `xpow105_minus1` | 69.528 us | 71.751 us | 295 ns | 1.819 us |
| `xpow120_minus1` | 35.502 us | 37.245 us | -4.186 us | 1.086 us |
| `cyclo_phi179` | 1.322 ms | 1.300 ms | 3.436 us | 15.983 us |
| `cyclo_phi64_x_phi105` | 2.740 ms | 2.761 ms | 28.602 us | 27.897 us |
| `cyclo_phi128_x_phi165` | 14.370 ms | 14.366 ms | 87.996 us | 100.644 us |
| `cyclo_phi385` | 31.905 ms | 31.041 ms | 219.125 us | 66.198 us |
| `wilkinson_40` | 186 ns | 10 ns | -731 ns | 295 ns |
| `wilkinson_48` | 296 ns | -26 ns | -506 ns | 54 ns |
| `wilkinson_56` | 235 ns | 5 ns | -170 ns | 24 ns |
| `chebyshev_T24` (control) | 18.994 us | 19.038 us | -1.002 us | -15 ns |
| `chebyshev_U24` (control) | 15.988 us | 16.054 us | -996 ns | 100 ns |
| `legendre_P30` (control) | 72.878 us | 72.874 us | -570 ns | 566 ns |
| `legendre_P38` (control) | 178.520 us | 179.516 us | -115 ns | -690 ns |
| `cyclo_phi17` (control) | 5.103 us | 5.298 us | -826 ns | 210 ns |
| `cyclo_phi41` (control) | 22.805 us | 21.892 us | -892 ns | 20 ns |
| `xpow24_minus1` (control) | -230 ns | 205 ns | -1.258 us | 80 ns |
| `randprod_10` (control) | 37.581 us | 37.861 us | -766 ns | 210 ns |
| `randprod_21` (control) | 66.079 us | 69.138 us | -636 ns | 656 ns |

`%`/Barrett: unweighted median 0.999, time-weighted 1.012, faster-with-`%` on 13 of 24 rows, range 0.92 to 1.02
on the three heaviest rows: [1.022, 1.02, 1.009]
UInt64/UInt32: unweighted median 1.70, time-weighted 1.93, range 1.02 to 1.99

The source-row copy is direction-independent on every row that pays it. The
reciprocal difference is not: on the small rows its sign flips with the
direction, which is the reason it is reported as unresolved there.

Second, the spread of the eight raw reductions of three representative rungs:

| instance | integrated | hoistedPivotRow | flatBothLoops |
|---|---:|---:|---:|
| `sd5` | 4.4% | 11.2% | 9.9% |
| `sd5_shift1` | 32.2% | 7.6% | 3.8% |
| `sd5_shift2` | 2.4% | 9.5% | 3.1% |
| `sd4_x_sd4shift1` | 2.1% | 1.9% | 2.8% |
| `sd5_x_phi11` | 5.8% | 2.4% | 6.0% |
| `xpow48_minus1` | 0.9% | 3.2% | 16.3% |
| `xpow105_minus1` | 3.0% | 1.9% | 4.8% |
| `xpow120_minus1` | 2.5% | 2.2% | 2.1% |
| `cyclo_phi179` | 5.7% | 2.3% | 4.2% |
| `cyclo_phi64_x_phi105` | 3.0% | 1.7% | 3.5% |
| `cyclo_phi128_x_phi165` | 3.5% | 0.8% | 1.4% |
| `cyclo_phi385` | 10.2% | 0.8% | 1.4% |
| `wilkinson_40` | 5.3% | 39.3% | 2.6% |
| `wilkinson_48` | 0.8% | 2.0% | 4.1% |
| `wilkinson_56` | 1.5% | 0.5% | 1.8% |
| `chebyshev_T24` (control) | 11.1% | 21.7% | 3.5% |
| `chebyshev_U24` (control) | 1.3% | 4.1% | 3.9% |
| `legendre_P30` (control) | 1.8% | 2.8% | 2.9% |
| `legendre_P38` (control) | 2.1% | 4.4% | 6.8% |
| `cyclo_phi17` (control) | 2.9% | 30.9% | 7.4% |
| `cyclo_phi41` (control) | 1.2% | 2.8% | 2.2% |
| `xpow24_minus1` (control) | 2.7% | 10.9% | 5.1% |
| `randprod_10` (control) | 3.7% | 4.3% | 2.9% |
| `randprod_21` (control) | 4.9% | 10.6% | 10.2% |

The heavy rows are within a few percent; rows whose whole reduction is tens of
microseconds are not, which is why no sub-percent claim is made about them.

## Allocations

| instance | integrated | hoisted | arrayPivots | flatBothLoops | prototype | rowAdds | skipped |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 122,163 | 122,163 | 122,163 | 121,882 | 120,097 | 215 | 281 |
| `sd5_shift1` | 150,946 | 150,946 | 150,946 | 150,899 | 148,646 | 449 | 47 |
| `sd5_shift2` | 150,477 | 150,477 | 150,477 | 150,436 | 148,171 | 455 | 41 |
| `sd4_x_sd4shift1` | 151,099 | 151,099 | 151,099 | 151,047 | 148,804 | 444 | 52 |
| `sd5_x_phi11` | 265,838 | 265,838 | 265,838 | 265,748 | 262,265 | 935 | 90 |
| `xpow48_minus1` | 53,828 | 53,828 | 53,828 | 52,503 | 50,422 | 38 | 1,325 |
| `xpow105_minus1` | 342,203 | 342,203 | 342,203 | 332,914 | 336,216 | 175 | 9,289 |
| `xpow120_minus1` | 227,904 | 227,904 | 227,904 | 218,381 | 210,396 | 116 | 9,523 |
| `cyclo_phi179` | 275,800 | 275,800 | 275,800 | 245,762 | 273,089 | 1,114 | 30,038 |
| `cyclo_phi64_x_phi105` | 349,007 | 349,007 | 349,007 | 347,754 | 341,535 | 4,277 | 1,253 |
| `cyclo_phi128_x_phi165` | 726,055 | 726,055 | 726,055 | 719,756 | 708,207 | 13,149 | 6,299 |
| `cyclo_phi385` | 663,779 | 663,779 | 663,779 | 625,323 | 641,764 | 17,948 | 38,456 |
| `wilkinson_40` | 20,689 | 20,689 | 20,689 | 20,689 | 15,774 | 0 | 0 |
| `wilkinson_48` | 29,605 | 29,605 | 29,605 | 29,605 | 22,554 | 0 | 0 |
| `wilkinson_56` | 47,122 | 47,122 | 47,122 | 47,122 | 37,551 | 0 | 0 |
| `chebyshev_T24` (control) | 11,098 | 11,098 | 11,098 | 10,727 | 10,682 | 112 | 371 |
| `chebyshev_U24` (control) | 7,708 | 7,708 | 7,708 | 7,346 | 7,215 | 98 | 362 |
| `legendre_P30` (control) | 117,473 | 117,473 | 117,473 | 117,121 | 116,328 | 315 | 352 |
| `legendre_P38` (control) | 233,310 | 233,310 | 233,310 | 232,635 | 232,204 | 620 | 675 |
| `cyclo_phi17` (control) | 2,864 | 2,864 | 2,864 | 2,689 | 2,738 | 50 | 175 |
| `cyclo_phi41` (control) | 15,532 | 15,532 | 15,532 | 14,267 | 14,612 | 100 | 1,265 |
| `xpow24_minus1` (control) | 15,020 | 15,020 | 15,020 | 14,778 | 13,885 | 11 | 242 |
| `randprod_10` (control) | 15,430 | 15,430 | 15,430 | 15,359 | 14,870 | 233 | 71 |
| `randprod_21` (control) | 53,277 | 53,277 | 53,277 | 53,239 | 52,268 | 353 | 38 |

`integrated`, `hoistedPivotRow` and `arrayPivots` report **identical**
small-allocation counts on every row, because an `n`-word row is not a small
allocation and neither is a cons cell chain of a few hundred. That is exactly
why the integration report's 661,844 against 97,269 could not identify the
cause, and why this page had to time it.

## What follows from this

The optimization this attribution points at is **not** in this PR, per the
issue's instruction. It is one change with a measured 64% to 72% share on the
rows where the reduction dominates: read the pivot row once per pivot column in
`Packed.eliminateColumn` and thread it into `Packed.rowAdd`, which is sound
because the pivot row is invariant across its column's elimination. The proof
cost is one more invariant in `rep_eliminateColumn_foldl`. `eliminateHoisted` in
the bench module is the shape it would take, and it agrees with
`Hex.Matrix.nullspace` on all 24 rows here.

Two secondary findings belong in the same follow-up: `Packed.nullspaceArray`'s
per-entry pivot-list search, which is a fifth to a third of the whole span on
high-nullity rows; and the `List.finRange n` column scan, 16% to 24% on the rows
dominated by already-zero columns. Neither is worth touching on the rows the
copy dominates.

## What these measurements do not establish

- **Nothing about a hoisted implementation's proof.** `eliminateHoisted` is a
  bench function with no correspondence theorem. That it computes the right
  answer on 24 instances is not that the equality is provable, only that the
  premise is not obviously wrong.
- **Nothing outside this corpus's moduli**, 3 to 79.
- **The multiply's number is a two-divide throughput increment**, not the cost
  of the shipped divide, and the two loop shapes disagree by 1.4x.
- **The row-write and pivot-accumulation comparisons are coarse mechanism
  swaps**, not exact prices for `Matrix.modifyEntries` or `List.concat`.
- **The bottom rung is the prototype, not an optimum**, and it changes six
  things at once.
- **The stage split's sparse rows carry the counting pass's cache warming**,
  which separating its duration does not remove.
- **Sub-percent effects on rows under 100 us are not resolved** by eight repeats
  on a shared host, and are reported with ranges that say so.
- **No memory-residency measurement.** The counts above are counts of small
  allocations, not bytes.

## Verification

- `lake build` green, `lake build HexConformance` green, zero warnings from the
  changed files.
- `lake exe hexberlekamp_emit_fixtures` and `lake exe hexbz_emit_fixtures`
  reproduce the committed fixtures byte for byte.
- `python3 scripts/bench/factor_phase_profile.py` with the kernel section: the
  counted packed mirror agrees with `Hex.Berlekamp.Packed.reduce` on echelon
  buffer and pivot columns, all twelve ladder rungs agree with
  `Hex.Matrix.nullspace` entry for entry, the four prototype variants still
  agree, and the counted Gauss-Jordan mirror still agrees with the production
  `rowReduce`, on **24 of 24** rows. The wider validation sample agrees with the
  production `factorTrace` on **368 of 368** instances.
- Nothing in `HexBerlekamp/` or any other library changed; the diff is the bench
  module, the driver's merge and validation, and this report.

## Regeneration

```sh
lake build hexbz_factor_service

python3 scripts/bench/factor_phase_profile.py   --no-counterfactual --no-scout --kernel-repeats 8   --output reports/bench-results/hexbz-phase-profile-d01c7146-chungus2.json
```

Use an **even** `--kernel-repeats`: the ladder and the prototype variants flip
their direction on every call, and an odd count leaves the median picking the
majority direction.

The driver exits non-zero if the counted packed mirror disagrees with
`Packed.reduce`, if any ladder rung or packed variant disagrees with
`Hex.Matrix.nullspace`, if any deterministic count or rank disagrees across
repeats, if the counted Gauss-Jordan mirror disagrees with the production row
reduction, or if the recombination mirror disagrees with the production trace.

## Follow-up

https://github.com/kim-em/hex-dev/issues/9166 "Berlekamp packed kernel: hoist
the pivot-row read out of the row addition" carries the one change this
attribution justifies, with the two secondary findings recorded there as out of
its scope. It landed, and
[reports/hexbz-hoisted-pivot-row.md](hexbz-hoisted-pivot-row.md) is its before
and after: the packed reduction on `cyclo_phi385` goes to 0.29x, `mirrored -
hoistedPivotRow` collapses to 0.1% of the rung, and the multiply's incremental
share rises from about 5% to about 17%, which re-opens the Barrett reciprocal.
