# Where the integrated packed kernel's time goes (issue #9160)

[reports/hexbz-packed-fp-matrix-integration.md](hexbz-packed-fp-matrix-integration.md)
measured the landed packed kernel at **2.6x slower than the benchmark prototype
it was derived from**, on the same matrix, in the same process, performing the
same 17,948 row additions, and named candidate causes by inspection. This page
measures them, one factor at a time.

**One cause is 71% of the reduction; every other candidate is under 1%, and one
of them is a saving rather than a cost.** `Hex.Matrix.rowAdd` reads the source
row out with `Hex.Matrix.getRow` before writing, once per row addition. On
`cyclo_phi385` that copy is **32.893 ms of a 46.121 ms reduction, 71.3%**; on
`cyclo_phi128_x_phi165`, 13.890 ms of 19.609 ms, **70.8%**; on the small
`randprod_21`, 72.969 us of 110.795 us, **65.9%**. Amortizing it to one read per
pivot column, which is sound because the pivot row does not change while its
column is eliminated, leaves a reduction that is **0.83x the prototype's** on
the two heaviest rows.

Of the other candidates, isolated one at a time on the same loop:
`Hex.Matrix.modifyEntries`'s `Fin.foldl` closure is **2.5% faster** than writing
the flat buffer directly, not slower; the `List (Fin m)` pivot accumulation is
**0.2%**; and the `List.finRange n` elimination scan is **1.0%** on
`cyclo_phi385` but **21%** on `xpow105_minus1`, whose reduction is dominated by
already-zero columns rather than by arithmetic.

The inner modular multiply is **4.8% of the integrated reduction** on
`cyclo_phi385` and 16.9% of the copy-free one. Both open design points close on
this run without building a variant of the shipped loop; see
[The two open design points](#the-two-open-design-points).

Nothing here is an optimization. The ladder rungs live in the bench module and
nothing reachable from `Hex.ZPoly.factorize` calls them.

## Revision and protocol

- Source revision `49e211a078bbc3e21e686059c5fcf39a0b62c26b` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured 2026-08-04.
  The host was shared with other work throughout. The driver pins itself to one
  idle logical CPU before spawning any service.
- Record `reports/bench-results/hexbz-phase-profile-49e211a0-chungus2.json`,
  SHA-256
  `c9e4b2ed5b290dd826bfcc6517d7a679831764f814c26af585d60fb7cfc8fff7`;
  `hexbz_factor_service` SHA-256
  `a09fa6c1a9935ff17d01d859aa5fb5d866956c39d6376e345fb613586b69dae4`; corpus
  `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- **Seven repeats per instance, in one process, with the ladder run in
  alternating directions** (`[forward, reverse, forward, ...]`, recorded as
  `ladderForward`) so a systematic order effect cancels rather than biasing one
  end. Every rung's reduction is kept per repeat in `reduceNanosSamples`, so
  every difference below is a **median of within-repeat paired differences**,
  reported with its full range, not a difference of two medians of different
  executions.
- **Every rung and the stage mirror are compared against each other and against
  `Hex.Matrix.nullspace` on all 24 rows, and the driver exits non-zero on any
  disagreement**; this run agreed on 24 of 24. Every deterministic count and
  rank is asserted equal across the seven repeats before any duration is
  merged.

Unlike the integration report, every comparison here is *within one run*: the
ladder rungs, the stage mirror and the prototype variants are priced back to
back in the same process on the same instance.

**What this protocol resolves and what it does not.** The repeat spread below is
under 4% on the heavy rows and as much as 54% on rows whose whole reduction is a
few tens of microseconds. Effects at or below a percent are therefore reported
with their paired range, and where that range crosses zero the honest reading is
"not resolved", not "free". Each such case is called out where it appears.

## How the attribution works

Three instruments, all in `bench/HexBench/BerlekampKernel.lean`.

**The stage mirror.** `countedPackedReduce` mirrors
`Hex.Berlekamp.Packed.reduceLoop` column for column, calling the production
`Packed.findPivot?`, `Matrix.rowSwap`, `Packed.rowScale`, `Packed.invMod` and
`Packed.eliminateColumn`, and reads the clock once per pivot column. It is
checked against the production `Packed.reduce` on every call, on echelon buffer
and pivot-column list.

**The ladder.** `ladderLoop` is the same loop with its column elimination passed
in as an argument, called once per pivot column and never in the inner loop.
Each rung differs from the one above it in exactly one place:

| rung | differs from the rung above by |
|---|---|
| `integrated` | (nothing: `Hex.Berlekamp.Packed.reduce` itself, no mirror, no parameter) |
| `mirrored` | running `Packed.eliminateColumn` through `ladderLoop` instead of `Packed.reduceLoop`. The control for the ladder's own scaffolding |
| `hoistedPivotRow` | reading the pivot row once per column instead of once per row addition |
| `arrayPivots` | accumulating the pivot columns in an `Array` with `push` rather than a `List` with `concat` |
| `flatRowWrite` | writing the destination row into the flat buffer directly instead of through `Matrix.modifyEntries`. **The outer scan is still `(List.finRange n).foldl`** |
| `flatBothLoops` | scanning the column with a `Nat` range instead of `List.finRange n` |
| `flatBuffer` | the prototype's `reduce32` on the packed buffer: pivot search, swap, scale, inversion, pivot storage and pivot-row access all change at once. **A residual comparison, not an attribution rung** |

`integrated` against `mirrored` is the control for the ladder's own loop: the
paired median difference is under 1% on every row whose reduction exceeds
100 us, and the ladder's own deltas are therefore taken against `mirrored`, not
against `integrated`, so that ladder overhead cancels.

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
modular multiply against one `UInt32` increment, per inner-loop entry.
`saltedMin - salted` prices the compare and select alone, and it is **not
small** -- see the multiply section -- which is why it is subtracted rather than
left inside the multiply's number.

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
  documents.
- **Aliasing.** Every rung and the stage mirror get their own freshly built
  `Packed.fixedSpace` buffer. `Matrix.getRow` materializes a new vector, so a
  hoisted source row does not share the matrix's backing buffer, and the bottom
  rung consumes `A.data.toArray` without retaining `A`.
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
| `sd5` | 32 | 29 | 822 ns | 4.718 us | 84.355 us | 89.786 us | 7.730 us | 100.068 us | 2.55% |
| `sd5_shift1` | 32 | 29 | 831 ns | 4.678 us | 168.031 us | 173.545 us | 7.403 us | 185.114 us | 2.25% |
| `sd5_shift2` | 32 | 29 | 822 ns | 4.619 us | 171.035 us | 176.475 us | 7.392 us | 187.428 us | 1.90% |
| `sd4_x_sd4shift1` | 32 | 29 | 823 ns | 4.817 us | 165.657 us | 171.292 us | 7.463 us | 183.251 us | 2.45% |
| `sd5_x_phi11` | 42 | 29 | 1.171 us | 8.164 us | 436.917 us | 446.289 us | 13.738 us | 465.120 us | 1.09% |
| `xpow48_minus1` | 48 | 11 | 1.272 us | 10.080 us | 36.123 us | 47.470 us | 16.888 us | 68.832 us | 6.50% |
| `xpow105_minus1` | 105 | 17 | 2.664 us | 54.297 us | 285.681 us | 342.933 us | 101.378 us | 458.660 us | 3.13% |
| `xpow120_minus1` | 120 | 7 | 3.160 us | 55.664 us | 242.844 us | 301.309 us | 102.519 us | 421.404 us | 4.17% |
| `cyclo_phi179` | 178 | 3 | 4.650 us | 165.462 us | 2.388 ms | 2.558 ms | 331.056 us | 2.966 ms | 2.59% |
| `cyclo_phi64_x_phi105` | 80 | 11 | 2.152 us | 34.561 us | 3.585 ms | 3.621 ms | 67.480 us | 3.703 ms | 0.39% |
| `cyclo_phi128_x_phi165` | 144 | 7 | 3.903 us | 108.206 us | 19.602 ms | 19.717 ms | 231.525 us | 19.996 ms | 0.24% |
| `cyclo_phi385` | 240 | 3 | 6.496 us | 292.248 us | 45.815 ms | 46.113 ms | 676.207 us | 46.911 ms | 0.26% |
| `wilkinson_40` | 40 | 47 | 983 ns | 0 ns | 0 ns | 983 ns | 0 ns | 6.239 us | 84.24% |
| `wilkinson_48` | 48 | 61 | 1.191 us | 0 ns | 0 ns | 1.191 us | 0 ns | 7.992 us | 85.10% |
| `wilkinson_56` | 56 | 67 | 1.404 us | 0 ns | 0 ns | 1.404 us | 0 ns | 10.265 us | 86.32% |
| `chebyshev_T24` (control) | 24 | 5 | 761 ns | 4.481 us | 39.689 us | 44.926 us | 7.996 us | 54.951 us | 3.69% |
| `chebyshev_U24` (control) | 24 | 3 | 676 ns | 4.325 us | 35.591 us | 40.604 us | 7.509 us | 50.034 us | 3.84% |
| `legendre_P30` (control) | 30 | 67 | 944 ns | 6.171 us | 119.809 us | 127.081 us | 10.084 us | 140.288 us | 2.23% |
| `legendre_P38` (control) | 38 | 79 | 1.210 us | 10.656 us | 287.170 us | 299.039 us | 17.908 us | 320.966 us | 1.25% |
| `cyclo_phi17` (control) | 16 | 3 | 432 ns | 2.484 us | 14.344 us | 17.259 us | 4.002 us | 22.804 us | 6.77% |
| `cyclo_phi41` (control) | 40 | 3 | 1.173 us | 9.985 us | 63.856 us | 74.993 us | 18.811 us | 97.595 us | 3.88% |
| `xpow24_minus1` (control) | 24 | 11 | 650 ns | 2.624 us | 7.111 us | 10.317 us | 4.066 us | 16.444 us | 12.53% |
| `randprod_10` (control) | 20 | 7 | 560 ns | 3.054 us | 63.154 us | 66.789 us | 5.448 us | 73.970 us | 2.34% |
| `randprod_21` (control) | 24 | 17 | 651 ns | 3.707 us | 108.499 us | 112.889 us | 6.178 us | 121.050 us | 1.64% |

As shares of the three production stages:

| instance | pivot | swap+scale | eliminate |
|---|---:|---:|---:|
| `sd5` | 0.92% | 5.25% | 93.95% |
| `sd5_shift1` | 0.48% | 2.70% | 96.82% |
| `sd5_shift2` | 0.47% | 2.62% | 96.92% |
| `sd4_x_sd4shift1` | 0.48% | 2.81% | 96.71% |
| `sd5_x_phi11` | 0.26% | 1.83% | 97.90% |
| `xpow48_minus1` | 2.68% | 21.23% | 76.10% |
| `xpow105_minus1` | 0.78% | 15.83% | 83.31% |
| `xpow120_minus1` | 1.05% | 18.47% | 80.60% |
| `cyclo_phi179` | 0.18% | 6.47% | 93.36% |
| `cyclo_phi64_x_phi105` | 0.06% | 0.95% | 99.01% |
| `cyclo_phi128_x_phi165` | 0.02% | 0.55% | 99.42% |
| `cyclo_phi385` | 0.01% | 0.63% | 99.35% |
| `wilkinson_40` | 100.00% | 0.00% | 0.00% |
| `wilkinson_48` | 100.00% | 0.00% | 0.00% |
| `wilkinson_56` | 100.00% | 0.00% | 0.00% |
| `chebyshev_T24` (control) | 1.69% | 9.97% | 88.34% |
| `chebyshev_U24` (control) | 1.66% | 10.65% | 87.65% |
| `legendre_P30` (control) | 0.74% | 4.86% | 94.28% |
| `legendre_P38` (control) | 0.40% | 3.56% | 96.03% |
| `cyclo_phi17` (control) | 2.50% | 14.39% | 83.11% |
| `cyclo_phi41` (control) | 1.56% | 13.31% | 85.15% |
| `xpow24_minus1` (control) | 6.30% | 25.43% | 68.93% |
| `randprod_10` (control) | 0.84% | 4.57% | 94.56% |
| `randprod_21` (control) | 0.58% | 3.28% | 96.11% |

The three rows the deliverable names: **`cyclo_phi385` residual 0.26%**,
**`cyclo_phi128_x_phi165` residual 0.24%**, **`randprod_21` (24x24 at p = 17)
residual 1.64%**. Elimination is 99.35%, 99.42% and 96.11% of those three staged
totals; swap and scale is 0.63%, 0.55% and 3.28%; pivot search is 0.01%, 0.02%
and 0.58%. Pivot search exceeds 2% only on `xpow48_minus1`, `cyclo_phi17` and
`xpow24_minus1`, whose whole reductions are 8 to 45 us, and is 100% of the
Wilkinson rows, which have no pivots at all.

**The counting pass is a residual confound, not just an overhead.** It is
reported separately, but it still reads the pivot column's entries immediately
before the elimination writes those rows, so it warms `n` of the `n * m` words
the elimination touches. On the rows where the elimination dominates that is 240
reads against 4.3 million read-modify-writes; on `xpow48_minus1`, where it is
17 us against a 36 us elimination, it is not negligible and that row's stage
proportions should be read with that in mind.

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
| `sd5` | 1.226 ms | 87.690 us | 32.118 us | 1.346 ms | 1.333 ms | +1.0% |
| `sd5_shift1` | 1.569 ms | 170.653 us | 32.238 us | 1.774 ms | 1.759 ms | +0.9% |
| `sd5_shift2` | 1.580 ms | 174.870 us | 32.408 us | 1.786 ms | 1.775 ms | +0.6% |
| `sd4_x_sd4shift1` | 1.585 ms | 168.921 us | 32.699 us | 1.788 ms | 1.767 ms | +1.2% |
| `sd5_x_phi11` | 2.789 ms | 446.052 us | 52.348 us | 3.287 ms | 3.263 ms | +0.8% |
| `xpow48_minus1` | 517.757 us | 44.196 us | 71.446 us | 633.620 us | 604.557 us | +4.8% |
| `xpow105_minus1` | 3.473 ms | 337.231 us | 203.471 us | 4.018 ms | 3.956 ms | +1.6% |
| `xpow120_minus1` | 2.238 ms | 293.675 us | 573.721 us | 3.102 ms | 2.949 ms | +5.2% |
| `cyclo_phi179` | 3.021 ms | 2.566 ms | 175.831 us | 5.777 ms | 5.750 ms | +0.5% |
| `cyclo_phi64_x_phi105` | 3.622 ms | 3.643 ms | 100.609 us | 7.361 ms | 7.354 ms | +0.1% |
| `cyclo_phi128_x_phi165` | 7.610 ms | 19.609 ms | 235.148 us | 27.515 ms | 28.040 ms | -1.9% |
| `cyclo_phi385` | 7.421 ms | 46.121 ms | 429.818 us | 54.169 ms | 53.813 ms | +0.7% |
| `wilkinson_40` | 186.667 us | 3.615 us | 83.163 us | 273.675 us | 222.099 us | +23.2% |
| `wilkinson_48` | 267.917 us | 5.067 us | 120.228 us | 393.694 us | 318.322 us | +23.7% |
| `wilkinson_56` | 436.388 us | 6.730 us | 167.028 us | 610.616 us | 502.936 us | +21.4% |
| `chebyshev_T24` (control) | 117.895 us | 42.443 us | 7.261 us | 167.569 us | 166.677 us | +0.5% |
| `chebyshev_U24` (control) | 82.783 us | 38.517 us | 8.473 us | 129.883 us | 127.189 us | +2.1% |
| `legendre_P30` (control) | 1.193 ms | 125.266 us | 16.955 us | 1.335 ms | 1.330 ms | +0.4% |
| `legendre_P38` (control) | 2.402 ms | 295.939 us | 15.122 us | 2.711 ms | 2.722 ms | -0.4% |
| `cyclo_phi17` (control) | 33.029 us | 15.443 us | 2.594 us | 51.236 us | 51.026 us | +0.4% |
| `cyclo_phi41` (control) | 165.826 us | 71.146 us | 21.792 us | 259.124 us | 255.229 us | +1.5% |
| `xpow24_minus1` (control) | 147.058 us | 8.893 us | 19.238 us | 175.220 us | 166.637 us | +5.2% |
| `randprod_10` (control) | 167.779 us | 65.136 us | 6.650 us | 239.615 us | 238.093 us | +0.6% |
| `randprod_21` (control) | 562.925 us | 110.795 us | 12.118 us | 687.069 us | 681.651 us | +0.8% |

The three stages sum to the production span within **0.7% on `cyclo_phi385`,
-1.9% on `cyclo_phi128_x_phi165` and 0.8% on `randprod_21`**, and within 5.2% on
every row except the three Wilkinson ones.

The Wilkinson overshoot is a known confound, not an unattributed cost. Each rung
converts its basis to `Nat` residues so it can be compared entry for entry
against `Hex.Matrix.nullspace`, and production does not do that. It is
`kernelDimension * n` conversions, which is 960 on `cyclo_phi385` and irrelevant
there, but the Wilkinson rows have rank 0 and therefore `kernelDimension = n`,
so it is 1,600 to 3,136 conversions plus one array per basis vector, against a
whole span of 222 to 503 us.

## The ladder

Reduction time only; build and readback are excluded from every rung.

| instance | integrated | mirrored | hoistedPivotRow | arrayPivots | flatRowWrite | flatBothLoops | flatBuffer |
|---|---|---|---|---|---|---|---|
| `sd5` | 87.690 us | 88.772 us | 35.312 us | 35.843 us | 38.197 us | 34.130 us | 34.711 us |
| `sd5_shift1` | 170.653 us | 170.562 us | 57.235 us | 57.495 us | 63.214 us | 59.528 us | 60.901 us |
| `sd5_shift2` | 174.870 us | 174.869 us | 57.876 us | 58.197 us | 64.386 us | 59.989 us | 61.652 us |
| `sd4_x_sd4shift1` | 168.921 us | 169.151 us | 56.854 us | 57.085 us | 63.093 us | 58.697 us | 61.081 us |
| `sd5_x_phi11` | 446.052 us | 444.108 us | 141.520 us | 141.450 us | 158.094 us | 152.837 us | 158.275 us |
| `xpow48_minus1` | 44.196 us | 44.636 us | 40.460 us | 40.821 us | 42.033 us | 31.797 us | 27.440 us |
| `xpow105_minus1` | 337.231 us | 337.381 us | 269.029 us | 259.425 us | 277.652 us | 208.760 us | 187.608 us |
| `xpow120_minus1` | 293.675 us | 296.891 us | 263.230 us | 255.459 us | 271.352 us | 198.204 us | 176.702 us |
| `cyclo_phi179` | 2.566 ms | 2.538 ms | 1.267 ms | 1.237 ms | 1.337 ms | 1.095 ms | 1.087 ms |
| `cyclo_phi64_x_phi105` | 3.643 ms | 3.633 ms | 1.103 ms | 1.096 ms | 1.215 ms | 1.198 ms | 1.302 ms |
| `cyclo_phi128_x_phi165` | 19.609 ms | 19.606 ms | 5.714 ms | 5.688 ms | 6.282 ms | 6.192 ms | 6.981 ms |
| `cyclo_phi385` | 46.121 ms | 46.117 ms | 13.211 ms | 13.134 ms | 14.413 ms | 13.943 ms | 15.968 ms |
| `wilkinson_40` | 3.615 us | 3.646 us | 3.515 us | 3.715 us | 3.486 us | 3.485 us | 4.337 us |
| `wilkinson_48` | 5.067 us | 4.947 us | 4.928 us | 5.128 us | 4.927 us | 4.928 us | 5.928 us |
| `wilkinson_56` | 6.730 us | 6.770 us | 6.600 us | 6.790 us | 6.579 us | 6.570 us | 8.202 us |
| `chebyshev_T24` (control) | 42.443 us | 42.563 us | 23.104 us | 23.214 us | 24.667 us | 20.580 us | 18.618 us |
| `chebyshev_U24` (control) | 38.517 us | 38.457 us | 21.792 us | 21.502 us | 22.633 us | 19.019 us | 16.615 us |
| `legendre_P30` (control) | 125.266 us | 126.037 us | 48.021 us | 48.472 us | 52.428 us | 46.719 us | 46.229 us |
| `legendre_P38` (control) | 295.939 us | 295.017 us | 105.397 us | 104.976 us | 118.746 us | 105.837 us | 106.068 us |
| `cyclo_phi17` (control) | 15.443 us | 15.814 us | 10.395 us | 10.385 us | 10.526 us | 8.613 us | 7.651 us |
| `cyclo_phi41` (control) | 71.146 us | 71.517 us | 49.343 us | 48.271 us | 51.036 us | 40.240 us | 34.441 us |
| `xpow24_minus1` (control) | 8.893 us | 8.903 us | 9.014 us | 9.384 us | 9.254 us | 7.070 us | 5.979 us |
| `randprod_10` (control) | 65.136 us | 65.197 us | 24.727 us | 24.687 us | 26.710 us | 24.155 us | 22.764 us |
| `randprod_21` (control) | 110.795 us | 110.745 us | 37.987 us | 37.986 us | 41.261 us | 38.587 us | 37.716 us |

### One factor at a time

Each column is the **median of the seven within-repeat differences**, with the
full range of those seven differences in brackets. A range that crosses zero
means the protocol does not resolve that effect on that row.

| instance | source-row copy | List.concat pivots | modifyEntries closure | List.finRange outer scan | residual vs prototype |
|---|---|---|---|---|---|
| `sd5` | 53.389 us [52.979 us, 62.943 us] | -1.121 us [-1.883 us, 822 ns] | -2.675 us [-3.606 us, -1.852 us] | 3.545 us [3.084 us, 4.277 us] | -430 ns [-1.482 us, -10 ns] |
| `sd5_shift1` | 113.367 us [77.185 us, 121.902 us] | -430 ns [-3.085 us, 30.175 us] | -6.559 us [-23.615 us, 24.656 us] | 3.816 us [2.244 us, 21.652 us] | -1.282 us [-5.198 us, 229 ns] |
| `sd5_shift2` | 116.654 us [111.206 us, 118.155 us] | -430 ns [-1.053 us, 2.944 us] | -6.310 us [-39.749 us, -4.187 us] | 4.196 us [-18.316 us, 37.666 us] | -1.282 us [-45.998 us, 17.054 us] |
| `sd4_x_sd4shift1` | 112.648 us [105.366 us, 116.693 us] | 60 ns [-922 ns, 5.920 us] | -5.889 us [-24.337 us, 431 ns] | 4.146 us [2.494 us, 23.766 us] | -2.064 us [-6.009 us, -1.272 us] |
| `sd5_x_phi11` | 302.688 us [287.676 us, 306.956 us] | -80 ns [-89.082 us, 892 ns] | -16.674 us [-48.822 us, -13.219 us] | 4.576 us [-57.566 us, 43.105 us] | -5.088 us [-10.566 us, 57.385 us] |
| `xpow48_minus1` | 3.766 us [1.492 us, 4.216 us] | -652 ns [-2.433 us, 3.305 us] | -1.493 us [-2.814 us, 1.252 us] | 10.475 us [9.074 us, 10.767 us] | 4.046 us [3.024 us, 5.568 us] |
| `xpow105_minus1` | 68.501 us [64.777 us, 75.502 us] | 6.910 us [2.674 us, 10.396 us] | -10.156 us [-16.735 us, -1.671 us] | 70.374 us [66.188 us, 75.232 us] | 17.627 us [13.369 us, 26.318 us] |
| `xpow120_minus1` | 33.861 us [19.048 us, 37.686 us] | 6.829 us [1.773 us, 11.367 us] | -6.570 us [-199.085 us, 1.332 us] | 70.784 us [66.680 us, 266.244 us] | 21.922 us [-101.119 us, 24.136 us] |
| `cyclo_phi179` | 1.275 ms [1.238 ms, 1.998 ms] | 34.732 us [24.687 us, 41.561 us] | -56.835 us [-81.641 us, -47.721 us] | 237.112 us [216.030 us, 253.826 us] | 6.770 us [741 ns, 37.537 us] |
| `cyclo_phi64_x_phi105` | 2.530 ms [2.515 ms, 2.979 ms] | 9.324 us [-130.203 us, 15.063 us] | -111.325 us [-139.697 us, -105.245 us] | 17.195 us [-61.241 us, 49.794 us] | -115.582 us [-151.294 us, 5.358 us] |
| `cyclo_phi128_x_phi165` | 13.890 ms [13.812 ms, 14.295 ms] | 26.140 us [-647.971 us, 35.902 us] | -566.509 us [-595.374 us, -474.674 us] | 77.244 us [-29.404 us, 220.206 us] | -789.371 us [-919.814 us, -744.524 us] |
| `cyclo_phi385` | 32.893 ms [32.663 ms, 33.060 ms] | 88.091 us [72.838 us, 143.845 us] | -1.172 ms [-1.313 ms, -852.824 us] | 474.804 us [192.124 us, 635.913 us] | -2.081 ms [-2.275 ms, -1.715 ms] |
| `wilkinson_40` | 91 ns [-20 ns, 451 ns] | -160 ns [-301 ns, -89 ns] | 30 ns [-20 ns, 80 ns] | 10 ns [-11 ns, 41 ns] | -852 ns [-982 ns, -761 ns] |
| `wilkinson_48` | 20 ns [-21 ns, 180 ns] | -190 ns [-269 ns, -110 ns] | 1 ns [-29 ns, 81 ns] | -10 ns [-81 ns, 40 ns] | -981 ns [-1.062 us, -931 ns] |
| `wilkinson_56` | 161 ns [0 ns, 240 ns] | -190 ns [-240 ns, -180 ns] | 20 ns [-10 ns, 61 ns] | 0 ns [-2.615 us, 20 ns] | -1.613 us [-2.143 us, 1.092 us] |
| `chebyshev_T24` (control) | 19.309 us [19.169 us, 19.830 us] | -341 ns [-1.703 us, 491 ns] | -1.482 us [-2.474 us, -972 ns] | 3.915 us [3.746 us, 4.227 us] | 2.172 us [1.823 us, 2.614 us] |
| `chebyshev_U24` (control) | 16.905 us [12.489 us, 17.446 us] | 290 ns [-470 ns, 4.286 us] | -1.071 us [-1.422 us, 3.455 us] | 3.726 us [3.374 us, 4.116 us] | 2.433 us [-1.392 us, 2.495 us] |
| `legendre_P30` (control) | 78.016 us [75.562 us, 80.199 us] | -670 ns [-992 ns, 1.041 us] | -3.816 us [-5.189 us, -3.414 us] | 5.788 us [4.497 us, 6.470 us] | 470 ns [-8.403 us, 880 ns] |
| `legendre_P38` (control) | 189.951 us [188.420 us, 196.721 us] | 270 ns [-2.173 us, 1.732 us] | -13.680 us [-14.682 us, -9.043 us] | 12.508 us [9.244 us, 14.431 us] | -140 ns [-2.764 us, 1.032 us] |
| `cyclo_phi17` (control) | 5.288 us [5.107 us, 5.679 us] | -270 ns [-832 ns, 370 ns] | -181 ns [-441 ns, 130 ns] | 1.963 us [1.732 us, 2.213 us] | 892 ns [790 ns, 1.151 us] |
| `cyclo_phi41` (control) | 22.184 us [19.380 us, 22.884 us] | 1.201 us [170 ns, 3.955 us] | -1.793 us [-2.364 us, 489 ns] | 10.917 us [10.135 us, 11.407 us] | 5.709 us [5.318 us, 6.198 us] |
| `xpow24_minus1` (control) | -30 ns [-252 ns, 70 ns] | -661 ns [-1.011 us, 210 ns] | -311 ns [-460 ns, -20 ns] | 2.164 us [2.003 us, 2.354 us] | 1.101 us [921 ns, 1.312 us] |
| `randprod_10` (control) | 40.710 us [39.288 us, 41.141 us] | 191 ns [-801 ns, 380 ns] | -2.183 us [-2.404 us, -1.963 us] | 2.444 us [2.244 us, 3.115 us] | 1.392 us [841 ns, 1.832 us] |
| `randprod_21` (control) | 72.969 us [71.305 us, 75.192 us] | -351 ns [-441 ns, 371 ns] | -3.304 us [-4.367 us, -3.115 us] | 2.734 us [180 ns, 3.896 us] | 831 ns [-100 ns, 3.034 us] |

On `cyclo_phi385`, against a 46.121 ms `integrated` reduction:

| factor | paired median | share | resolved? |
|---|---:|---:|---|
| source-row copy (`mirrored - hoistedPivotRow`) | 32.893 ms | **71.3%** | 7/7 repeats same sign |
| `List.concat` pivot accumulation (`hoistedPivotRow - arrayPivots`) | 88.091 us | 0.19% | 7/7 same sign |
| `Matrix.modifyEntries` (`hoistedPivotRow - flatRowWrite`) | **-1.172 ms** | **-2.5%** | 7/7 same sign |
| `List.finRange` column scan (`flatRowWrite - flatBothLoops`) | 474.804 us | 1.03% | 7/7 same sign |
| residual against the prototype (`flatBothLoops - flatBuffer`) | -2.081 ms | -4.5% | 7/7 same sign |

### The source-row copy is the gap

| instance | integrated | mirrored - hoisted (paired median) | share of integrated | ops per column scan |
|---|---:|---:|---:|---:|
| `sd5` | 87.690 us | 53.389 us | 60.9% | 13.9 |
| `sd5_shift1` | 170.653 us | 113.367 us | 66.4% | 29.0 |
| `sd5_shift2` | 174.870 us | 116.654 us | 66.7% | 29.4 |
| `sd4_x_sd4shift1` | 168.921 us | 112.648 us | 66.7% | 28.6 |
| `sd5_x_phi11` | 446.052 us | 302.688 us | 67.9% | 38.3 |
| `xpow48_minus1` | 44.196 us | 3.766 us | 8.5% | 1.3 |
| `xpow105_minus1` | 337.231 us | 68.501 us | 20.3% | 1.9 |
| `xpow120_minus1` | 293.675 us | 33.861 us | 11.5% | 1.4 |
| `cyclo_phi179` | 2.566 ms | 1.275 ms | 49.7% | 6.4 |
| `cyclo_phi64_x_phi105` | 3.643 ms | 2.530 ms | 69.4% | 61.9 |
| `cyclo_phi128_x_phi165` | 19.609 ms | 13.890 ms | 70.8% | 97.4 |
| `cyclo_phi385` | 46.121 ms | 32.893 ms | 71.3% | 76.4 |
| `wilkinson_40` | 3.615 us | 91 ns | 2.5% | 0.0 |
| `wilkinson_48` | 5.067 us | 20 ns | 0.4% | 0.0 |
| `wilkinson_56` | 6.730 us | 161 ns | 2.4% | 0.0 |
| `chebyshev_T24` (control) | 42.443 us | 19.309 us | 45.5% | 5.6 |
| `chebyshev_U24` (control) | 38.517 us | 16.905 us | 43.9% | 5.1 |
| `legendre_P30` (control) | 125.266 us | 78.016 us | 62.3% | 14.2 |
| `legendre_P38` (control) | 295.939 us | 189.951 us | 64.2% | 18.2 |
| `cyclo_phi17` (control) | 15.443 us | 5.288 us | 34.2% | 3.6 |
| `cyclo_phi41` (control) | 71.146 us | 22.184 us | 31.2% | 2.9 |
| `xpow24_minus1` (control) | 8.893 us | -30 ns | -0.3% | 1.0 |
| `randprod_10` (control) | 65.136 us | 40.710 us | 62.5% | 15.3 |
| `randprod_21` (control) | 110.795 us | 72.969 us | 65.9% | 21.7 |

The share tracks the row's ratio of inner-loop entry operations to column scans,
`rowAdds * n` against `rowAdds + rowAddsSkipped`: 76 on `cyclo_phi385`, 97 on
`cyclo_phi128_x_phi165`, 22 on `randprod_21`, but 1.9 on `xpow105_minus1` and
1.0 on `xpow24_minus1`. The copy is `n` words per row addition, so it is charged
only where row additions happen, and rows whose columns are mostly already zero
never pay it.

This is the *net* saving from hoisting, not the gross cost of the copies: the
hoisted rung still reads the pivot row once per pivot column, unconditionally,
including on columns where every elimination is skipped.

### The other candidates

**`Matrix.modifyEntries` is not a cost; it is a saving.** Writing the flat
backing buffer directly, with the outer scan held fixed, is slower on every row
that does arithmetic: 1.172 ms on `cyclo_phi385` (2.5% of the reduction, 8.9% of
the hoisted one), 566 us on `cyclo_phi128_x_phi165`, and the sign is the same on
all seven repeats of both. `Fin.foldl` with a closure over a `Vector` beats a
`Nat`-indexed `Vector.set!` loop here, presumably because the closure body's
index is a `Fin` and needs no bounds test.

**The `List (Fin m)` pivot accumulation is 0.19%.** `List.concat` is `O(length)`
per pivot, so it is `O(rank^2)` cons cells across a reduction, 28,000 on
`cyclo_phi385`. Switching to `Array.push` saves 88 us of 46 ms. It is resolved
in sign on `cyclo_phi385`, `cyclo_phi179`, `xpow105_minus1` and
`xpow120_minus1`, and unresolved (the seven paired differences straddle zero) on
`cyclo_phi128_x_phi165` and `cyclo_phi64_x_phi105`. Either way it is under half
a percent.

**The `List.finRange n` column scan is 1% where arithmetic dominates and 20%
where it does not.** On `cyclo_phi385` it is 475 us of 46 ms. On
`xpow105_minus1` it is 70.374 us of a 337 us reduction, **21%**; on
`xpow120_minus1`, 70.784 us of 294 us, **24%**; on `cyclo_phi41`, 10.917 us of
71 us, **15%**. Those are exactly the rows whose entry-operation to column-scan
ratio is between 1.0 and 2.9: the scan is paid per column entry, the arithmetic
per row entry. On `cyclo_phi128_x_phi165` and `cyclo_phi64_x_phi105` the effect
is not resolved.

**The bottom rung is a residual, not an attribution.** `reduce32` changes pivot
search, swap, scale, inversion, pivot storage and pivot-row access all at once,
and carries its `useBarrett` and `skipZero` flags as runtime `Bool`s tested
inside the inner loop. It is here because it reproduces the prototype column the
2.6x was measured against, to within 0.1% on `cyclo_phi385` (15.968 ms in the
ladder against 15.983 ms in the prototype pricing), and because
`flatBothLoops - flatBuffer` is then the part of the gap the ladder does not
explain. On the two heaviest rows that residual is *negative*: the shipped
loop's scaffolding, with the copy hoisted and both loops flattened, beats the
prototype's by 13% and 11%.

### The basis readback

Not part of the reduction, and a second real finding, with two confounds stated
up front. `Packed.nullspaceArray` searches the pivot-column *list* for every
output entry, so it is `O(kernelDim * m * rank)`; `basisOfBuffer32` scans the
pivot-column `Array` once for the free columns and then scatters only the pivot
entries, `O(kernelDim * (m + rank))` after an `O(m * rank)` free-column scan.
They are different algorithms, not the same algorithm with different constants,
and the `nullspaceArray` column additionally carries the `ZMod64`-to-`Nat`
conversion the rungs do for cross-checking. The factor below is therefore an
end-to-end comparison of two readbacks, not the price of a list.

| instance | kernel dim | rank | nullspaceArray + Nat | basisOfBuffer32 | factor | share of span |
|---|---:|---:|---:|---:|---:|---:|
| `sd5` | 16 | 16 | 32.118 us | 2.063 us | 15.6x | 2.4% |
| `sd5_shift1` | 16 | 16 | 32.238 us | 1.993 us | 16.2x | 1.8% |
| `sd5_shift2` | 16 | 16 | 32.408 us | 2.063 us | 15.7x | 1.8% |
| `sd4_x_sd4shift1` | 16 | 16 | 32.699 us | 2.403 us | 13.6x | 1.9% |
| `sd5_x_phi11` | 17 | 25 | 52.348 us | 3.135 us | 16.7x | 1.6% |
| `xpow48_minus1` | 19 | 29 | 71.446 us | 3.865 us | 18.5x | 11.8% |
| `xpow105_minus1` | 14 | 91 | 203.471 us | 12.389 us | 16.4x | 5.1% |
| `xpow120_minus1` | 39 | 81 | 573.721 us | 20.701 us | 27.7x | 19.5% |
| `cyclo_phi179` | 2 | 176 | 175.831 us | 22.233 us | 7.9x | 3.1% |
| `cyclo_phi64_x_phi105` | 10 | 70 | 100.609 us | 7.871 us | 12.8x | 1.4% |
| `cyclo_phi128_x_phi165` | 8 | 136 | 235.148 us | 17.846 us | 13.2x | 0.8% |
| `cyclo_phi385` | 4 | 236 | 429.818 us | 40.160 us | 10.7x | 0.8% |
| `wilkinson_40` | 40 | 0 | 83.163 us | 1.772 us | 46.9x | 37.4% |
| `wilkinson_48` | 48 | 0 | 120.228 us | 2.764 us | 43.5x | 37.8% |
| `wilkinson_56` | 56 | 0 | 167.028 us | 3.175 us | 52.6x | 33.2% |
| `chebyshev_T24` (control) | 3 | 21 | 7.261 us | 971 ns | 7.5x | 4.4% |
| `chebyshev_U24` (control) | 4 | 20 | 8.473 us | 1.001 us | 8.5x | 6.7% |
| `legendre_P30` (control) | 7 | 23 | 16.955 us | 1.582 us | 10.7x | 1.3% |
| `legendre_P38` (control) | 3 | 35 | 15.122 us | 1.893 us | 8.0x | 0.6% |
| `cyclo_phi17` (control) | 1 | 15 | 2.594 us | 461 ns | 5.6x | 5.1% |
| `cyclo_phi41` (control) | 5 | 35 | 21.792 us | 1.933 us | 11.3x | 8.5% |
| `xpow24_minus1` (control) | 13 | 11 | 19.238 us | 1.222 us | 15.7x | 11.5% |
| `randprod_10` (control) | 4 | 16 | 6.650 us | 761 ns | 8.7x | 2.8% |
| `randprod_21` (control) | 7 | 17 | 12.118 us | 1.092 us | 11.1x | 1.8% |

On the rows where the reduction dominates the readback is under 1% of the span
and does not matter. On high-nullity rows it is a fifth to a third of it.

## The inner modular multiply

`doubled - saltedMin` is one modular multiply against one `UInt32` increment,
per inner-loop entry, over the same entries, in the same loop, with the same
control flow and the same row additions. It is measured in both loop shapes, so
that transferring it between shapes is a measurement rather than an assumption.

| instance | inner multiplies | modifyEntries shape | flat shape | ns/multiply (modifyEntries) | ns/multiply (flat) | share of integrated | share of hoisted |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 6,880 | 3.736 us [3.074 us, 5.890 us] | 2.705 us [169 ns, 3.525 us] | 0.54 ns | 0.39 ns | 4.3% | 10.6% |
| `sd5_shift1` | 14,368 | 8.022 us [7.361 us, 8.683 us] | 5.899 us [4.696 us, 31.186 us] | 0.56 ns | 0.41 ns | 4.7% | 14.0% |
| `sd5_shift2` | 14,560 | 8.152 us [7.432 us, 8.762 us] | 6.029 us [5.027 us, 9.033 us] | 0.56 ns | 0.41 ns | 4.7% | 14.1% |
| `sd4_x_sd4shift1` | 14,208 | 7.722 us [7.591 us, 10.646 us] | 6.349 us [4.416 us, 9.254 us] | 0.54 ns | 0.45 ns | 4.6% | 13.6% |
| `sd5_x_phi11` | 39,270 | 21.112 us [20.331 us, 24.396 us] | 17.996 us [13.019 us, 107.909 us] | 0.54 ns | 0.46 ns | 4.7% | 14.9% |
| `xpow48_minus1` | 1,824 | 1.282 us [-1.151 us, 1.863 us] | 1.092 us [500 ns, 1.943 us] | 0.70 ns | 0.60 ns | 2.9% | 3.2% |
| `xpow105_minus1` | 18,375 | 11.086 us [-208.278 us, 19.199 us] | 7.090 us [6.128 us, 11.588 us] | 0.60 ns | 0.39 ns | 3.3% | 4.1% |
| `xpow120_minus1` | 13,920 | 9.123 us [-4.306 us, 10.926 us] | 7.411 us [2.203 us, 125.245 us] | 0.66 ns | 0.53 ns | 3.1% | 3.5% |
| `cyclo_phi179` | 198,292 | 109.222 us [99.237 us, 386.202 us] | 68.651 us [48.582 us, 79.468 us] | 0.55 ns | 0.35 ns | 4.3% | 8.6% |
| `cyclo_phi64_x_phi105` | 342,160 | 184.863 us [30.405 us, 424.599 us] | 119.427 us [101.962 us, 146.698 us] | 0.54 ns | 0.35 ns | 5.1% | 16.8% |
| `cyclo_phi128_x_phi165` | 1,893,456 | 982.457 us [854.648 us, 990.639 us] | 801.779 us [657.857 us, 1.001 ms] | 0.52 ns | 0.42 ns | 5.0% | 17.2% |
| `cyclo_phi385` | 4,307,520 | 2.229 ms [2.148 ms, 2.344 ms] | 1.479 ms [1.369 ms, 1.780 ms] | 0.52 ns | 0.34 ns | 4.8% | 16.9% |
| `wilkinson_40` | 0 | -10 ns | 30 ns | -- | -- | -- | -- |
| `wilkinson_48` | 0 | 1 ns | 130 ns | -- | -- | -- | -- |
| `wilkinson_56` | 0 | 10 ns | 20 ns | -- | -- | -- | -- |
| `chebyshev_T24` (control) | 2,688 | 1.503 us [1.262 us, 1.612 us] | 1.472 us [912 ns, 3.365 us] | 0.56 ns | 0.55 ns | 3.5% | 6.5% |
| `chebyshev_U24` (control) | 2,352 | 1.362 us [1.131 us, 1.522 us] | 931 ns [-2.073 us, 1.102 us] | 0.58 ns | 0.40 ns | 3.5% | 6.2% |
| `legendre_P30` (control) | 9,450 | 5.449 us [1.833 us, 7.411 us] | 3.686 us [2.213 us, 4.216 us] | 0.58 ns | 0.39 ns | 4.3% | 11.3% |
| `legendre_P38` (control) | 23,560 | 12.809 us [9.083 us, 15.753 us] | 9.735 us [3.545 us, 13.209 us] | 0.54 ns | 0.41 ns | 4.3% | 12.2% |
| `cyclo_phi17` (control) | 800 | 440 ns [311 ns, 520 ns] | 310 ns [130 ns, 791 ns] | 0.55 ns | 0.39 ns | 2.8% | 4.2% |
| `cyclo_phi41` (control) | 4,000 | 2.353 us [-601 ns, 2.604 us] | 1.463 us [922 ns, 1.842 us] | 0.59 ns | 0.37 ns | 3.3% | 4.8% |
| `xpow24_minus1` (control) | 264 | 139 ns [-30 ns, 241 ns] | 381 ns [70 ns, 691 ns] | 0.53 ns | 1.44 ns | 4.3% | 4.2% |
| `randprod_10` (control) | 4,660 | 2.604 us [2.454 us, 5.128 us] | 1.923 us [1.322 us, 6.400 us] | 0.56 ns | 0.41 ns | 4.0% | 10.5% |
| `randprod_21` (control) | 8,472 | 4.567 us [4.427 us, 4.888 us] | 3.394 us [2.483 us, 3.715 us] | 0.54 ns | 0.40 ns | 4.1% | 12.0% |

Per multiply the two shapes do not agree: **0.52 ns in the `modifyEntries` shape
and 0.34 ns in the flat shape** on `cyclo_phi385`, and the same 1.3x to 1.5x
spread on every heavy row. The larger of the two is used for the share, so the
share is the conservative reading: **4.8% of the integrated reduction on
`cyclo_phi385` and 16.9% of the copy-free one**, 5.0% and 17.2% on
`cyclo_phi128_x_phi165`.

**This is an incremental two-divide throughput measurement, not a causal share.**
Two effects push it in opposite directions and neither is quantified: the two
divides in the doubled rung are independent, so the core overlaps them and the
increment measures less than an isolated divide would cost; and the doubled rung
holds one more live value, which costs something the control does not pay. It is
the right order of magnitude for "what would removing the divide be worth", and
it is not a bound in either direction.

The control that makes it that much is the select:

| instance | saltedMin - salted (the select) | salted - flatBothLoops (the salt) |
|---|---:|---:|
| `sd5` | 2.343 us [1.191 us, 3.806 us] | 281 ns [-330 ns, 702 ns] |
| `sd5_shift1` | 4.497 us [3.275 us, 6.889 us] | -20 ns [-1.822 us, 2.313 us] |
| `sd5_shift2` | 4.166 us [3.506 us, 6.890 us] | -430 ns [-21.852 us, 872 ns] |
| `sd4_x_sd4shift1` | 3.626 us [-22.554 us, 4.647 us] | 731 ns [-120 ns, 28.243 us] |
| `sd5_x_phi11` | 8.904 us [7.792 us, 18.146 us] | -2.814 us [-58.878 us, 4.117 us] |
| `xpow48_minus1` | 471 ns [-2.704 us, 1.282 us] | 30 ns [-1.222 us, 3.626 us] |
| `xpow105_minus1` | 5.978 us [-116.041 us, 9.754 us] | -471 ns [-4.647 us, 123.003 us] |
| `xpow120_minus1` | 3.825 us [2.715 us, 7.031 us] | -481 ns [-1.632 us, 391 ns] |
| `cyclo_phi179` | 65.407 us [63.625 us, 90.695 us] | 1.242 us [-3.376 us, 26.148 us] |
| `cyclo_phi64_x_phi105` | 123.984 us [105.236 us, 151.755 us] | -4.016 us [-144.074 us, 16.324 us] |
| `cyclo_phi128_x_phi165` | 521.614 us [378.200 us, 753.677 us] | 8.593 us [-122.522 us, 135.912 us] |
| `cyclo_phi385` | 1.515 ms [1.195 ms, 1.776 ms] | 70.555 us [-55.503 us, 437.839 us] |
| `wilkinson_40` | 1 ns [-10 ns, 50 ns] | 10 ns [-11 ns, 20 ns] |
| `wilkinson_48` | 20 ns [-31 ns, 60 ns] | -11 ns [-91 ns, 31 ns] |
| `wilkinson_56` | 10 ns [-20 ns, 40 ns] | 1 ns [-2.594 us, 40 ns] |
| `chebyshev_T24` (control) | 931 ns [261 ns, 1.012 us] | -151 ns [-370 ns, 189 ns] |
| `chebyshev_U24` (control) | 802 ns [560 ns, 3.306 us] | 29 ns [-201 ns, 290 ns] |
| `legendre_P30` (control) | 2.774 us [661 ns, 4.395 us] | 191 ns [69 ns, 2.384 us] |
| `legendre_P38` (control) | 7.331 us [-19 ns, 13.039 us] | -140 ns [-1.072 us, 5.087 us] |
| `cyclo_phi17` (control) | 392 ns [260 ns, 671 ns] | -100 ns [-330 ns, 1 ns] |
| `cyclo_phi41` (control) | 1.382 us [1.012 us, 1.773 us] | -631 ns [-1.001 us, 20 ns] |
| `xpow24_minus1` (control) | 71 ns [30 ns, 321 ns] | 91 ns [-190 ns, 181 ns] |
| `randprod_10` (control) | 1.593 us [1.231 us, 1.953 us] | -300 ns [-551 ns, 241 ns] |
| `randprod_21` (control) | 2.613 us [1.964 us, 3.876 us] | -561 ns [-2.353 us, 1.411 us] |

The compare and select alone is **1.515 ms on `cyclo_phi385`, comparable to the
multiply itself**. Charging it to the multiply, as a doubled-against-plain
comparison would, overstates the multiply by a factor of two. The salt is free:
its paired range straddles zero on 15 of 24 rows and its median is under 0.2% of
the reduction on every row.

## The two open design points

#9150's verification left two of the prototype's five design factors
unre-measured against the integrated implementation. This run prices both, in
the same process on the same matrices, on the prototype's two storage widths and
two multiply routines.

| instance | UInt64 + Barrett | UInt32 + Barrett | UInt32 + hardware `%` | UInt64/UInt32 | `%`/Barrett |
|---|---:|---:|---:|---:|---:|
| `sd5` | 60.860 us | 35.873 us | 34.942 us | 1.70x | 0.97x |
| `sd5_shift1` | 112.156 us | 62.302 us | 61.882 us | 1.80x | 0.99x |
| `sd5_shift2` | 112.647 us | 62.583 us | 62.453 us | 1.80x | 1.00x |
| `sd4_x_sd4shift1` | 110.934 us | 61.562 us | 61.762 us | 1.80x | 1.00x |
| `sd5_x_phi11` | 292.494 us | 159.096 us | 160.869 us | 1.84x | 1.01x |
| `xpow48_minus1` | 40.590 us | 28.593 us | 27.561 us | 1.42x | 0.96x |
| `xpow105_minus1` | 300.125 us | 189.010 us | 186.266 us | 1.59x | 0.99x |
| `xpow120_minus1` | 275.348 us | 176.852 us | 175.190 us | 1.56x | 0.99x |
| `cyclo_phi179` | 1.911 ms | 1.087 ms | 1.085 ms | 1.76x | 1.00x |
| `cyclo_phi64_x_phi105` | 2.440 ms | 1.302 ms | 1.322 ms | 1.87x | 1.02x |
| `cyclo_phi128_x_phi165` | 13.295 ms | 6.981 ms | 7.038 ms | 1.90x | 1.01x |
| `cyclo_phi385` | 32.827 ms | 15.970 ms | 15.983 ms | 2.06x | 1.00x |
| `wilkinson_40` | 4.867 us | 4.817 us | 4.286 us | 1.01x | 0.89x |
| `wilkinson_48` | 6.359 us | 6.440 us | 5.898 us | 0.99x | 0.92x |
| `wilkinson_56` | 8.553 us | 8.582 us | 8.072 us | 1.00x | 0.94x |
| `chebyshev_T24` (control) | 29.884 us | 19.570 us | 18.697 us | 1.53x | 0.96x |
| `chebyshev_U24` (control) | 26.259 us | 17.396 us | 16.705 us | 1.51x | 0.96x |
| `legendre_P30` (control) | 82.322 us | 47.580 us | 46.399 us | 1.73x | 0.98x |
| `legendre_P38` (control) | 185.695 us | 109.012 us | 107.910 us | 1.70x | 0.99x |
| `cyclo_phi17` (control) | 11.907 us | 8.342 us | 7.721 us | 1.43x | 0.93x |
| `cyclo_phi41` (control) | 53.299 us | 35.713 us | 34.621 us | 1.49x | 0.97x |
| `xpow24_minus1` (control) | 8.913 us | 6.900 us | 6.069 us | 1.29x | 0.88x |
| `randprod_10` (control) | 38.487 us | 23.665 us | 22.844 us | 1.63x | 0.97x |
| `randprod_21` (control) | 64.075 us | 38.477 us | 38.097 us | 1.67x | 0.99x |

`%`/Barrett: unweighted median 0.980, time-weighted 1.003, faster-with-`%` on 19 of 24 rows, range 0.88 to 1.02
on the three heaviest rows: [1.015, 1.008, 1.001]
UInt64/UInt32: unweighted median 1.65, time-weighted 1.98, range 0.99 to 2.06

**`UInt32` versus `UInt64` entries: the shipped choice is the right one, by a
margin no aggregation reverses.** Unweighted median 1.65x, time-weighted 1.98x,
range 0.99x to 2.06x, and below 1.05x only on the three rank-0 Wilkinson rows,
which perform no row additions. The prototype's 2.42x re-measures a little
lower, on a different day and a busier host, but in the same direction and for
the same reason, which is boxing: `lean_box_uint32` is a tagged immediate on a
64-bit runtime and `lean_box_uint64` allocates. This remains a comparison of
`reduce64` against `reduce32`, not of two integrated implementations, so it is
strong corroborating evidence for the shipped choice rather than a
re-measurement of it -- but it is one-directional at every row and every
aggregation, which is what a decision needs.

**Barrett reciprocal versus hardware remainder: a tie this protocol cannot
break.** The two aggregations disagree in sign. Unweighted across 24 rows the
hardware remainder is faster, median 0.980, and it is faster on 19 of 24 rows.
Time-weighted over the whole corpus the two are level at 1.003, and on the three
heaviest rows Barrett is ahead by 1.5%, 0.8% and 0.1%. The unweighted count
gives a 4 us reduction the same vote as a 16 ms one, and the rows where the
hardware remainder wins clearly (0.88x to 0.94x) are the microsecond and rank-0
rows. The defensible statement is **approximately tied, within about 1.5% either
way**, not "closed against Barrett".

**Neither variant should be built.** For the entry width there is nothing to
build: the shipped code already stores `UInt32` and every measurement says so.
For the reciprocal, the whole-reduction effect measured here is at most about
1.5%, its sign depends on how the corpus is weighted, and buying it against the
shipped loop means a second compiled reduction plus the reciprocal's proof
obligations inside the correspondence. Against the 71% the source-row copy costs
on the same rows, that is not where the next measurement should go.

The decision rule #9160 sets resolves through its "not material" branch, but for
a narrower reason than that branch assumes. The multiply is not immaterial in
the abstract: it is about a sixth of what the reduction becomes once the copy is
gone. What is immaterial is either *alternative* to it, and both alternatives are
priced directly in this run rather than inferred. If the source-row copy is ever
removed the multiply's share of the reduction roughly triples, from 4.8% to
16.9% on `cyclo_phi385`, and the reciprocal is worth re-checking then -- against
a direct measurement that still says the swap is worth at most 1.5% of the whole
reduction.

The one thing this leaves open about the multiply is the modulus range. Every
number here is on moduli 3 to 79, far from the `2^31` bound `ZMod64.Bounds`
allows, and the hardware divider's cost is data-dependent. A corpus with moduli
near `2^31` could move both of these conclusions; nothing in this run speaks to
it.

## Repeat spread

The paired ranges above are the primary uncertainty statement. As a summary, the
spread of the seven raw reductions of three representative rungs:

| instance | integrated | hoistedPivotRow | flatBothLoops |
|---|---:|---:|---:|
| `sd5` | 2.7% | 4.8% | 1.9% |
| `sd5_shift1` | 7.2% | 54.5% | 3.2% |
| `sd5_shift2` | 3.5% | 5.9% | 35.3% |
| `sd4_x_sd4shift1` | 7.0% | 13.2% | 3.7% |
| `sd5_x_phi11` | 1.2% | 2.7% | 42.8% |
| `xpow48_minus1` | 5.1% | 9.0% | 5.2% |
| `xpow105_minus1` | 3.7% | 4.8% | 3.5% |
| `xpow120_minus1` | 3.4% | 5.2% | 3.1% |
| `cyclo_phi179` | 17.9% | 2.9% | 3.1% |
| `cyclo_phi64_x_phi105` | 11.9% | 1.2% | 12.3% |
| `cyclo_phi128_x_phi165` | 2.6% | 0.2% | 3.0% |
| `cyclo_phi385` | 0.7% | 1.6% | 3.5% |
| `wilkinson_40` | 3.6% | 2.3% | 0.9% |
| `wilkinson_48` | 1.0% | 2.0% | 2.3% |
| `wilkinson_56` | 1.4% | 0.9% | 39.6% |
| `chebyshev_T24` (control) | 0.8% | 4.0% | 5.9% |
| `chebyshev_U24` (control) | 2.9% | 21.5% | 2.9% |
| `legendre_P30` (control) | 2.5% | 2.8% | 2.4% |
| `legendre_P38` (control) | 2.6% | 1.3% | 2.0% |
| `cyclo_phi17` (control) | 4.5% | 5.2% | 6.7% |
| `cyclo_phi41` (control) | 4.1% | 6.6% | 2.7% |
| `xpow24_minus1` (control) | 35.6% | 8.2% | 8.1% |
| `randprod_10` (control) | 5.9% | 3.1% | 3.8% |
| `randprod_21` (control) | 2.8% | 1.8% | 9.2% |

The heavy rows are within a few percent; rows whose whole reduction is tens of
microseconds are not, which is why no sub-percent claim is made about them.

## Allocations

| instance | integrated | hoisted | arrayPivots | flatBothLoops | prototype | rowAdds | skipped |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 122,162 | 122,162 | 122,162 | 121,881 | 120,097 | 215 | 281 |
| `sd5_shift1` | 150,945 | 150,945 | 150,945 | 150,898 | 148,646 | 449 | 47 |
| `sd5_shift2` | 150,476 | 150,476 | 150,476 | 150,435 | 148,171 | 455 | 41 |
| `sd4_x_sd4shift1` | 151,098 | 151,098 | 151,098 | 151,046 | 148,804 | 444 | 52 |
| `sd5_x_phi11` | 265,837 | 265,837 | 265,837 | 265,747 | 262,265 | 935 | 90 |
| `xpow48_minus1` | 53,827 | 53,827 | 53,827 | 52,502 | 50,422 | 38 | 1,325 |
| `xpow105_minus1` | 342,202 | 342,202 | 342,202 | 332,913 | 336,216 | 175 | 9,289 |
| `xpow120_minus1` | 227,903 | 227,903 | 227,903 | 218,380 | 210,396 | 116 | 9,523 |
| `cyclo_phi179` | 275,799 | 275,799 | 275,799 | 245,761 | 273,089 | 1,114 | 30,038 |
| `cyclo_phi64_x_phi105` | 349,006 | 349,006 | 349,006 | 347,753 | 341,535 | 4,277 | 1,253 |
| `cyclo_phi128_x_phi165` | 726,054 | 726,054 | 726,054 | 719,755 | 708,207 | 13,149 | 6,299 |
| `cyclo_phi385` | 663,778 | 663,778 | 663,778 | 625,322 | 641,764 | 17,948 | 38,456 |
| `wilkinson_40` | 20,688 | 20,688 | 20,688 | 20,688 | 15,774 | 0 | 0 |
| `wilkinson_48` | 29,604 | 29,604 | 29,604 | 29,604 | 22,554 | 0 | 0 |
| `wilkinson_56` | 47,121 | 47,121 | 47,121 | 47,121 | 37,551 | 0 | 0 |
| `chebyshev_T24` (control) | 11,097 | 11,097 | 11,097 | 10,726 | 10,682 | 112 | 371 |
| `chebyshev_U24` (control) | 7,707 | 7,707 | 7,707 | 7,345 | 7,215 | 98 | 362 |
| `legendre_P30` (control) | 117,472 | 117,472 | 117,472 | 117,120 | 116,328 | 315 | 352 |
| `legendre_P38` (control) | 233,309 | 233,309 | 233,309 | 232,634 | 232,204 | 620 | 675 |
| `cyclo_phi17` (control) | 2,863 | 2,863 | 2,863 | 2,688 | 2,738 | 50 | 175 |
| `cyclo_phi41` (control) | 15,531 | 15,531 | 15,531 | 14,266 | 14,612 | 100 | 1,265 |
| `xpow24_minus1` (control) | 15,019 | 15,019 | 15,019 | 14,777 | 13,885 | 11 | 242 |
| `randprod_10` (control) | 15,429 | 15,429 | 15,429 | 15,358 | 14,870 | 233 | 71 |
| `randprod_21` (control) | 53,276 | 53,276 | 53,276 | 53,238 | 52,268 | 353 | 38 |

`integrated`, `hoistedPivotRow` and `arrayPivots` report **identical**
small-allocation counts on every row, because an `n`-word row is not a small
allocation and neither is a cons cell chain of a few hundred. That is exactly
why the integration report's 661,844 against 97,269 could not identify the
cause, and why this page had to time it.

## What follows from this

The optimization this attribution points at is **not** in this PR, per the
issue's instruction. It is one change with a measured 65% to 71% share on the
rows where the reduction dominates: read the pivot row once per pivot column in
`Packed.eliminateColumn` and thread it into `Packed.rowAdd`, which is sound
because the pivot row is invariant across its column's elimination. The proof
cost is one more invariant in `rep_eliminateColumn_foldl`. `eliminateHoisted` in
the bench module is the shape it would take, and it agrees with
`Hex.Matrix.nullspace` on all 24 rows here.

Two secondary findings belong in the same follow-up: `Packed.nullspaceArray`'s
per-entry pivot-list search, which is a fifth to a third of the whole span on
high-nullity rows; and the `List.finRange n` column scan, 15% to 24% on the rows
dominated by already-zero columns. Neither is worth touching on the rows the
copy dominates.

## What these measurements do not establish

- **Nothing about a hoisted implementation's proof.** `eliminateHoisted` is a
  bench function with no correspondence theorem. That it computes the right
  answer on 24 instances is not that the equality is provable, only that the
  premise is not obviously wrong.
- **Nothing outside this corpus's moduli**, 3 to 79.
- **The multiply's number is a two-divide throughput increment**, not the cost
  of the shipped divide, and the two loop shapes disagree by 1.5x.
- **The bottom rung is the prototype, not an optimum**, and it changes six
  things at once.
- **Sub-percent effects on rows under 100 us are not resolved** by seven repeats
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

python3 scripts/bench/factor_phase_profile.py \
  --no-counterfactual --no-scout --kernel-repeats 7 \
  --output reports/bench-results/hexbz-phase-profile-49e211a0-chungus2.json
```

The driver exits non-zero if the counted packed mirror disagrees with
`Packed.reduce`, if any ladder rung or packed variant disagrees with
`Hex.Matrix.nullspace`, if any deterministic count or rank disagrees across
repeats, if the counted Gauss-Jordan mirror disagrees with the production row
reduction, or if the recombination mirror disagrees with the production trace.

## Follow-up

https://github.com/kim-em/hex-dev/issues/9166 "Berlekamp packed kernel: hoist
the pivot-row read out of the row addition" carries the one change this
attribution justifies, with the two secondary findings recorded there as out of
its scope.
