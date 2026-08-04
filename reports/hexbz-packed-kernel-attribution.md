# Where the integrated packed kernel's time goes (issue #9160)

[reports/hexbz-packed-fp-matrix-integration.md](hexbz-packed-fp-matrix-integration.md)
measured the landed packed kernel at **2.6x slower than the benchmark prototype
it was derived from**, on the same matrix, in the same process, performing the
same 17,948 row additions, and named three candidate causes by inspection. This
page measures them.

**One cause is 70% of the reduction and the other two are not costs at all.**
`Hex.Matrix.rowAdd` reads the source row out with `Hex.Matrix.getRow` before
writing, once per row addition. On `cyclo_phi385` that copy is **31.715 ms of a
45.254 ms reduction, 70.1%**; on `cyclo_phi128_x_phi165`, 14.502 ms of
20.349 ms, **71.3%**. Amortizing it to one read per pivot column, which is
sound because the pivot row does not change while its column is eliminated,
leaves a reduction that is **0.84x the prototype's** on both rows. Replacing
`Hex.Matrix.modifyEntries` with a straight-line write costs 2.7% more, not
less, and the prototype's flat `Array` loop is 15.6% slower again.

The inner modular multiply is **7.8% of the integrated reduction** on
`cyclo_phi385` and 26.0% of the copy-free one, at 0.82 ns per multiply. Both
open design points close on this run without building a variant: see
[The two open design points](#the-two-open-design-points-both-close).

Nothing here is an optimization. The ladder rungs live in the bench module and
nothing reachable from `Hex.ZPoly.factorize` calls them.

## Revision and protocol

- Source revision `fca8ee4eb9ed2c4871bd75e10b88d7d9d53f5073` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured 2026-08-04.
  The host was shared with other work throughout. The driver pins itself to one
  idle logical CPU before spawning any service.
- Record `reports/bench-results/hexbz-phase-profile-fca8ee4e-chungus2.json`,
  SHA-256
  `6e99f602fb5a575c7ee5a15d8db625905ff6df02df1a44b1c5934997299187d4`;
  `hexbz_factor_service` SHA-256
  `86b7017cdfbeab4b5b4dadcd6a979bb349796d485bda3f34738b3138e01dc7e0`; corpus
  `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Every number below is a median of three calls in one process on one instance,
  merged by `merge_kernels`, which asserts that the repeats agree on every
  deterministic field before replacing the durations. **Every rung and the
  stage mirror are compared against each other and against
  `Hex.Matrix.nullspace` on all 24 rows, and the driver exits non-zero on any
  disagreement**; this run agreed on 24 of 24.

Unlike the integration report, this page's comparisons are all *within one
run*: the ladder rungs, the stage mirror and the prototype variants are priced
back to back in the same process on the same instance, so the run-to-run
variance that page carries does not apply to the ratios here.

## How the attribution works

Three instruments, all in `bench/HexBench/BerlekampKernel.lean`.

**The stage mirror.** `countedPackedReduce` mirrors
`Hex.Berlekamp.Packed.reduceLoop` column for column, calling the production
`Packed.findPivot?`, `Matrix.rowSwap`, `Packed.rowScale`, `Packed.invMod` and
`Packed.eliminateColumn`, and reads the clock once per pivot column. It is
checked against the production `Packed.reduce` on every call, on echelon buffer
and pivot-column list.

**The ladder.** `ladderLoop` is the same loop with its column elimination
passed in as an argument, called once per pivot column and never in the inner
loop. Each rung drops exactly one scaffolding choice, cumulatively:

| rung | elimination |
|---|---|
| `integrated` | `Hex.Berlekamp.Packed.reduce`, no mirror and no parameter |
| `mirrored` | `Packed.eliminateColumn` verbatim, through `ladderLoop` |
| `hoistedPivotRow` | the same with the pivot row read once per column instead of once per row addition |
| `flatRowWrite` | the same again writing the flat backing buffer directly instead of through `Matrix.modifyEntries` |
| `flatBuffer` | the prototype's `reduce32` on the packed buffer, which additionally drops the `List.finRange` elimination fold, the `List.concat` pivot accumulation, and the pivot-row copy entirely |

`integrated` against `mirrored` is the control for the ladder's own
scaffolding: the median difference is 0.83% and the largest is 7.1%, on
`xpow24_minus1`, whose whole reduction is 8.6 us.

**The multiply.** `eliminateFlatDoubleMul` performs a second modular multiply
per inner-loop entry, on an operand salted by a runtime zero read from an
`IO.Ref`, and combines the two products by `min`. The two products are equal,
so the reduction stays correct and is checked entry for entry like every other
rung; the compiler cannot see that they are equal, so both divisions execute
and neither is eliminated as a common subexpression. `eliminateFlatSalted`
threads the same salt while performing one multiply, and is the control: it
differs from `flatRowWrite` by a median of -0.45%, so the salt itself is free.
The difference `doubled - salted` is the marginal in-situ cost of one modular
multiply over the whole reduction.

### The five traps

- **Let-floating.** This one bit. The first version of the stage mirror charged
  236 columns of elimination **11 us against a 46 ms wall**: `let e :=
  eliminateColumn ...` is consumed only by the tail call, so the compiler moved
  it past the clock read. The mirror now pushes an entry of the eliminated
  buffer into an `IO.Ref` before reading the clock. The generic
  `countedRowReduce` never had the problem because its elimination returns a
  pair and the destructuring pattern match cannot be floated.
- **CSE through a scalar forcing barrier.** Each force carries a
  runtime-varying operand, `probePacked`'s `salt`, for the reason
  `probeEntry` documents.
- **Aliasing.** Every rung and the stage mirror get their own freshly built
  `Packed.fixedSpace` buffer. A buffer shared between two rungs updates in
  place for the first one only and costs the second a full copy per row
  operation.
- **The length index.** No rung mentions
  `basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)`; the pivot
  columns are carried as a list and the basis as a plain `Array`.
- **Marking inside the elimination loop.** Marks are taken once per pivot
  column, never per row operation, so the clock reads are `O(n)` and the loop
  being timed is the loop production runs. On rows where a column's work is
  under a microsecond this is exactly what shows up as the residual; see below.

## The stage split

`wall` is the mirror's own reduction span. `staged` is the sum of its three
stages. The residual is what the marking does not attribute: the loop's
recursion, its counter records, and the clock reads themselves.

| instance | n | p | pivot search | swap + scale | eliminate | staged | wall | residual |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32 | 29 | 862 ns | 12.119 us | 81.649 us | 95.162 us | 99.167 us | 4.04% |
| `sd5_shift1` | 32 | 29 | 810 ns | 10.936 us | 170.553 us | 182.220 us | 185.124 us | 1.57% |
| `sd5_shift2` | 32 | 29 | 840 ns | 10.866 us | 174.389 us | 186.054 us | 188.840 us | 1.48% |
| `sd4_x_sd4shift1` | 32 | 29 | 790 ns | 11.286 us | 162.299 us | 174.379 us | 177.323 us | 1.66% |
| `sd5_x_phi11` | 42 | 29 | 1.161 us | 20.891 us | 435.577 us | 457.510 us | 461.504 us | 0.87% |
| `xpow48_minus1` | 48 | 11 | 1.194 us | 25.910 us | 35.795 us | 62.853 us | 67.420 us | 6.77% |
| `xpow105_minus1` | 105 | 17 | 2.703 us | 158.457 us | 289.922 us | 462.086 us | 476.026 us | 2.93% |
| `xpow120_minus1` | 120 | 7 | 3.140 us | 158.675 us | 245.417 us | 408.664 us | 426.712 us | 4.23% |
| `cyclo_phi179` | 178 | 3 | 4.827 us | 503.071 us | 2.362 ms | 2.891 ms | 2.938 ms | 1.60% |
| `cyclo_phi64_x_phi105` | 80 | 11 | 2.190 us | 102.309 us | 3.727 ms | 3.832 ms | 3.847 ms | 0.40% |
| `cyclo_phi128_x_phi165` | 144 | 7 | 3.913 us | 338.030 us | 20.156 ms | 20.498 ms | 20.541 ms | 0.21% |
| `cyclo_phi385` | 240 | 3 | 6.747 us | 948.230 us | 44.489 ms | 45.451 ms | 45.558 ms | 0.23% |
| `wilkinson_40` | 40 | 47 | 1.039 us | 0 ns | 0 ns | 1.039 us | 6.139 us | 83.08% |
| `wilkinson_48` | 48 | 61 | 1.290 us | 0 ns | 0 ns | 1.290 us | 10.015 us | 87.12% |
| `wilkinson_56` | 56 | 67 | 1.378 us | 0 ns | 0 ns | 1.378 us | 10.325 us | 86.65% |
| `chebyshev_T24` (control) | 24 | 5 | 611 ns | 11.951 us | 39.598 us | 51.757 us | 53.991 us | 4.14% |
| `chebyshev_U24` (control) | 24 | 3 | 670 ns | 11.645 us | 35.583 us | 47.901 us | 50.936 us | 5.96% |
| `legendre_P30` (control) | 30 | 67 | 812 ns | 14.852 us | 117.957 us | 133.421 us | 136.102 us | 1.97% |
| `legendre_P38` (control) | 38 | 79 | 1.102 us | 26.549 us | 281.568 us | 309.348 us | 313.304 us | 1.26% |
| `cyclo_phi17` (control) | 16 | 3 | 400 ns | 6.142 us | 14.250 us | 20.792 us | 22.233 us | 6.48% |
| `cyclo_phi41` (control) | 40 | 3 | 1.164 us | 26.210 us | 61.869 us | 89.221 us | 93.208 us | 4.28% |
| `xpow24_minus1` (control) | 24 | 11 | 582 ns | 6.141 us | 6.758 us | 13.479 us | 15.764 us | 14.50% |
| `randprod_10` (control) | 20 | 7 | 530 ns | 7.472 us | 61.040 us | 68.733 us | 70.274 us | 2.19% |
| `randprod_21` (control) | 24 | 17 | 699 ns | 9.203 us | 104.925 us | 114.798 us | 116.843 us | 1.75% |

The three rows the deliverable names: **`cyclo_phi385` residual 0.23%**,
**`cyclo_phi128_x_phi165` residual 0.21%**, **`randprod_21` (24x24 at p = 17)
residual 1.75%**. Elimination is 97.7%, 98.1% and 89.8% of those three walls;
swap and scale is 2.1%, 1.6% and 7.9%; pivot search is under 0.02% everywhere
and never exceeds 6.7 us on any row.

**The three Wilkinson rows are the instrument, not the loop.** Their
fixed-space matrix is zero, so no column has a pivot, no row is ever added, and
the only stage that runs is pivot search. The 5 to 9 us residual is 2 clock
reads per free column over 40 to 56 columns at roughly 60 ns a read. That is
the honest reading: on a reduction that does no arithmetic, the marking is the
cost. It is reported rather than absorbed, and it is why the residual is stated
as a percentage of the wall and not folded into a stage.

## The whole span

The ladder's `integrated` rung splits `fixedSpaceKernelVectors` into the same
three stages the prototype's column has: build, reduce, read the basis back.
`build` is `Packed.fixedSpace`, which contains the Frobenius power and the
column-polynomial recurrence.

| instance | build | reduce | readback | sum | `fixedSpaceKernelVectors` | residual |
|---|---:|---:|---:|---:|---:|---:|
| `sd5` | 1.239 ms | 85.226 us | 32.278 us | 1.357 ms | 1.340 ms | +1.2% |
| `sd5_shift1` | 1.633 ms | 173.427 us | 32.258 us | 1.839 ms | 1.804 ms | +1.9% |
| `sd5_shift2` | 1.622 ms | 177.343 us | 32.117 us | 1.832 ms | 1.812 ms | +1.1% |
| `sd4_x_sd4shift1` | 1.639 ms | 166.257 us | 32.418 us | 1.838 ms | 1.812 ms | +1.4% |
| `sd5_x_phi11` | 2.826 ms | 439.952 us | 51.876 us | 3.321 ms | 3.324 ms | -0.1% |
| `xpow48_minus1` | 527.883 us | 44.636 us | 71.316 us | 643.384 us | 615.352 us | +4.6% |
| `xpow105_minus1` | 3.547 ms | 341.356 us | 208.239 us | 4.094 ms | 4.073 ms | +0.5% |
| `xpow120_minus1` | 2.294 ms | 304.401 us | 564.717 us | 3.161 ms | 3.020 ms | +4.7% |
| `cyclo_phi179` | 3.140 ms | 2.551 ms | 178.935 us | 5.878 ms | 5.829 ms | +0.8% |
| `cyclo_phi64_x_phi105` | 3.728 ms | 3.754 ms | 102.992 us | 7.596 ms | 7.614 ms | -0.2% |
| `cyclo_phi128_x_phi165` | 7.877 ms | 20.349 ms | 230.141 us | 28.457 ms | 28.311 ms | +0.5% |
| `cyclo_phi385` | 7.555 ms | 45.254 ms | 384.250 us | 53.420 ms | 52.413 ms | +1.9% |
| `wilkinson_40` | 187.969 us | 3.575 us | 80.109 us | 271.653 us | 222.811 us | +21.9% |
| `wilkinson_48` | 270.712 us | 5.057 us | 118.776 us | 394.585 us | 322.448 us | +22.4% |
| `wilkinson_56` | 446.292 us | 6.690 us | 170.663 us | 623.083 us | 511.228 us | +21.9% |
| `chebyshev_T24` (control) | 121.520 us | 42.523 us | 7.201 us | 171.074 us | 169.461 us | +1.0% |
| `chebyshev_U24` (control) | 85.306 us | 38.587 us | 8.583 us | 132.336 us | 131.194 us | +0.9% |
| `legendre_P30` (control) | 1.234 ms | 122.452 us | 17.005 us | 1.376 ms | 1.363 ms | +0.9% |
| `legendre_P38` (control) | 2.451 ms | 288.858 us | 15.042 us | 2.756 ms | 2.750 ms | +0.2% |
| `cyclo_phi17` (control) | 33.330 us | 15.393 us | 2.684 us | 51.606 us | 51.646 us | -0.1% |
| `cyclo_phi41` (control) | 167.588 us | 69.373 us | 21.492 us | 260.396 us | 252.745 us | +3.0% |
| `xpow24_minus1` (control) | 149.762 us | 8.573 us | 18.688 us | 177.012 us | 169.391 us | +4.5% |
| `randprod_10` (control) | 165.194 us | 62.924 us | 6.349 us | 236.360 us | 233.847 us | +1.1% |
| `randprod_21` (control) | 561.592 us | 107.429 us | 11.948 us | 680.969 us | 678.886 us | +0.3% |

The three stages sum to the production span within **1.9% on `cyclo_phi385`,
0.5% on `cyclo_phi128_x_phi165` and 0.3% on `randprod_21`**, and within 5% on
every row except the three Wilkinson ones.

The Wilkinson overshoot is a known confound, not an unattributed cost. Each
rung converts its basis to `Nat` residues so it can be compared entry for entry
against `Hex.Matrix.nullspace`, and production does not do that. It is
`kernelDimension * n` conversions, which is 960 on `cyclo_phi385` and
irrelevant there, but the Wilkinson rows have rank 0 and therefore
`kernelDimension = n`, so it is 1,600 to 3,136 conversions plus one array per
basis vector, against a whole span of 223 to 511 us.

## The scaffolding ladder

Reduction time only; build and readback are excluded from every rung.

| instance | integrated | mirrored | hoisted pivot row | flat row write | prototype loop |
|---|---:|---:|---:|---:|---:|
| `sd5` | 85.226 us | 85.627 us | 36.434 us | 34.311 us | 34.741 us |
| `sd5_shift1` | 173.427 us | 173.407 us | 58.476 us | 59.308 us | 62.592 us |
| `sd5_shift2` | 177.343 us | 174.999 us | 58.987 us | 59.729 us | 60.810 us |
| `sd4_x_sd4shift1` | 166.257 us | 167.989 us | 58.146 us | 58.848 us | 60.971 us |
| `sd5_x_phi11` | 439.952 us | 444.038 us | 148.130 us | 154.429 us | 157.484 us |
| `xpow48_minus1` | 44.636 us | 47.741 us | 42.363 us | 32.008 us | 27.672 us |
| `xpow105_minus1` | 341.356 us | 344.871 us | 278.593 us | 212.555 us | 187.417 us |
| `xpow120_minus1` | 304.401 us | 302.108 us | 269.930 us | 202.180 us | 175.140 us |
| `cyclo_phi179` | 2.551 ms | 2.547 ms | 1.302 ms | 1.115 ms | 1.084 ms |
| `cyclo_phi64_x_phi105` | 3.754 ms | 3.756 ms | 1.131 ms | 1.208 ms | 1.323 ms |
| `cyclo_phi128_x_phi165` | 20.349 ms | 20.273 ms | 5.847 ms | 6.168 ms | 6.987 ms |
| `cyclo_phi385` | 45.254 ms | 44.843 ms | 13.539 ms | 13.902 ms | 16.067 ms |
| `wilkinson_40` | 3.575 us | 3.755 us | 3.555 us | 3.516 us | 4.467 us |
| `wilkinson_48` | 5.057 us | 5.218 us | 4.967 us | 4.927 us | 6.209 us |
| `wilkinson_56` | 6.690 us | 6.911 us | 6.620 us | 6.570 us | 8.212 us |
| `chebyshev_T24` (control) | 42.523 us | 42.804 us | 24.156 us | 20.450 us | 18.948 us |
| `chebyshev_U24` (control) | 38.587 us | 38.958 us | 22.604 us | 19.339 us | 16.785 us |
| `legendre_P30` (control) | 122.452 us | 123.222 us | 48.983 us | 46.519 us | 46.909 us |
| `legendre_P38` (control) | 288.858 us | 288.918 us | 107.450 us | 107.760 us | 107.280 us |
| `cyclo_phi17` (control) | 15.393 us | 16.094 us | 10.776 us | 8.953 us | 7.891 us |
| `cyclo_phi41` (control) | 69.373 us | 69.693 us | 48.992 us | 40.060 us | 35.042 us |
| `xpow24_minus1` (control) | 8.573 us | 9.183 us | 9.184 us | 7.201 us | 6.289 us |
| `randprod_10` (control) | 62.924 us | 63.254 us | 24.807 us | 23.905 us | 22.754 us |
| `randprod_21` (control) | 107.429 us | 108.150 us | 39.047 us | 38.537 us | 37.676 us |

### The source-row copy is the gap

| instance | integrated | source-row copy | share | what is left |
|---|---:|---:|---:|---:|
| `cyclo_phi385` | 45.254 ms | 31.715 ms | **70.1%** | 13.539 ms |
| `cyclo_phi128_x_phi165` | 20.349 ms | 14.502 ms | **71.3%** | 5.847 ms |
| `cyclo_phi64_x_phi105` | 3.754 ms | 2.622 ms | 69.9% | 1.131 ms |
| `sd5_shift1` | 173.427 us | 114.951 us | 66.3% | 58.476 us |
| `randprod_21` (control) | 107.429 us | 68.382 us | **63.7%** | 39.047 us |
| `legendre_P38` (control) | 288.858 us | 181.408 us | 62.8% | 107.450 us |
| `cyclo_phi179` | 2.551 ms | 1.250 ms | 49.0% | 1.302 ms |
| `chebyshev_T24` (control) | 42.523 us | 18.367 us | 43.2% | 24.156 us |
| `cyclo_phi41` (control) | 69.373 us | 20.381 us | 29.4% | 48.992 us |
| `xpow105_minus1` | 341.356 us | 62.763 us | 18.4% | 278.593 us |
| `xpow120_minus1` | 304.401 us | 34.471 us | 11.3% | 269.930 us |
| `xpow48_minus1` | 44.636 us | 2.273 us | 5.1% | 42.363 us |
| `wilkinson_40` | 3.575 us | 20 ns | 0.6% | 3.555 us |
| `xpow24_minus1` (control) | 8.573 us | -611 ns | -7.1% | 9.184 us |

The share tracks the row's ratio of inner-loop entry operations to
column scans, `rowAdds * n` against `rowAdds + rowAddsSkipped`: 76 on
`cyclo_phi385`, 97 on `cyclo_phi128_x_phi165`, 22 on `randprod_21`, but 1.9 on
`xpow105_minus1` and 1.0 on `xpow24_minus1`. The copy is `n` words per row
addition, so it is charged only where row additions actually happen, and rows
whose columns are mostly already zero never pay it. On those rows the
per-column scaffolding dominates instead, and the number is inside the noise:
`xpow24_minus1`'s -7.1% is -611 ns on a 8.6 us reduction, smaller than the 7.1%
its `mirrored` control also moves.

### The other two named causes are not costs

| instance | hoisted | flat row write | prototype loop | flat / hoisted | prototype / hoisted |
|---|---:|---:|---:|---:|---:|
| `cyclo_phi385` | 13.539 ms | 13.902 ms | 16.067 ms | +2.7% | +18.7% |
| `cyclo_phi128_x_phi165` | 5.847 ms | 6.168 ms | 6.987 ms | +5.5% | +19.5% |
| `cyclo_phi64_x_phi105` | 1.131 ms | 1.208 ms | 1.323 ms | +6.8% | +17.0% |
| `randprod_21` (control) | 39.047 us | 38.537 us | 37.676 us | -1.3% | -3.5% |
| `xpow105_minus1` | 278.593 us | 212.555 us | 187.417 us | -23.7% | -32.7% |
| `xpow120_minus1` | 269.930 us | 202.180 us | 175.140 us | -25.1% | -35.1% |
| `cyclo_phi41` (control) | 48.992 us | 40.060 us | 35.042 us | -18.2% | -28.5% |

`Hex.Matrix.modifyEntries`'s `Fin.foldl` closure, named as cause 2 by the
integration report, is **not a cost on the rows where the reduction dominates**:
writing the flat buffer directly is 2.7% to 6.8% *slower* on the three heaviest
rows. Neither is the prototype's flat `Array` loop, which is 17% to 19% slower
again once the copy is amortized. On those rows **the shipped loop with the
copy hoisted would be 0.84x, 0.84x and 0.86x the prototype's time**, that is,
faster than the code the 2.6x was measured against.

Cause 3, the `List.finRange n` elimination fold and the `List.concat` pivot
accumulation, *is* real, but only where the reduction is dominated by
already-zero columns: on `xpow105_minus1`, `xpow120_minus1` and
`cyclo_phi41` the two flat rungs are 18% to 35% faster, and those are precisely
the rows whose entry-operation to column-scan ratio is between 1.0 and 2.9. The
scaffolding is paid per column scan; the arithmetic is paid per entry.

One caveat on the bottom rung: `reduce32` carries its `useBarrett` and
`skipZero` flags as runtime `Bool`s tested inside the inner loop, which the
production path does not do. It is the right comparison target here because it
reproduces the prototype column of the integration report to within 1%
(16.067 ms against that column's own 16.205 ms on `cyclo_phi385` in this run),
but it is not a lower bound on what a flat loop can do.

### The basis readback

Not one of the three named causes, and a second real finding.
`Packed.nullspaceArray` walks the pivot-column *list* per entry;
`basisOfBuffer32` scans a pivot-column `Array`. Same asymptotics, very
different constants.

| instance | kernel dim | `nullspaceArray` | `basisOfBuffer32` | factor | share of span |
|---|---:|---:|---:|---:|---:|
| `cyclo_phi385` | 4 | 384.250 us | 35.032 us | 11.0x | 0.7% |
| `cyclo_phi128_x_phi165` | 8 | 230.141 us | 15.754 us | 14.6x | 0.8% |
| `randprod_21` (control) | 7 | 11.948 us | 1.202 us | 9.9x | 1.8% |
| `xpow120_minus1` | 39 | 564.717 us | 17.997 us | 31.4x | 18.7% |
| `wilkinson_56` | 56 | 170.663 us | 3.234 us | 52.8x | 33.4% |

The `nullspaceArray` column includes the `Nat` conversion the rungs do for
cross-checking, which is `kernelDimension * n` conversions; that is what makes
the Wilkinson factor an upper bound rather than a clean one. On the rows where
the reduction dominates the readback is under 1% of the span and does not
matter. On high-nullity rows it is a fifth to a third of it.

## The inner modular multiply

`doubled - salted` is one extra modular multiply per inner-loop entry, over the
same entries, in the same loop, with the same control flow and the same row
additions.

| instance | salted | doubled | marginal multiply | inner multiplies | per multiply | share of `integrated` | share of `hoisted` |
|---|---:|---:|---:|---:|---:|---:|---:|
| `cyclo_phi385` | 13.844 ms | 17.358 ms | 3.515 ms | 4,307,520 | 0.82 ns | **7.8%** | **26.0%** |
| `cyclo_phi128_x_phi165` | 6.141 ms | 7.688 ms | 1.547 ms | 1,893,456 | 0.82 ns | **7.6%** | **26.5%** |
| `randprod_21` (control) | 38.267 us | 44.777 us | 6.510 us | 8,472 | 0.77 ns | **6.1%** | **16.7%** |
| `cyclo_phi64_x_phi105` | 1.175 ms | 1.453 ms | 278.833 us | 342,160 | 0.81 ns | 7.4% | 24.6% |
| `cyclo_phi179` | 1.103 ms | 1.251 ms | 147.928 us | 198,292 | 0.75 ns | 5.8% | 11.4% |
| `sd5_x_phi11` | 151.674 us | 185.946 us | 34.272 us | 39,270 | 0.87 ns | 7.8% | 23.1% |
| `legendre_P38` (control) | 104.135 us | 122.662 us | 18.527 us | 23,560 | 0.79 ns | 6.4% | 17.2% |
| `xpow105_minus1` | 211.323 us | 223.542 us | 12.219 us | 18,375 | 0.66 ns | 3.6% | 4.4% |
| `xpow120_minus1` | 205.635 us | 212.315 us | 6.680 us | 13,920 | 0.48 ns | 2.2% | 2.5% |
| `wilkinson_40` | 3.505 us | 3.505 us | 0 ns | 0 | -- | 0.0% | 0.0% |

Across the 19 rows that perform at least a thousand inner multiplies the
marginal cost is **0.48 to 0.87 ns, median 0.78 ns**, which on a 3.15 GHz part
is about 2.5 cycles. The corpus's moduli are 3 to 79, so the dividend of the
`UInt64` remainder is tiny and the hardware divider takes its short path.

**This is a lower bound on the share, and it is stated as one.** The two
multiplies in the doubled rung are independent, so they overlap in the
out-of-order window; removing the multiply entirely would save at least the
marginal cost and possibly more. It is a lower bound in the direction that
matters: it says the multiply is *at least* 7.8% of the shipped reduction on
`cyclo_phi385` and *at least* 26.0% of what the reduction becomes once the
source-row copy is gone.

## The two open design points, both close

#9150's verification left two of the prototype's five design factors
unre-measured against the integrated implementation. This run settles both, and
neither needs a variant of the shipped loop built.

**`UInt32` versus `UInt64` entries: confirmed, and the shipped choice is
already the right one.** The prototype's two storage widths are priced in this
same run, back to back, on the same matrix:

| instance | `UInt64` + Barrett | `UInt32` + Barrett | factor |
|---|---:|---:|---:|
| `cyclo_phi385` | 33.065 ms | 15.962 ms | 2.07x |
| `cyclo_phi128_x_phi165` | 13.278 ms | 7.067 ms | 1.88x |
| `cyclo_phi64_x_phi105` | 2.432 ms | 1.307 ms | 1.86x |
| `randprod_21` (control) | 64.215 us | 38.577 us | 1.66x |
| `wilkinson_40` | 4.958 us | 5.097 us | 0.97x |

Median 1.61x over 24 rows, and below 1.05x only on the three rank-0 Wilkinson
rows, which perform no row additions. The shipped code already stores `UInt32`
words, so the open question was whether that choice was justified, and it is:
1.26x to 2.07x on every row that does any arithmetic. There is nothing to
build. The prototype's 2.42x re-measures a little lower here, on a different
day and a busier host, but in the same direction and for the same reason, which
is boxing: `lean_box_uint32` is a tagged immediate on a 64-bit runtime and
`lean_box_uint64` allocates.

**Barrett reciprocal versus hardware remainder: closed against Barrett.** Same
run, same rows:

| | hardware `%` / Barrett |
|---|---:|
| rows where the hardware remainder is faster | **20 of 24** |
| median | 0.983 |
| range | 0.85 to 1.02 |

The hardware remainder is faster than the Barrett reciprocal on 20 of 24 rows,
by 1.7% at the median, and the four rows where Barrett wins do so by at most
2%. The marginal-multiply measurement says why: at 0.78 ns a multiply the
divider is already about as cheap as the `mulHi`, multiply, subtract and
conditional subtract that Barrett would replace it with, on this corpus's
moduli. Building a Barrett variant of the shipped loop would be measuring a
swap that is a wash at best and a small loss at the median.

So the decision rule resolves the way the "not material" branch does, but for a
stronger reason than that branch assumes. The multiply is not immaterial: it is
at least a quarter of what the reduction becomes once the copy is gone. What is
immaterial is either *alternative* to it, and both alternatives are priced
directly in this run rather than inferred. **Neither variant should be
built.** The prototype's numbers stand as the reason the choices were made, and
this run confirms them on the same host with the shipped code in the same
process.

The one thing this leaves open about the multiply is the modulus range. Every
number here is on moduli 3 to 79, far from the `2^31` bound `ZMod64.Bounds`
allows, and the hardware divider's cost is data-dependent. A corpus with
moduli near `2^31` could move both of these conclusions; nothing in this run
speaks to it.

## What follows from this

The optimization this attribution points at is **not** in this PR, per the
issue's instruction. It is one change with a measured 70% share on the rows
where the reduction dominates: read the pivot row once per pivot column in
`Packed.eliminateColumn` and thread it into `Packed.rowAdd`, which is sound
because the pivot row is invariant across its column's elimination. The proof
cost is one more invariant in `rep_eliminateColumn_foldl`. `eliminateHoisted`
in the bench module is the shape it would take, and it agrees with
`Hex.Matrix.nullspace` on all 24 rows here.

Two secondary findings ride along and belong in the same follow-up:
`Packed.nullspaceArray`'s list walk, which is 11x to 53x the array scan and a
fifth to a third of the whole span on high-nullity rows; and the per-column
`List.finRange` scaffolding, which is 18% to 35% on the rows dominated by
already-zero columns.

## What these measurements do not establish

- **Nothing about a hoisted implementation's proof.** `eliminateHoisted` is a
  bench function with no correspondence theorem. That it computes the right
  answer on 24 instances is not that the equality is provable, only that the
  premise is not obviously wrong.
- **Nothing outside this corpus's moduli**, 3 to 79. See the last paragraph of
  the multiply section.
- **The marginal multiply is a lower bound**, not the multiply's cost. See the
  multiply section.
- **The bottom rung is the prototype, not an optimum.** `reduce32` tests two
  runtime flags inside its inner loop.
- **No memory-residency measurement.** The allocation counts in the record are
  counts of small allocations, not bytes, and the source-row copies do not
  appear in them at all: `integrated` and `hoistedPivotRow` report *identical*
  small-allocation counts on every row, because an `n`-word row is not a small
  allocation. That is exactly why the integration report's 661,844 against
  97,269 could not identify the cause, and why this page had to time it.

## Verification

- `lake build` green, `lake build HexConformance` green, zero warnings from the
  changed files.
- `lake exe hexberlekamp_emit_fixtures` and `lake exe hexbz_emit_fixtures`
  reproduce the committed fixtures byte for byte.
- `python3 scripts/bench/factor_phase_profile.py` with the kernel section: the
  counted packed mirror agrees with `Hex.Berlekamp.Packed.reduce` on echelon
  buffer and pivot columns, all seven ladder rungs agree with
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
  --no-counterfactual --no-scout \
  --output reports/bench-results/hexbz-phase-profile-fca8ee4e-chungus2.json
```

The driver exits non-zero if the counted packed mirror disagrees with
`Packed.reduce`, if any ladder rung or packed variant disagrees with
`Hex.Matrix.nullspace`, if the counted Gauss-Jordan mirror disagrees with the
production row reduction, or if the recombination mirror disagrees with the
production trace.
