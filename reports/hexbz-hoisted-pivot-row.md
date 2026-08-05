# Hoisting the packed pivot-row read (issue #9166)

[reports/hexbz-packed-kernel-attribution.md](hexbz-packed-kernel-attribution.md)
measured `Hex.Matrix.getRow`'s source-row copy inside
`Hex.Berlekamp.Packed.rowAdd` at 70.4% of the packed reduction on
`cyclo_phi385`, 71.5% on `cyclo_phi128_x_phi165` and 63.7% on `randprod_21`, as
the median of eight within-repeat paired differences. This page records what
happened when that read was hoisted out of the row addition and taken once per
pivot column instead.

**The packed reduction on `cyclo_phi385` goes from 45.095 ms to 13.260 ms,
0.29x, and the whole `Hex.ZPoly.factorize` call on that row goes from 143.566 ms
to 115.069 ms, 0.80x.** The reduction is now **0.83x the prototype it was
2.80x slower than**, and 0.82x on `cyclo_phi128_x_phi165` against 2.76x before,
which is what #9160 projected from the `hoistedPivotRow` ladder rung.

The saving tracks one count and nothing else: the pivot row was read once per
row addition and is now read once per pivot column, so a row saves
`rowAdds - pivots` copies of `n` words. On the two rows where those counts are
equal (`xpow24_minus1`, 11 and 11) or both zero (the three Wilkinson rows) there
is no saving to have, and none is measured.

## Revision and protocol

- Source revision `dcecc57e`, this PR's first commit: `a5a55cbf` plus the hoist.
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured 2026-08-05.
  The host was shared with other work throughout. The driver pins itself to one
  idle logical CPU before spawning any service; all three runs below landed on
  cpu 1.
- Three runs, in the order **after, before, after**, so the before run is
  bracketed by two after runs on the same host within six minutes:

  | record | `hexbz_factor_service` SHA-256 | `HexBerlekamp/PackedKernel.lean` |
  |---|---|---|
  | `hexbz-phase-profile-dcecc57e-chungus2.json` | `fcc8436a...` | hoisted |
  | `hexbz-phase-profile-a5a55cbf-chungus2.json` | `f2865db2...` | at `a5a55cbf`, the parent commit |
  | `hexbz-phase-profile-dcecc57e-chungus2-rerun.json` | `fcc8436a...` | hoisted |

  The before run was taken with `HexBerlekamp/PackedKernel.lean` and
  `bench/HexBench/BerlekampKernel.lean` checked out at the parent commit and the
  rest of the tree unchanged, so all three records carry the same `git_commit`
  (`55fc3bee`, this branch's pre-rebase SHA for the tree the runs were taken on)
  with `git_dirty` set. The service binary's SHA-256 is what distinguishes them,
  and the two after runs share one binary.
- Record SHA-256s:
  `2b3c505288973e75e9173a852cd85bfb6df0d63d1ca0cf6d636655e54d702390`,
  `17e6ce73388727eed4ae585ece66f5795503cf45e686d4af9bb749b1cc1238f3`,
  `1a18cff40b47b3110988b0d10aee1bf2ad88a5cda49187952279bb6114fa2a42`;
  corpus `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Eight repeats per instance per run, in one process, with the ladder rungs and
  the prototype variants run in alternating directions. Every rung's reduction
  is kept per repeat in `reduceNanosSamples`, so every difference *within* a run
  is a median of within-repeat paired differences, and every table below that
  compares one run against another states both runs' full sample ranges rather
  than a paired difference, because there is no pairing across processes.
- Every ladder rung, the stage mirror and the four prototype variants are
  compared against `Hex.Matrix.nullspace` on all 24 rows in each run, and the
  driver exits non-zero on any disagreement. All three runs agreed on 24 of 24,
  and the wider validation sample agreed with the production `factorTrace` on
  368 of 368 instances in each.

## What changed

`Packed.eliminateColumn` reads the pivot row once, before the fold, and threads
it into the new `Packed.rowAddFrom`:

```lean
def eliminateColumn (q : UInt32) (A : Matrix UInt32 n m) (pivotRow : Fin n)
    (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := Matrix.getRow A pivotRow
  (List.finRange n).foldl
    (fun A j =>
      if j = pivotRow then A
      else
        let c := negMod q A[(j, col)]
        if c == 0 then A else rowAddFrom q A rsrc j c)
    A
```

`Packed.rowAdd` is retained, defined as `rowAddFrom` on `Matrix.getRow A src`,
so its existing correspondence lemma is a one-line consequence of
`Rep.rowAddFrom` and nothing outside the elimination changed shape.

The correspondence proof carries one extra invariant through
`rep_eliminateColumn_foldl`: `∀ k, rsrc[k] = A[pivotRow][k]` for the accumulated
buffer `A` at every step. `elim_step_pivotRow` establishes preservation from the
step either doing nothing or writing a row `j ≠ pivotRow`, and the invariant
holds at entry by `rfl`. No `axiom`, `sorry`, `native_decide` or unchecked
oracle.

**Aliasing.** `Matrix.getRow` is `Vector.ofFn`, a fresh allocation, so the
hoisted row is not a borrow of `A`'s backing buffer and `A` stays uniquely
referenced through the fold. This is the trap #9166 named: a borrow would leave
the buffer multiply referenced and turn every row addition into a whole-matrix
copy. The measured direction rules that out on its own, but the reason it is
safe is the `ofFn`, not the measurement.

## The reduction, before and after

`integrated` is the production `Packed.reduce`, no mirror and no ladder
parameter. "reads saved" is `rowAdds - pivots`: the number of `n`-word row
copies the hoist removes.

| instance | n | row additions | pivots | reads saved | `integrated` before | `integrated` after | after (rerun) | after/before |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32 | 215 | 16 | 199 | 87.845 us | 35.397 us | 35.062 us | 0.40x |
| `sd5_shift1` | 32 | 449 | 16 | 433 | 174.423 us | 57.405 us | 57.090 us | 0.33x |
| `sd5_shift2` | 32 | 455 | 16 | 439 | 173.642 us | 57.841 us | 58.106 us | 0.33x |
| `sd4_x_sd4shift1` | 32 | 444 | 16 | 428 | 169.366 us | 57.245 us | 57.010 us | 0.34x |
| `sd5_x_phi11` | 42 | 935 | 25 | 910 | 448.610 us | 142.151 us | 141.489 us | 0.32x |
| `xpow48_minus1` | 48 | 38 | 29 | 9 | 44.476 us | 42.473 us | 41.627 us | 0.95x |
| `xpow105_minus1` | 105 | 175 | 91 | 84 | 340.325 us | 280.922 us | 277.791 us | 0.83x |
| `xpow120_minus1` | 120 | 116 | 81 | 35 | 301.046 us | 277.156 us | 273.365 us | 0.92x |
| `cyclo_phi179` | 178 | 1114 | 176 | 938 | 2.540 ms | 1.307 ms | 1.296 ms | 0.51x |
| `cyclo_phi64_x_phi105` | 80 | 4277 | 70 | 4207 | 3.642 ms | 1.116 ms | 1.112 ms | 0.31x |
| `cyclo_phi128_x_phi165` | 144 | 13149 | 136 | 13013 | 19.529 ms | 5.739 ms | 5.736 ms | 0.29x |
| `cyclo_phi385` | 240 | 17948 | 236 | 17712 | 45.095 ms | 13.260 ms | 13.282 ms | 0.29x |
| `wilkinson_40` | 40 | 0 | 0 | 0 | 3.605 us | 3.666 us | 3.675 us | 1.02x |
| `wilkinson_48` | 48 | 0 | 0 | 0 | 5.013 us | 5.107 us | 5.213 us | 1.02x |
| `wilkinson_56` | 56 | 0 | 0 | 0 | 6.685 us | 6.835 us | 6.891 us | 1.02x |
| `chebyshev_T24` (control) | 24 | 112 | 21 | 91 | 41.892 us | 23.820 us | 23.415 us | 0.57x |
| `chebyshev_U24` (control) | 24 | 98 | 20 | 78 | 36.859 us | 22.172 us | 21.392 us | 0.60x |
| `legendre_P30` (control) | 30 | 315 | 23 | 292 | 119.517 us | 48.361 us | 47.806 us | 0.40x |
| `legendre_P38` (control) | 38 | 620 | 35 | 585 | 283.300 us | 105.717 us | 104.290 us | 0.37x |
| `cyclo_phi17` (control) | 16 | 50 | 15 | 35 | 15.057 us | 10.486 us | 10.255 us | 0.70x |
| `cyclo_phi41` (control) | 40 | 100 | 35 | 65 | 68.492 us | 50.264 us | 49.389 us | 0.73x |
| `xpow24_minus1` (control) | 24 | 11 | 11 | 0 | 8.773 us | 9.114 us | 8.889 us | 1.04x |
| `randprod_10` (control) | 20 | 233 | 16 | 217 | 63.003 us | 24.916 us | 24.531 us | 0.40x |
| `randprod_21` (control) | 24 | 353 | 17 | 336 | 106.894 us | 38.416 us | 38.062 us | 0.36x |

The full sample ranges, since these are cross-run comparisons and the medians
above are not paired:

| instance | before range | after range | after (rerun) range |
|---|---:|---:|---:|
| `sd5` | 86.699 us to 89.022 us | 35.213 us to 35.803 us | 34.622 us to 35.443 us |
| `sd5_shift1` | 171.414 us to 189.241 us | 57.195 us to 57.846 us | 56.854 us to 57.746 us |
| `sd5_shift2` | 170.042 us to 177.994 us | 57.596 us to 61.521 us | 57.395 us to 58.988 us |
| `sd4_x_sd4shift1` | 164.454 us to 183.592 us | 56.714 us to 57.496 us | 56.654 us to 57.805 us |
| `sd5_x_phi11` | 442.707 us to 457.508 us | 141.470 us to 142.451 us | 140.548 us to 142.401 us |
| `xpow48_minus1` | 43.184 us to 47.961 us | 41.632 us to 42.983 us | 41.081 us to 47.771 us |
| `xpow105_minus1` | 337.340 us to 343.098 us | 276.880 us to 283.991 us | 273.726 us to 284.442 us |
| `xpow120_minus1` | 295.478 us to 303.420 us | 266.335 us to 284.061 us | 267.537 us to 276.700 us |
| `cyclo_phi179` | 2.527 ms to 2.561 ms | 1.298 ms to 1.318 ms | 1.267 ms to 1.325 ms |
| `cyclo_phi64_x_phi105` | 3.616 ms to 3.674 ms | 1.108 ms to 1.120 ms | 1.106 ms to 1.137 ms |
| `cyclo_phi128_x_phi165` | 18.760 ms to 19.996 ms | 5.722 ms to 5.778 ms | 5.716 ms to 5.765 ms |
| `cyclo_phi385` | 44.090 ms to 45.406 ms | 13.225 ms to 13.302 ms | 13.223 ms to 13.317 ms |
| `wilkinson_40` | 3.575 us to 3.616 us | 3.616 us to 3.846 us | 3.645 us to 3.715 us |
| `wilkinson_48` | 4.987 us to 5.047 us | 5.078 us to 5.248 us | 5.148 us to 6.249 us |
| `wilkinson_56` | 6.640 us to 6.710 us | 6.770 us to 6.881 us | 6.870 us to 6.920 us |
| `chebyshev_T24` (control) | 41.281 us to 46.509 us | 23.715 us to 24.196 us | 23.325 us to 23.485 us |
| `chebyshev_U24` (control) | 36.544 us to 37.435 us | 21.982 us to 22.323 us | 21.262 us to 21.472 us |
| `legendre_P30` (control) | 118.135 us to 122.773 us | 48.182 us to 51.797 us | 47.160 us to 50.895 us |
| `legendre_P38` (control) | 280.516 us to 286.615 us | 105.246 us to 106.167 us | 104.055 us to 104.485 us |
| `cyclo_phi17` (control) | 14.711 us to 15.283 us | 10.405 us to 10.606 us | 10.185 us to 10.336 us |
| `cyclo_phi41` (control) | 67.821 us to 101.300 us | 49.864 us to 50.465 us | 49.273 us to 50.005 us |
| `xpow24_minus1` (control) | 8.673 us to 8.973 us | 9.004 us to 9.164 us | 8.742 us to 9.054 us |
| `randprod_10` (control) | 60.710 us to 63.795 us | 24.707 us to 25.057 us | 24.336 us to 24.616 us |
| `randprod_21` (control) | 104.856 us to 118.616 us | 38.156 us to 38.697 us | 37.876 us to 38.216 us |

### The rows that do not improve, and why they do not

Four rows are at or above 1.00x. **They are the four rows with nothing to save,
and one of them proves that the residual is not the change.**

The three Wilkinson rows find **no pivot column at all**: `pivots` is 0, so
`eliminateColumn` is never called on them and the hoisted read never executes.
Their 1.02x is therefore an artifact of comparing two different binaries in two
different processes, not of the change. Three no-work rows on a 3 to 7 us span
show about 2% of cross-run drift; that is a demonstration on those rows, not a
bound on the drift a longer measurement carries. `xpow24_minus1` has 11 pivots
and 11 row additions, so the hoist replaces 11 reads with 11 reads and saves
exactly nothing; it measures 1.04x in one after run and 1.01x in the other, the
same size of effect.

`xpow48_minus1` (9 reads saved of 38) and `xpow120_minus1` (35 of 116) are the
genuinely small savings, at 0.95x and 0.92x, and both reproduce in the second
after run. These are the rows #9160 already flagged as dominated by already-zero
columns rather than by arithmetic, and the `List.finRange n` scan they are
dominated by is explicitly out of this issue's scope.

## The hoist is where it was measured

`mirrored - hoistedPivotRow` is the paired within-run difference #9160 used to
attribute the copy. `mirrored` runs the production `Packed.eliminateColumn`
through the ladder, so after this change both rungs read the pivot row once per
column and their difference should collapse to nothing. It does.

| instance | before (paired median) | before paired range | after (paired median) | after paired range |
|---|---:|---:|---:|---:|
| `sd5` | 52.418 us | 49.875 us to 53.670 us | 256 ns | -390 ns to 661 ns |
| `sd5_shift1` | 116.077 us | 112.896 us to 124.264 us | -20 ns | -190 ns to 441 ns |
| `sd5_shift2` | 114.109 us | 112.477 us to 119.598 us | 341 ns | 109 ns to 2.805 us |
| `sd4_x_sd4shift1` | 111.706 us | 107.700 us to 116.182 us | 410 ns | -60 ns to 690 ns |
| `sd5_x_phi11` | 304.687 us | 299.504 us to 312.944 us | 216 ns | -3.925 us to 370 ns |
| `xpow48_minus1` | 2.679 us | 2.123 us to 3.485 us | 135 ns | -300 ns to 4.226 us |
| `xpow105_minus1` | 62.508 us | 47.080 us to 65.538 us | 2.168 us | 1.052 us to 3.705 us |
| `xpow120_minus1` | 30.275 us | 28.351 us to 35.122 us | 1.407 us | -3.115 us to 9.055 us |
| `cyclo_phi179` | 1.244 ms | 1.232 ms to 1.259 ms | -196 ns | -4.247 us to 8.102 us |
| `cyclo_phi64_x_phi105` | 2.529 ms | 2.492 ms to 2.568 ms | 1.391 us | -4.787 us to 8.663 us |
| `cyclo_phi128_x_phi165` | 13.836 ms | 13.111 ms to 14.293 ms | 722 ns | -57.355 us to 24.167 us |
| `cyclo_phi385` | 31.606 ms | 30.766 ms to 32.138 ms | 16.841 us | -73.248 us to 35.292 us |
| `wilkinson_40` | 105 ns | -29 ns to 621 ns | 10 ns | -2.514 us to 220 ns |
| `wilkinson_48` | 60 ns | -110 ns to 301 ns | 5 ns | -2.754 us to 171 ns |
| `wilkinson_56` | 106 ns | -10 ns to 271 ns | 70 ns | -10 ns to 261 ns |
| `chebyshev_T24` (control) | 17.826 us | 16.805 us to 21.993 us | 170 ns | -90 ns to 3.585 us |
| `chebyshev_U24` (control) | 15.222 us | 11.698 us to 29.173 us | -5 ns | -410 ns to 230 ns |
| `legendre_P30` (control) | 72.151 us | 69.854 us to 86.048 us | 130 ns | -3.325 us to 762 ns |
| `legendre_P38` (control) | 178.304 us | 149.262 us to 185.825 us | 356 ns | -2.373 us to 4.787 us |
| `cyclo_phi17` (control) | 4.796 us | 4.528 us to 5.027 us | 70 ns | -11 ns to 221 ns |
| `cyclo_phi41` (control) | 19.840 us | 19.218 us to 19.970 us | 246 ns | -191 ns to 3.846 us |
| `xpow24_minus1` (control) | -320 ns | -381 ns to -140 ns | 0 ns | -210 ns to 70 ns |
| `randprod_10` (control) | 38.077 us | 36.384 us to 39.389 us | 136 ns | -80 ns to 240 ns |
| `randprod_21` (control) | 68.286 us | 66.538 us to 73.389 us | 176 ns | -1.933 us to 331 ns |

Both columns are within-run paired medians. The before column reproduces
#9160's attribution, taken on the same host four commits earlier, but it is not
the same number row for row: the heaviest rows agree closely (31.606 ms against
31.378 ms on `cyclo_phi385`, 68.286 us against 67.320 us on `randprod_21`, both
within 1.5%), and the sparse rows do not (2.679 us against 3.791 us on
`xpow48_minus1`, 62.508 us against 70.325 us on `xpow105_minus1`). Those four
intervening commits include two that change the factorization path itself
(#9171, #9172), and the sparse rows are the ones whose reduction is small
enough for that to matter.

On `cyclo_phi385` the difference goes from 31.606 ms to 16.841 us, 0.1% of the
rung, and its paired range now straddles zero on **22 of 24** rows. Only
`sd5_shift2` (341 ns) and `xpow105_minus1` (2.168 us) stay wholly positive, at
0.6% and 0.8% of their rungs, which is the ladder's own scaffolding.

The other direction of the same check: `integrated` after (13.260 ms and
13.282 ms on `cyclo_phi385`) lands on `hoistedPivotRow` before (13.225 ms in the
`a5a55cbf` run), within 0.4%. That is the check #9166's verification asked for.

## Against the prototype

`flatBuffer` is the benchmark prototype the 2.6x was measured against, run on
the packed buffer in the same process. It did not change.

| instance | `integrated`/prototype before | after |
|---|---:|---:|
| `sd5` | 2.58x | 1.04x |
| `sd5_shift1` | 2.85x | 0.95x |
| `sd5_shift2` | 2.84x | 0.95x |
| `sd4_x_sd4shift1` | 2.80x | 0.95x |
| `sd5_x_phi11` | 2.84x | 0.91x |
| `xpow48_minus1` | 1.65x | 1.56x |
| `xpow105_minus1` | 1.85x | 1.53x |
| `xpow120_minus1` | 1.76x | 1.61x |
| `cyclo_phi179` | 2.37x | 1.21x |
| `cyclo_phi64_x_phi105` | 2.77x | 0.86x |
| `cyclo_phi128_x_phi165` | 2.76x | 0.82x |
| `cyclo_phi385` | 2.80x | 0.83x |
| `wilkinson_40` | 0.78x | 0.89x |
| `wilkinson_48` | 0.82x | 0.90x |
| `wilkinson_56` | 0.81x | 0.89x |
| `chebyshev_T24` (control) | 2.26x | 1.31x |
| `chebyshev_U24` (control) | 2.22x | 1.37x |
| `legendre_P30` (control) | 2.57x | 1.05x |
| `legendre_P38` (control) | 2.66x | 1.01x |
| `cyclo_phi17` (control) | 1.97x | 1.37x |
| `cyclo_phi41` (control) | 2.00x | 1.46x |
| `xpow24_minus1` (control) | 1.46x | 1.53x |
| `randprod_10` (control) | 2.76x | 1.09x |
| `randprod_21` (control) | 2.83x | 1.03x |

0.82x and 0.83x on the two heaviest rows, against the 0.82x to 0.83x #9160
projected from the ladder. The rows still above 1.00x are the sparse ones, where
the residual is the `List.finRange n` scan and the prototype's `Nat` range beats
it; that is the second of the two findings this issue held out of scope.

## End to end

The reduction is one stage of one prime's Berlekamp split, so the end-to-end
effect is bounded by that stage's share.

| instance | `factor` before | `factor` after | after/before | `fixedSpaceKernelVectors` before | after | after/before |
|---|---:|---:|---:|---:|---:|---:|
| `sd5` | 68.848 ms | 68.875 ms | 1.00x | 1.357 ms | 1.303 ms | 0.96x |
| `sd5_shift1` | 63.757 ms | 62.689 ms | 0.98x | 1.809 ms | 1.686 ms | 0.93x |
| `sd5_shift2` | 66.329 ms | 65.302 ms | 0.98x | 1.802 ms | 1.686 ms | 0.94x |
| `sd4_x_sd4shift1` | 17.970 ms | 17.662 ms | 0.98x | 1.806 ms | 1.699 ms | 0.94x |
| `sd5_x_phi11` | 138.623 ms | 138.921 ms | 1.00x | 3.305 ms | 3.034 ms | 0.92x |
| `xpow48_minus1` | 10.547 ms | 10.445 ms | 0.99x | 625.602 us | 615.347 us | 0.98x |
| `xpow105_minus1` | 44.489 ms | 45.913 ms | 1.03x | 4.014 ms | 3.929 ms | 0.98x |
| `xpow120_minus1` | 146.843 ms | 148.327 ms | 1.01x | 2.957 ms | 3.005 ms | 1.02x |
| `cyclo_phi179` | 34.578 ms | 33.724 ms | 0.98x | 5.741 ms | 4.560 ms | 0.79x |
| `cyclo_phi64_x_phi105` | 18.796 ms | 16.263 ms | 0.87x | 7.451 ms | 4.927 ms | 0.66x |
| `cyclo_phi128_x_phi165` | 75.134 ms | 61.575 ms | 0.82x | 27.580 ms | 13.909 ms | 0.50x |
| `cyclo_phi385` | 143.566 ms | 115.069 ms | 0.80x | 52.252 ms | 21.140 ms | 0.40x |
| `wilkinson_40` | 9.179 ms | 9.329 ms | 1.02x | 218.554 us | 223.656 us | 1.02x |
| `wilkinson_48` | 16.220 ms | 16.172 ms | 1.00x | 313.055 us | 322.558 us | 1.03x |
| `wilkinson_56` | 20.907 ms | 20.932 ms | 1.00x | 498.213 us | 504.913 us | 1.01x |
| `chebyshev_T24` (control) | 448.755 us | 420.604 us | 0.94x | 167.128 us | 149.596 us | 0.90x |
| `chebyshev_U24` (control) | 597.456 us | 579.800 us | 0.97x | 126.738 us | 112.913 us | 0.89x |
| `legendre_P30` (control) | 8.639 ms | 8.384 ms | 0.97x | 1.331 ms | 1.291 ms | 0.97x |
| `legendre_P38` (control) | 3.925 ms | 3.682 ms | 0.94x | 2.685 ms | 2.509 ms | 0.93x |
| `cyclo_phi17` (control) | 108.911 us | 102.873 us | 0.94x | 50.014 us | 45.397 us | 0.91x |
| `cyclo_phi41` (control) | 2.023 ms | 1.992 ms | 0.98x | 248.388 us | 231.829 us | 0.93x |
| `xpow24_minus1` (control) | 2.317 ms | 2.324 ms | 1.00x | 170.593 us | 168.515 us | 0.99x |
| `randprod_10` (control) | 635.442 us | 604.046 us | 0.95x | 235.985 us | 199.240 us | 0.84x |
| `randprod_21` (control) | 1.438 ms | 1.358 ms | 0.94x | 687.129 us | 623.859 us | 0.91x |

`fixedSpaceKernelVectors` is the median of eight one-call observations, one per
kernel repeat, and unlike the ladder rungs its raw samples are not retained, so
no range is available for it. The end-to-end column is a median over the
driver's `--repeats` end-to-end calls. The 1.03x on
`xpow105_minus1` and 1.01x on `xpow120_minus1` are rows whose reduction improved
and whose end-to-end time did not; on those rows the kernel is a small share of
`factor` and the difference is between-run drift on a 45 to 148 ms wall.

### The full corpus sweep

Touching executable factorization code invalidates the committed cross-system
sweep, so a fresh `hex-factor` sweep was recorded at `8ed3c378` on a clean tree,
against the committed `48bdfb8e` baseline, and the figures under
`reports/figures/` were regenerated from it.

`hexbz-factor-sweep-8ed3c378-hex-chungus2.json`, SHA-256
`30d8ebad55a52b953cc3af05788ec33cf1177334adb8bd285d5efb2cbd22ddbb`: **377 of
392 instances solved at the 10 s cutoff, the same 377 as the baseline**, with
the cross-system factor-degree check clean. 64 instances improve by more than
10%, led by `conway_p11_n1` at 0.61x, `cyclo_phi625` 60.110 ms to 41.545 ms
(0.69x), `cyclo_phi509` 48.989 ms to 38.894 ms (0.79x), `cyclo_phi385`
142.409 ms to 114.089 ms (0.80x) and `cyclo_phi331` 20.935 ms to 16.809 ms
(0.80x), plus most of the `conway_p*_n3*` family at 0.76x to 0.81x.

Eight instances regress by more than 5%, and **every one of them is
sub-millisecond**, where the absolute change is single-digit microseconds:

| instance | before | after | ratio |
|---|---:|---:|---:|
| `sd2` | 53 us | 61 us | 1.17x |
| `chebyshev_T3` | 34 us | 39 us | 1.16x |
| `conway_p11_n2` | 29 us | 33 us | 1.13x |
| `xpow12_minus1` | 238 us | 255 us | 1.07x |
| `quartic_a4` | 52 us | 56 us | 1.07x |
| `conway_p5_n6` | 53 us | 56 us | 1.06x |
| `conway_p5_n2` | 25 us | 26 us | 1.05x |
| `conway_p2_n1` | 22 us | 24 us | 1.05x |

These are single sweep observations at the scale where the sweep's own
per-call protocol overhead is 18.7 us, so they are reported rather than
explained. Nothing above 300 us regresses at all.

**Allocations do not resolve this change and are not reported as if they did.**
The driver's `smallAllocs` counter reports 663,779 for `cyclo_phi385` on the
`integrated`, `mirrored` *and* `hoistedPivotRow` rungs, in the before run, where
`mirrored` and `hoistedPivotRow` differ by 17,712 row copies. Whatever that
counter tracks, it does not see the row vectors, so its being unchanged before
and after says nothing either way.

## The multiply's share moved, as predicted

#9160 priced the inner modular multiply by a doubled-multiply rung against a
salted-select control and measured it at about 5% of the integrated reduction.
Removing two thirds of the reduction does not remove any multiplies, so its
share rises.

| instance | multiply before | share of `integrated` before | multiply after | share after |
|---|---:|---:|---:|---:|
| `sd5` | 3.761 us | 4.3% | 4.271 us | 12.1% |
| `sd5_shift1` | 7.867 us | 4.5% | 7.782 us | 13.6% |
| `sd5_x_phi11` | 21.262 us | 4.7% | 21.492 us | 15.1% |
| `cyclo_phi179` | 106.062 us | 4.2% | 105.858 us | 8.1% |
| `cyclo_phi64_x_phi105` | 183.673 us | 5.0% | 181.981 us | 16.3% |
| `cyclo_phi128_x_phi165` | 982.912 us | 5.0% | 969.268 us | 16.9% |
| `cyclo_phi385` | 2.193 ms | 4.9% | 2.218 ms | 16.7% |
| `randprod_21` (control) | 4.627 us | 4.3% | 4.717 us | 12.3% |

The absolute cost is unchanged, within a few percent, on every row: 2.193 ms
against 2.218 ms on `cyclo_phi385`. That is the check that this is a share
moving and not a multiply getting more expensive.

This is the condition #9166 set for re-opening the Barrett reciprocal: the
reciprocal resolved on two of 24 rows at 1.4% to 2.2% in its favour when the
multiply was 5% of the reduction, and it is now about 17%.

## What this does not establish

- **The before and after are not paired.** They are separate processes with
  separate binaries, so no difference in the cross-run tables has a paired
  range. What is paired is the within-run collapse of
  `mirrored - hoistedPivotRow`. The Wilkinson rows show that cross-run drift on
  a no-work row is about 2%, which is a demonstration on three 3 to 7 us rows,
  not a bound that transfers to the millisecond rows.
- **This is one host on one day.** `chungus2` was shared with other work
  throughout, which is why the before run is bracketed by two after runs rather
  than run once beside one.
- **Nothing here says the residual is now arithmetic.** The sparse rows are
  still 1.5x to 1.6x the prototype, and the two findings #9166 held out of scope
  (the `nullspaceArray` pivot search and the `List.finRange n` scan) are
  untouched and unmeasured here.
- **No claim about non-corpus shapes.** The corpus is 24 rows of the committed
  factorization corpus, and the saving is proportional to
  `rowAdds - pivots`, which a different distribution of matrices would change.

## Verification

- `lake build` green (9,737 jobs), `lake build HexConformance` green,
  `hexbz_factor_service` builds, zero warnings from the changed files. The only
  `sorry` warnings in the tree are the pre-existing ones in
  `HexNumberFieldTowerMathlib`.
- `lake exe hexberlekamp_emit_fixtures` and `lake exe hexbz_emit_fixtures`
  reproduce `conformance-fixtures/HexBerlekamp/berlekamp.jsonl` and
  `conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl` byte for byte.
- No `axiom`, `sorry`, `native_decide` or unchecked oracle added.
- A fresh `hex-factor` corpus sweep at `8ed3c378` on a clean tree solves the
  same 377 of 392 instances as the `48bdfb8e` baseline with a clean
  cross-system factor-degree check, and the 25 figures under `reports/figures/`
  are regenerated from it.
  `python3 scripts/bench/check_factor_sweep_freshness.py` and
  `uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
  --check` both pass.
- All three profile runs: 24 of 24 kernel rows agree with
  `Hex.Matrix.nullspace` on every ladder rung and every packed variant, the
  counted mirror agrees with `Packed.reduce` and with the production
  `rowReduce`, and 368 of 368 wider-sample instances agree with the production
  `factorTrace` on leaf count, selected prime, subset cardinalities and factor
  degrees.

## Regeneration

```sh
lake build hexbz_factor_service

python3 scripts/bench/factor_phase_profile.py \
  --no-counterfactual --no-scout --kernel-repeats 8 \
  --output reports/bench-results/hexbz-phase-profile-dcecc57e-chungus2.json

# the before run, with only the two measured files reverted
git checkout a5a55cbf -- HexBerlekamp/PackedKernel.lean bench/HexBench/BerlekampKernel.lean
lake build hexbz_factor_service
python3 scripts/bench/factor_phase_profile.py \
  --no-counterfactual --no-scout --kernel-repeats 8 \
  --output reports/bench-results/hexbz-phase-profile-a5a55cbf-chungus2.json
git checkout HEAD -- HexBerlekamp/PackedKernel.lean bench/HexBench/BerlekampKernel.lean
```

Use an **even** `--kernel-repeats`: the ladder and the prototype variants flip
direction on every call, and an odd count leaves the median picking the majority
direction.

The tables come out of `scripts/bench/packed_ladder_diff.py`:

```sh
# the within-run paired collapse
python3 scripts/bench/packed_ladder_diff.py \
  reports/bench-results/hexbz-phase-profile-dcecc57e-chungus2.json

# the cross-run before/after on any single rung
python3 scripts/bench/packed_ladder_diff.py --rung integrated \
  reports/bench-results/hexbz-phase-profile-a5a55cbf-chungus2.json \
  reports/bench-results/hexbz-phase-profile-dcecc57e-chungus2.json
```

The corpus sweep and the figures, on a clean tree:

```sh
python3 scripts/bench/factor_sweep.py --systems hex-factor \
  --output reports/bench-results/hexbz-factor-sweep-8ed3c378-hex-chungus2.json
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
```

## Follow-up

- **Re-open the Barrett reciprocal.** #9160 measured it at 1.4% to 2.2% in
  Barrett's favour on two of 24 rows and unresolved elsewhere, against a
  multiply that was 5% of the reduction. It is 17% now, and a measurement
  designed for a two-percent effect is worth running.
- The two findings #9166 held out of scope are unchanged: `nullspaceArray`'s
  per-entry pivot-column search, and the `List.finRange n` scan in
  `eliminateColumn`, which is what the sparse rows' remaining 1.5x to 1.6x
  against the prototype is.
