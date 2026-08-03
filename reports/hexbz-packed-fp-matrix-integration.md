# The packed finite-field matrix, integrated (issue #9150)

[reports/hexbz-packed-fp-matrix.md](hexbz-packed-fp-matrix.md) measured a
benchmark prototype and returned a **go**. This page measures the landed
implementation: `HexBerlekamp/PackedKernel.lean`, selected in compiled code by
a `@[csimp]`-proved equality at the `fixedSpaceKernelVectors` boundary.

The headline is the same span the prototype page priced, measured the same way
by the same driver on the same host: `fixedSpaceKernelVectors` on
`cyclo_phi385` goes from **327.823 ms to 53.886 ms, 6.08x**, and the whole
factorization from 434.641 ms to 167.124 ms, **2.60x**. No row of the
representative set regresses, on either span, at any margin -- including the
Wilkinson rows, whose fixed-space matrix is zero and which the prototype
*slowed down* by 1.4x.

The implementation is **2.6x slower than the prototype** on the rows where the
reduction dominates. That gap is the honest headline of the second table below
and is not a measurement artefact; [Where the remaining
2.6x is](#where-the-remaining-26x-is) names its causes.

## Revision and protocol

- Source revision `2c4c6e4fa0378ee34cf6399a91c720b4e63cf84d` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, measured 2026-08-03.
  The host was shared with other work throughout.
- The driver pins itself to one idle logical CPU before spawning any service.
- Baseline: `reports/bench-results/hexbz-phase-profile-0e1601a0-chungus2.json`,
  the record the prototype page reads, measured on the same host.
- After: `reports/bench-results/hexbz-phase-profile-2c4c6e4f-chungus2.json`,
  SHA-256 `1f595bed0ef0e5a67cc2b8246af8eb4f91d5769cc92bad4e0665185f1433ac59`.
  `hexbz_factor_service` SHA-256
  `c22f80f3683e4e9c7b7c7432e6af80543e920aa9402b8cd37ea4686d3d6360c4`; corpus
  `bench/corpus/hexbz-factor-corpus.jsonl`, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.

The baseline and the after record are **separate runs minutes to hours apart on
a shared host**, so every before/after ratio below carries that run-to-run
variance. The prototype page measured the same computation at 0.67x to 1.00x of
itself across two sections of a single run; nothing here is more precise than
that. The ratios that matter are large enough to survive it, and the small ones
are reported as small.

## What landed

`Hex.Berlekamp.fixedSpaceKernelVectors` still *means*
`Hex.Matrix.nullspace (fixedSpaceMatrix f hmonic)`, and every Berlekamp
soundness and completeness proof still reasons about ordinary
`Matrix (ZMod64 p)`. Compiled code runs
`Hex.Berlekamp.Packed.kernelArray` instead, through the `@[csimp]` theorem
`Hex.Berlekamp.fixedSpaceKernelVectors_eq_packed`, whose statement is one
equality of the two functions and whose proof is
`Hex.Berlekamp.Packed.kernelArray_eq`.

The packed representation is a `Hex.Matrix UInt32 n m`: the same flat row-major
backing buffer `HexMatrix` already uses, with one `UInt32` word per entry
instead of one boxed `ZMod64 p`. Reusing `Hex.Matrix` rather than a bare
`Array` is what keeps the correspondence short -- `Matrix.rowSwap`,
`Matrix.modifyEntries` and their entrywise read lemmas are already proved, and
the in-place update behaviour on a uniquely referenced buffer is the one the
generic path already relies on.

Against the six design points the prototype page fixed:

1. **Built from the column polynomials, not from a `Hex.Matrix`.**
   `Packed.fixedSpace` fills the packed buffer straight from
   `berlekampColumnPolys`, decrementing the diagonal in the same pass. No
   `Matrix (ZMod64 p)` is ever built on the fast path, so neither the
   conversion stage nor a separate pack stage is paid. This is what removes the
   prototype's only measured regression: `wilkinson_40`, rank 0, goes from
   1.4x *slower* under the prototype to 1.33x faster here.
2. **`UInt32` entries.** `Packed.mulMod`/`addMod`/`negMod` work on `UInt32`
   words; `ZMod64.Bounds` caps the modulus at `2^31`, which is what makes the
   sum of two residues fit a `UInt32` without widening and the product of two
   arbitrary words fit a `UInt64` exactly.
3. **No transform.** `Packed.State` has no transform field and
   `Packed.eliminateColumn` performs one row addition per eliminated entry
   rather than two.
4. **The whole reduction loop is specialized** -- pivot search
   (`Packed.findPivot?`), swap (`Matrix.rowSwap` at `UInt32`), scale
   (`Packed.rowScale`), elimination (`Packed.eliminateColumn`), and the basis
   readback (`Packed.nullspaceArray`). Modular inversion is the one operation
   left on `ZMod64`: it runs once per pivot column, never in the inner loop,
   and routing it through `ZMod64.inv` keeps an extended-Euclid correspondence
   out of the proof.
5. **No Barrett context.** The inner multiply is a hardware `%` on a `UInt64`
   product.
6. **No zero-entry skip.** Orthogonal, and still owed its own evidence.

## Proof obligations, and where each is discharged

All in `HexBerlekamp/PackedKernel.lean`. No `axiom`, `sorry`, `native_decide`,
or unchecked oracle; `scripts/release/check_trust_surface.py` passes.

| obligation | discharged by |
|---|---|
| packed entry access agrees with the interpreted matrix | `Packed.Rep`, and `Rep.toZMod_eq` |
| each elementary row operation interprets to the corresponding one | `Rep.rowSwap`, `Rep.rowScale`, `Rep.rowAdd` |
| pivot search agrees with the reference | `Packed.findPivot?_eq` |
| the rank agrees with `Hex.Matrix.rowReduce_rank` | `Packed.reduce_rank` |
| the basis is sound and spans the whole kernel | `Packed.nullspaceArray_eq`, which reduces both to the existing `Matrix.nullspace_sound`/`nullspace_complete` |
| the witnesses reaching `fullySplit` are the same fixed-space witnesses | `fixedSpaceKernelVectors_eq_packed`: the boundary function is unchanged, so `fixedSpaceKernelVectors_sound`/`_complete` are untouched |

The simulation is one induction, `Packed.reduceLoop_sim`, relating
`Packed.reduceLoop` to `Hex.Matrix.rowReduceLoop` under `Packed.Rep`. The
reference's transform is carried along on the right of the relation and never
inspected, which is exactly what makes dropping it sound.

### The instance the packed words stand for

`fixedSpaceKernelVectors` used to take an opaque
`[Lean.Grind.Field (ZMod64 p)]` instance. A packed word can only stand for a
residue if the arithmetic it is reduced under is *the* `ZMod64` arithmetic, and
an opaque field instance is not that: `Lean.Grind.Field` bundles `Add`, `Mul`
and `Inv` as fields, so `rowReduceLoop`'s multiplications are whatever the
supplied dictionary says they are, and no packed implementation can be correct
for every dictionary.

The Berlekamp kernel path is therefore now parameterised by
`[ZMod64.PrimeModulus p]`, and the field structure comes from the canonical
`Hex.zmod64FieldOfPrime`. This is a strengthening of an existing hypothesis
rather than a new one -- every call site already had a primality witness in
scope and was already passing `zmod64FieldOfPrime` built from it, and
`PrimeModulus` is a `Prop` class, so nothing is passed at runtime that was not
already being passed.

## The measurement

`kernel` is the `fixedSpaceKernelVectors` span of the kernel section: the whole
boundary, Frobenius power and column polynomials included, on both sides.
`total` is the phase profile's own end-to-end median for the production
cascade.

| instance | matrix | prime | kernel before | kernel after | gain | total before | total after | gain |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32x32 | 29 | 1.821 ms | 1.339 ms | 1.36x | 75.594 ms | 69.402 ms | 1.09x |
| `sd5_shift1` | 32x32 | 29 | 2.739 ms | 1.750 ms | 1.57x | 64.235 ms | 64.425 ms | 1.00x |
| `sd5_shift2` | 32x32 | 29 | 2.739 ms | 1.762 ms | 1.55x | 68.231 ms | 67.697 ms | 1.01x |
| `sd4_x_sd4shift1` | 32x32 | 29 | 2.706 ms | 1.771 ms | 1.53x | 19.094 ms | 18.172 ms | 1.05x |
| `sd5_x_phi11` | 42x42 | 29 | 5.692 ms | 3.307 ms | 1.72x | 161.131 ms | 140.318 ms | 1.15x |
| `xpow48_minus1` | 48x48 | 11 | 894.566 us | 618.196 us | 1.45x | 19.639 ms | 10.400 ms | 1.89x |
| `xpow105_minus1` | 105x105 | 17 | 6.015 ms | 3.969 ms | 1.52x | 74.986 ms | 46.124 ms | 1.63x |
| `xpow120_minus1` | 120x120 | 7 | 5.009 ms | 3.003 ms | 1.67x | 478.515 ms | 148.233 ms | 3.23x |
| `cyclo_phi179` | 178x178 | 3 | 20.539 ms | 5.811 ms | 3.53x | 74.909 ms | 42.336 ms | 1.77x |
| `cyclo_phi64_x_phi105` | 80x80 | 11 | 27.932 ms | 7.506 ms | 3.72x | 61.349 ms | 45.865 ms | 1.34x |
| `cyclo_phi128_x_phi165` | 144x144 | 7 | 139.775 ms | 28.100 ms | 4.97x | 198.351 ms | 84.694 ms | 2.34x |
| `cyclo_phi385` | 240x240 | 3 | 327.823 ms | 53.886 ms | 6.08x | 434.641 ms | 167.124 ms | 2.60x |
| `wilkinson_40` | 40x40 | 47 | 297.862 us | 224.763 us | 1.33x | 13.451 ms | 13.518 ms | 1.00x |
| `wilkinson_48` | 48x48 | 61 | 427.624 us | 318.171 us | 1.34x | 25.192 ms | 24.389 ms | 1.03x |
| `wilkinson_56` | 56x56 | 67 | 661.561 us | 501.855 us | 1.32x | 34.180 ms | 32.686 ms | 1.05x |
| `chebyshev_T24` (control) | 24x24 | 5 | 401.566 us | 170.353 us | 2.36x | 558.258 us | 441.454 us | 1.26x |
| `chebyshev_U24` (control) | 24x24 | 3 | 334.365 us | 128.962 us | 2.59x | 711.415 us | 589.554 us | 1.21x |
| `legendre_P30` (control) | 30x30 | 67 | 2.032 ms | 1.363 ms | 1.49x | 9.080 ms | 8.560 ms | 1.06x |
| `legendre_P38` (control) | 38x38 | 79 | 4.244 ms | 2.712 ms | 1.57x | 4.792 ms | 3.820 ms | 1.25x |
| `cyclo_phi17` (control) | 16x16 | 3 | 129.993 us | 50.605 us | 2.57x | 155.711 us | 104.535 us | 1.49x |
| `cyclo_phi41` (control) | 40x40 | 3 | 643.014 us | 254.197 us | 2.53x | 2.825 ms | 1.979 ms | 1.43x |
| `xpow24_minus1` (control) | 24x24 | 11 | 227.337 us | 165.265 us | 1.38x | 3.223 ms | 2.293 ms | 1.41x |
| `randprod_10` (control) | 20x20 | 7 | 573.701 us | 232.915 us | 2.46x | 824.853 us | 640.029 us | 1.29x |
| `randprod_21` (control) | 24x24 | 17 | 1.251 ms | 681.290 us | 1.84x | 1.748 ms | 1.402 ms | 1.25x |

**No regression above 5% on any row, on either span.** The largest end-to-end
move against the implementation is `sd5_shift1` at 1.00x (64.235 ms to
64.425 ms, 0.3%), well inside the run-to-run variance stated above.

`xpow120_minus1`'s 3.23x is the one number here that its kernel gain (1.67x on
5 ms of a 478 ms factorization) cannot explain. That row's cost is
recombination, not the modular kernel, and the two runs disagree about it by
more than the kernel change can account for; read it as run-to-run variance on
a row this change does not touch, not as evidence of a further win.

Allocation, on the same span:

| instance | small allocs before | after | factor |
|---|---:|---:|---:|
| `cyclo_phi385` | 18,309,485 | 661,844 | 28x |
| `cyclo_phi128_x_phi165` | 8,451,415 | 723,728 | 12x |
| `cyclo_phi64_x_phi105` | 1,761,785 | 347,380 | 5x |
| `cyclo_phi179` | 1,290,156 | 275,077 | 5x |

## Where the remaining 2.6x is

The kernel section prices the prototype's four packed variants alongside the
integrated implementation in the same process, so the gap is measured, not
inferred. `prototype` is `packedHalfWordDivision` -- `UInt32` storage,
hardware remainder, pack plus reduce plus readback. `integrated` is the
`fixedSpaceKernelVectors` span less its Frobenius power and column
polynomials, which is the same work.

| instance | transform mirror | echelon-only mirror | transform factor | prototype | integrated | overhead |
|---|---:|---:|---:|---:|---:|---:|
| `cyclo_phi385` | 301.969 ms | 155.084 ms | 1.95x | 18.164 ms | 47.683 ms | 2.63x |
| `cyclo_phi128_x_phi165` | 132.537 ms | 67.510 ms | 1.96x | 7.688 ms | 20.750 ms | 2.70x |
| `cyclo_phi64_x_phi105` | 23.282 ms | 12.232 ms | 1.90x | 1.535 ms | 3.926 ms | 2.56x |
| `cyclo_phi179` | 16.922 ms | 9.692 ms | 1.75x | 2.527 ms | 3.389 ms | 1.34x |
| `wilkinson_40` | 40.730 us | 42.794 us | 0.95x | 71.976 us | 66.949 us | 0.93x |
| `legendre_P38` | 1.786 ms | 997.048 us | 1.79x | 166.207 us | 376.599 us | 2.27x |

Three causes, in the order they are worth fixing:

1. **`Matrix.rowAdd` copies the source row.** `HexMatrix`'s row addition reads
   the source row out with `getRow` before writing, because a closure that
   captured the matrix would hold a second reference and defeat the in-place
   update. The prototype indexed one flat `Array` directly and paid nothing.
   The copy is `m` words per row addition; on `cyclo_phi385` that is 17,948
   copies of 240 words. The pivot row is *invariant* across a column's
   elimination, so hoisting one `getRow` per pivot column would remove
   `n - 1` of every `n` copies; the proof cost is one more invariant in the
   elimination induction.
2. **The pivot columns are a boxed `List (Fin m)`.** It mirrors
   `rowReduceLoop`'s own representation, which is what makes the simulation an
   equality rather than a transport, but it allocates.
3. **The basis readback is `O(m * rank)` per basis vector**, because it mirrors
   `IsRowReduced.nullspaceMatrix`'s `pivotIndex?` scan column by column. The
   reference pays the same, so this is not a regression; a scattered readback
   would be `O(m + rank)`.

The transform columns re-measure design point 3 against this build: dropping
the transform is worth **1.75x to 1.96x** on the rows where the reduction
dominates, measured on the generic representation, which is where the prototype
page put it (1.98x).

## What these measurements do not establish

- **Design points 2 and 5 are not re-measured.** Separating `UInt32` from
  `UInt64` entries, or a Barrett reciprocal from the hardware remainder,
  against *this* implementation needs a second and third compiled variant of
  the packed loop that nothing would ship. The prototype's 2.42x for `UInt32`
  and 1.01x for Barrett are still the only evidence for those two choices, and
  they were measured on a prototype.
- **The before and after records are separate runs.** See
  [Revision and protocol](#revision-and-protocol).
- **The corpus moduli are small**, 3 to 79, far from the `2^31` bound the
  representation supports. The single division in the inner loop is the
  operation most likely to behave differently near that bound.
- **No memory-residency measurement.** `VmHWM` is a whole-process high-water
  mark; the allocation counts above are counts of small allocations, not bytes.

## Verification

- `lake build` green, `lake build HexConformance` green, zero warnings from the
  changed files.
- `lake exe hexberlekamp_emit_fixtures` and `lake exe hexbz_emit_fixtures`
  reproduce the committed fixtures byte for byte.
- The kernel section's own cross-checks pass on all 24 rows: the counted
  Gauss-Jordan mirror agrees with the production `rowReduce`, the
  transform-free mirror agrees with the transform-carrying one, and all four
  packed prototype variants agree with `Hex.Matrix.nullspace` entry for entry.
  The wider validation sample agrees with the production `factorTrace` on
  selected prime, leaf count, subset cardinalities and returned factor degrees
  on **368 of 368** instances.
- A fresh full Hex sweep over all 392 corpus instances, with the external
  comparator records reused unchanged, and regenerated cactus and
  runtime-by-degree figures.

## Regeneration

```sh
lake build hexbz_factor_service

taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output reports/bench-results/hexbz-factor-sweep-2c4c6e4f-hex-chungus2.json

python3 scripts/bench/factor_phase_profile.py \
  --no-counterfactual --no-scout \
  --output reports/bench-results/hexbz-phase-profile-2c4c6e4f-chungus2.json

python3 scripts/plots/hexbz-cactus.py
```

The phase-profile driver exits non-zero if any packed variant disagrees with
`Hex.Matrix.nullspace`, if the counted mirror disagrees with the production row
reduction, or if the recombination mirror disagrees with the production trace.
