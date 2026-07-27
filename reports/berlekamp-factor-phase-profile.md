# Berlekamp factorization sub-phase profile (#8700)

## Headline

The apparent cubic fixed-space cost was repeated construction, not scalar
`ZMod64` arithmetic. Two invariant computations sat inside per-index
`Vector.ofFn` bodies:

- `fixedSpaceKernel` rebuilt the complete vector kernel for every polynomial
  representative;
- `IsRowReduced.nullspace` rebuilt `nullspaceMatrix` for every basis column.

On the split height-2 degree grid, this repeated fixed-space work consumed
**70.2-90.6%** of `berlekampFactor`; on phi15, SD3, and SD4 it consumed
**77.9-90.9%**. Hoisting both invariants speeds up the complete modular
factorization by **3.29-10.48x** on the grid and **3.86-9.91x** on the
adversarial inputs. The direct old/new callbacks produce identical
boundary-sensitive checksums, and the elementwise correspondence proofs pin
the same basis-vector values and order.

After the fix, witness splitting through `DensePoly.gcd` is the largest phase
on the fully split grid (76.3-92.3%); the shared nullspace is only 1.1-3.5%.
Phi15 is matrix-heavy because it has only two modular factors; splitting leads
on SD3 and SD4. A future split-family optimization should therefore target the
witness/GCD phase. The boundary-free row-reduction work of #8669 is no longer
the common dominant lever on this corpus.

The follow-up witness profile and linear-leaf optimization are recorded in
[`berlekamp-witness-split-profile.md`](berlekamp-witness-split-profile.md).
The timings in this report were measured before that #8888 optimization.

These ratios apply to `berlekampFactor` on an already-selected monic modular
image. They are not speedups for the whole prime walk, Hensel lifting,
recombination, or public integer factorization.

## Method

`RELIFT_PROFILE=berlekamp` in
`bench/HexBench/RecursiveReliftSpike.lean` is a compiled `lean_exe` profile. It
runs prime selection once per input outside the timed regions, then measures
the selected monic modular image directly. Pure work is passed through a
`@[noinline]` IO identity between `IO.monoNanosNow` timestamps; each figure is
the median of 31 single-call samples. Declined inputs are emitted with
`status=skipped` rather than silently dropped.

The callbacks are:

- `matrix`: checksum `fixedSpaceMatrix`;
- `repeatedKernel`: reproduce both pre-fix per-index rebuilds;
- `repeatedFactor`: reproduce the complete pre-fix `berlekampFactor` shape;
- `kernel`: checksum the shared `fixedSpaceKernel`;
- `factor`: checksum the fixed `berlekampFactor`.

The baseline and fixed speedup are a direct `repeatedFactor`/`factor` A/B in
one binary. Baseline phase shares subtract the cumulative `matrix`,
`repeatedKernel`, and `repeatedFactor` medians; fixed shares subtract `matrix`,
`kernel`, and `factor`. Every subtraction is checked for ordering and aborts on
inversion. The raw kernel ratio is included as an internal check on the nested
repetition. Old/new kernel and factor checksums are compared before timing and
a mismatch aborts the profile.

Checksum traversals and subtraction of independently sampled medians make the
phase percentages approximate; they are attribution evidence, not cycle-exact
self-time. The primary result is the direct matched end-to-end speedup.

Measurement environment:

- base commit: `afc8ca4d` (`origin/main` at measurement time);
- Lean: `leanprover/lean4:v4.32.0-rc1`;
- host: `chungus2`;
- CPU: AMD EPYC 9455 48-Core Processor, 96 logical CPUs;
- invocation: `lake build hex_recursive_relift_spike`, then
  `RELIFT_PROFILE=berlekamp .lake/build/bin/hex_recursive_relift_spike`.

The exact output is committed as
`reports/bench-results/berlekamp-factor-phase-profile.csv`.

## Results

Times are microseconds. `M`, `N`, and `GCD` are the fixed matrix, nullspace,
and witness-splitting shares. `kernel ratio` is repeated/shared kernel time.

| input | deg | p | r | baseline | fixed-space | split | fixed | M | N | GCD | kernel ratio | speedup |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| split h2 | 6 | 7 | 6 | 176 | 70.2% | 23.6% | 54 | 20.2% | 3.5% | 76.3% | 10.6x | 3.29x |
| split h2 | 8 | 11 | 8 | 436 | 75.1% | 20.5% | 110 | 17.6% | 2.6% | 79.8% | 15.6x | 3.96x |
| split h2 | 10 | 11 | 10 | 818 | 79.4% | 17.8% | 174 | 13.4% | 2.3% | 84.3% | 24.6x | 4.70x |
| split h2 | 12 | 13 | 12 | 1460 | 81.6% | 16.3% | 275 | 10.8% | 2.1% | 87.1% | 34.5x | 5.31x |
| split h2 | 14 | 17 | 14 | 2378 | 83.7% | 14.9% | 390 | 8.8% | 1.8% | 89.4% | 48.8x | 6.09x |
| split h2 | 16 | 17 | 16 | 3733 | 85.7% | 13.2% | 556 | 7.4% | 1.5% | 91.1% | 65.1x | 6.71x |
| split h2 | 18 | 19 | 18 | 5863 | 87.3% | 11.6% | 765 | 8.0% | 1.5% | 90.6% | 71.7x | 7.66x |
| split h2 | 20 | 23 | 20 | 8555 | 88.5% | 10.6% | 979 | 7.7% | 1.4% | 91.0% | 86.6x | 8.74x |
| split h2 | 22 | 23 | 22 | 12081 | 89.0% | 10.3% | 1247 | 6.8% | 1.2% | 92.0% | 108.3x | 9.69x |
| split h2 | 24 | 29 | 24 | 16750 | 90.6% | 8.8% | 1598 | 6.6% | 1.1% | 92.3% | 124.0x | 10.48x |
| phi15 | 8 | 7 | 2 | 221 | 81.7% | 4.6% | 57 | 52.9% | 29.5% | 17.6% | 4.5x | 3.86x |
| SD3 | 8 | 7 | 4 | 341 | 77.9% | 13.7% | 82 | 34.6% | 8.8% | 56.6% | 8.2x | 4.15x |
| SD4 | 16 | 11 | 8 | 4975 | 90.9% | 6.3% | 502 | 27.7% | 8.7% | 63.7% | 25.5x | 9.91x |

`Vector.map` preserves the fixed-space vector length and order, while the
`Vector.getElem_map` proof used at every consumer shows each polynomial equals
the old per-index conversion. `IsRowReduced.nullspace` still uses the same
`Vector.ofFn` columns; it now lets the basis matrix once outside that body.
