# Berlekamp witness-splitting profile (#8888)

## Headline

On modular inputs whose emitted factors are linear, witness splitting grows
mainly because of candidate count and traversal order, not because individual
polynomial GCDs become dramatically more expensive. At degree 24, the old
recursion made 622 witness attempts. Of those, 576 were the 24 witnesses
scanned once against each of the 24 already-linear leaves. Those leaves cannot
admit the loop's required nonconstant, strictly smaller factor.

`fullySplit` now emits every polynomial of size at most two immediately. The
fast path reduces witness attempts from 46--622 to 10--46 across the degree
6--24 grid and speeds up the isolated witness bucket by **1.72--2.53x**. The
complete shared-kernel `berlekampFactor` callback improves by **1.46--2.26x**.
Phi15, SD3, and SD4 are unchanged because their emitted factors have degree at
least two: this optimization applies only when the modular image has linear
factors. In particular, 64 of SD4's 78 witness attempts are scans of
already-irreducible degree-two leaves, and its guard reductions remain 31.7%
of instrumented split time.

Before the fast path, witness reduction and its constant guard grew from 39.1%
to 57.0% of the instrumented split time across the grid. GCD work stayed near
31--38%. The degree-24 GCD count grew 15.8x (20 to 315 from degree 6), while
the measured cost per GCD grew only 2.0x (0.80 to 1.61 us). This is candidate
count growth, with the futile linear-leaf guards as the dominant avoidable
part on this grid.

The remainder-reuse prototype does not exercise a useful case on the split
grid: internal factors already see lower-degree witnesses, while linear leaves
exit at the constant guard before the sweep. On non-linear leaves it remains a
live result, measuring about 4% faster on SD3 and 11% faster on SD4. It is not
part of the production change because exact GCD invariance and recursive
remainder propagation still need to be carried through the correspondence
proofs; the split-grid measurement is not evidence against that design. After
the linear-leaf fast path, the remaining degree-24 split profile is 80.1% GCD
work, so a future improvement there would need to reduce or accelerate the 315
genuine constant candidates rather than optimize the eliminated leaf
reductions.

## Method

The existing compiled `RELIFT_PROFILE=berlekamp` arm in
`bench/HexBench/RecursiveReliftSpike.lean` now has three matched witness
callbacks:

- `baseline`: the pre-change recursion and unreduced GCD candidate;
- `reduced`: the same recursion with the guard remainder passed to the GCD;
- `linear stop`: a bench-local copy of the production recursion, which emits
  size-at-most-two leaves without scanning witnesses.

Each direct callback is `@[noinline]`, starts from the same precomputed fixed
space, and returns a boundary-sensitive checksum of the stored factor list.
The callback aborts if the baseline, remainder-reuse prototype, linear-stop
copy, and complete production `berlekampFactor` result disagree. Only the
`factor_baseline_us` and `factor_fixed_us` columns time the complete production
factorization callback.

An instrumented version brackets the following pure operations with
`IO.monoNanosNow` and forces each result through a no-inline IO identity:

1. `witness % f` and the constant guard;
2. construction of `c` and `witness - C c` for each attempted constant;
3. `DensePoly.gcd f (witness - C c)`, including its polynomial remainder
   sequence;
4. `f / factor` for a successful split.

The outer clock covers the complete recursive split. Subtracting the four
operation clocks leaves witness traversal, recursive child processing, stats
bookkeeping, and list construction as the residual. Operation timings are
medians of 31 single-call samples. The direct A/B timings are separate
uninstrumented medians, because per-operation clocks add observable overhead.

Dynamic counters are deterministic and checked on every sample: factors
visited, witnesses tried, constants tried, GCD calls, successful splits, and
the ordered factor/cofactor degree pairs. The reported `constants` count is
the number actually reached before a successful constant or exhausted sweep.
It equals the GCD-call count by instrumentation construction: each reached
constant records exactly one call.

The executable prints one phase line and one witness line per input. The CSV
joins those lines by input, renames `profile_reduced_us` to
`reduced_profile_us`, and appends the phase line's `shared_baseline_us`,
`fixed_us`, and `factor_speedup` as `factor_baseline_us`, `factor_fixed_us`,
and `factor_speedup`.

Measurement environment:

- source base: `3ccfd115`, plus the #8888 working-tree change;
- Lean: `leanprover/lean4:v4.32.0-rc1`;
- host: `chungus2`;
- CPU: AMD EPYC 9455 48-Core Processor, 96 logical CPUs;
- OS: Linux 6.12.95, x86-64;
- command: `lake build hex_recursive_relift_spike`, then
  `RELIFT_PROFILE=berlekamp .lake/build/bin/hex_recursive_relift_spike`.

Raw medians and counts are in
`reports/bench-results/berlekamp-witness-split-profile.csv`.

## Dynamic work

`F` is factors visited, `W` is witness attempts before and after the linear
stop, `C/G` is both constants tried and GCD calls, and `S` is successful
splits. Degree pairs are in stored depth-first order; the CSV records every
pair explicitly.

| input | p | r | F | W old -> new | C/G | S | degree-pair shape |
|---|---:|---:|---:|---:|---:|---:|---|
| split h2 d6 | 7 | 6 | 11 | 46 -> 10 | 20 | 5 | `1x5, ..., 1x1` |
| split h2 d8 | 11 | 8 | 15 | 78 -> 14 | 39 | 7 | `1x7, ..., 1x1` |
| split h2 d10 | 11 | 10 | 19 | 118 -> 18 | 54 | 9 | `1x9, ..., 1x1` |
| split h2 d12 | 13 | 12 | 23 | 166 -> 22 | 77 | 11 | `1x11, ..., 1x1` |
| split h2 d14 | 17 | 14 | 27 | 222 -> 26 | 108 | 13 | `1x13, ..., 1x1` |
| split h2 d16 | 17 | 16 | 31 | 286 -> 30 | 135 | 15 | `1x15, ..., 1x1` |
| split h2 d18 | 19 | 18 | 35 | 358 -> 34 | 170 | 17 | `1x17, ..., 1x1` |
| split h2 d20 | 23 | 20 | 39 | 438 -> 38 | 213 | 19 | `1x19, ..., 1x1` |
| split h2 d22 | 23 | 22 | 43 | 526 -> 42 | 252 | 21 | `1x21, ..., 1x1` |
| split h2 d24 | 29 | 24 | 47 | 622 -> 46 | 315 | 23 | `1x23, ..., 1x1` |
| phi15 | 7 | 2 | 3 | 6 -> 6 | 3 | 1 | `4x4` |
| SD3 | 7 | 4 | 7 | 22 -> 22 | 12 | 3 | `2x6, 2x4, 2x2` |
| SD4 | 11 | 8 | 15 | 78 -> 78 | 42 | 7 | `2x14, ..., 2x2` |

On the split grid, the old witness count is `r^2 + 2(r - 1)`: every one of
the `r` linear leaves scans all `r` witnesses, while the internal split chain
uses `2(r - 1)` attempts. The fast path removes the `r^2` term exactly. It
does not change constants, GCD calls, successful splits, or degree pairs.

## Time attribution

Times are microseconds. Phase percentages use the instrumented baseline total;
the speedup uses the separate uninstrumented callbacks.

| input | direct old | direct new | speedup | guard | sweep | GCD | cofactor | traversal/list |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| split h2 d6 | 39.5 | 23.0 | 1.72x | 39.1% | 5.9% | 35.3% | 7.2% | 12.5% |
| split h2 d8 | 84.8 | 47.9 | 1.77x | 41.0% | 5.3% | 37.6% | 5.6% | 10.5% |
| split h2 d10 | 140.8 | 70.9 | 1.99x | 46.3% | 4.6% | 34.7% | 5.0% | 9.5% |
| split h2 d12 | 224.7 | 108.0 | 2.08x | 48.8% | 4.1% | 34.2% | 4.4% | 8.5% |
| split h2 d14 | 341.2 | 159.1 | 2.15x | 50.4% | 3.8% | 34.4% | 3.9% | 7.5% |
| split h2 d16 | 480.2 | 208.0 | 2.31x | 53.0% | 3.4% | 32.9% | 3.6% | 7.0% |
| split h2 d18 | 654.3 | 275.7 | 2.37x | 54.5% | 3.2% | 32.6% | 3.2% | 6.4% |
| split h2 d20 | 869.4 | 361.6 | 2.40x | 55.4% | 3.0% | 32.8% | 2.9% | 5.9% |
| split h2 d22 | 1129.3 | 446.8 | 2.53x | 57.3% | 2.8% | 31.8% | 2.7% | 5.5% |
| split h2 d24 | 1457.0 | 584.5 | 2.49x | 57.0% | 2.7% | 32.7% | 2.5% | 5.1% |
| phi15 | 10.1 | 10.1 | 1.00x | 15.7% | 5.6% | 57.1% | 12.3% | 9.2% |
| SD3 | 46.4 | 46.5 | 1.00x | 26.9% | 4.8% | 55.4% | 6.0% | 6.8% |
| SD4 | 325.5 | 321.4 | 1.01x | 31.7% | 3.1% | 58.1% | 3.6% | 3.4% |

The complete `berlekampFactor` callback, including the shared matrix and
nullspace construction, improves from 51.4 to 35.1 us at degree 6 and from
1566.7 to 698.6 us at degree 24. It remains unchanged within noise on phi15,
SD3, and SD4, as expected from their non-linear leaves.

## Correctness and output order

The optimization does not reorder witnesses, constants, children, or lists.
It skips only a search proved impossible from the executable predicate itself:
a successful candidate has positive degree and size strictly below `f`, while
positive degree implies size at least two. Such a candidate cannot exist when
`f.size <= 2`.

The existing product, positivity, `Nodup`, recursion-descent, completeness,
and per-factor no-split proofs have been extended across this branch. Exact
conformance guards pin a linear singleton, the ordered two-factor quadratic
result, and a mixed degree-1/5/2 tree with product reconstruction. The compiled
profile additionally requires identical full factor-list checksums, split
counts, and ordered degree pairs for every input before printing measurements.
