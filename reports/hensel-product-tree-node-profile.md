# Node-level profile of the multifactor Hensel product tree

Issue #9154. Measured on `chungus2`, one warm
`hexbz_factor_service` process per run, medians over ten repeats after three
warm-up calls, `taskset`-pinned to a verified-idle core.

The `henselTreeProfile` entry of `hexbz_factor_service` re-walks the production
tree `Hex.ZPoly.multifactorLiftQuadraticListImpl` in `IO`, calling the
production functions in production order, and times every node's two
sub-products, its normalised XGCD, and every quadratic doubling step of that
node's exact-exponent lift. Its returned factor array is checked against
`Hex.ZPoly.multifactorLiftQuadratic` before any time is reported. Bignum steps
are additionally replayed piece by piece; the replay reconstructs the
*specification* shape of `quadraticHenselStepBignum`, so it prices the residual,
the `t·e` product, the monic modular division and the coefficient updates
separately.

## Where the proposal tier goes

`proposalProfile` times the tier; `henselTreeProfile` decomposes its Hensel
phase. Both on the pre-change tree:

| case | proposal tier | Hensel lift | node-level sum | tier explained |
|---|---|---|---|---|
| wilkinson_40 | 7.95 ms | 6.36 ms | 6.61 ms | 83.1% + 16.9% other timed phases |
| wilkinson_48 | 14.85 ms | 12.60 ms | 12.34 ms | 83.1% + 16.9% |
| wilkinson_56 | 18.66 ms | 15.71 ms | 15.85 ms | 84.9% + 15.1% |

The node-level sum accounts for 101-104% of the untimed lift call (the excess is
the instrumentation's own mark overhead). The remaining sixth of the tier is
peeling, CLD preparation, the lattice schedule, the piece product, replay and
acceptance, all of which `proposalProfile` already times, so the tier is
explained end to end.

## Inside a bignum doubling step, wilkinson_56

Six doubling steps run per node at `p = 67`, `k = 51`: exponents 1, 2, 4 clear
the word-sized guard `m² < 2⁶⁴`; exponents 7, 13 and the closing factor-only
step at 26 do not. The three bignum levels are 90% of the lift.

Replay attribution, summed over all 55 nodes:

| piece | before | after |
|---|---|---|
| factor-update division | 5.68 ms (33.5%) | 3.60 ms (26.5%) |
| Bezout-update division | 3.73 ms (22.0%) | 2.56 ms (18.8%) |
| factor update (products, adds, reductions) | 2.59 ms (15.3%) | 2.57 ms (18.9%) |
| Bezout update | 1.69 ms (10.0%) | 1.63 ms (12.0%) |
| Bezout residual | 1.54 ms (9.1%) | 1.46 ms (10.7%) |
| `t · e` product | 1.11 ms (6.6%) | 1.12 ms (8.3%) |
| residual `f - g·h` | 0.63 ms (3.7%) | 0.65 ms (4.8%) |
| **production bignum steps** | **17.14 ms** | **13.65 ms** |
| word-path steps | 1.30 ms | 1.27 ms |

The two monic modular divisions were 55.5% of a bignum step. Every *product* in
the step already goes through the Kronecker kernel of #9142/#9147 and together
they are under a tenth of it; the divisions were the only remaining
`Θ(deg f · deg f)` loop over individual coefficients.

The replay mirrors the specification, so it under-reports the change: it sees
the division improvement but not the narrowed target or the fused
canonicalisations, which is why the production step total falls further (-20.4%)
than the replayed pieces suggest.

## Why the division was the cost

`divModMonicModSquareAux` rebuilt *and re-canonicalised* the whole running
remainder and the whole running quotient at every elimination step, though a
step changes only `deg q + 1` remainder slots and one quotient slot. Per
iteration that is roughly five array allocations of length `deg p` and `2·deg p`
coefficient reductions where `deg q` is the arithmetic actually being done. On
`wilkinson_56` the root node's factor division ran 56 iterations over an 84-slot
remainder to eliminate against a 29-slot divisor.

Coefficient *width* turned out to matter far less than coefficient *count*: the
step at modulus `p⁷` (43-bit modulus) and the step at `p¹³` (79-bit) cost
2.0 ms and 2.3 ms at the root, while the factor-only step at `p²⁶` (158-bit)
cost 1.3 ms. Allocation and Lean-runtime dispatch dominate; a flat profile of
the whole run puts ~20% in `malloc`/`free`/`__gmpz_init_set` and ~10% in closure
dispatch and refcounting. That is what ruled out the tempting reading of the
#9142 evidence -- that the answer was another crossover on the multiplication
kernel.

## What was measured and rejected

* **Lowering the Kronecker crossover.** The products are already under a tenth
  of a bignum step. Nothing to recover.
* **Narrowing the step's target on its own.** The exact-exponent recursion hands
  the same `f` to every step, and that `f` carries the finally requested
  precision: at the first bignum step of a `wilkinson_56` lift the residual is
  310 bits wide against an 86-bit `m²`. Reducing the target first is correct and
  is kept, but measured as a wash on its own -- the reduction costs what the
  narrower products save. It is retained because it composes with the fused
  canonicalisations and bounds peak memory.
* **A second near-canonical window in the reducer** (`[m, 2m) → z - m`, so that
  a modular addition never divides). Measured 2% *slower*: the `z - m` is a
  `let`, so the subtraction is allocated whether or not the branch is taken.
  Reverted.
