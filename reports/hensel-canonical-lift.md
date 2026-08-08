# Hensel Lifting: Canonical Coefficients and Where the Reduction Cost Is

Issue #9131 asked whether the quadratic multifactor lift keeps redundant
coefficient reductions, and predicted that removing them would recover a large
part of the 21.0% of total time the elbow baseline attributes to
`Hex.ZPoly.reduceModPowImpl` on `cyclo_phi179`.

The audit's premise is **correct in kind and wrong in magnitude**. Every
reduction the issue names as possibly redundant is proved redundant here and
removed. They are also, all of them, the cheap ones: removing all three is
worth nothing measurable on `cyclo_phi179`. The `reduceModPowImpl` share the
baseline measured is not the canonicalisation between steps at all. It is the
mod-`m²` arithmetic *inside* `quadraticHenselStepBignum` -- above all inside
the monic division kernel, which reduces a whole polynomial on every division
iteration.

Attacking it there does pay. Reducing through a window rather than a division
takes **8.7% off the lift on `cyclo_phi179` and 10.0% on Wilkinson 56**, and
6.4% and 6.5% off their total factor time. What remains is not reduction at
all: schoolbook dense multiplication is about 45% of lift time on
`cyclo_phi179`, which already satisfies the trigger the issue reserves for
Phase 3.

This page records the invariant, the three removals, the fused reduction, and
the attribution that locates what is left.

## Revision and protocol

- Branch `issue-9131`, Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores.
- Baseline of comparison: [reports/hexbz-cactus-elbow.md](hexbz-cactus-elbow.md)
  at source revision `c34ffbbb`, and its records
  `hexbz-phase-profile-c34ffbbb-chungus2.json` and
  `hexbz-factor-sampling-profiles-c34ffbbb-chungus2.json`.
- Comparisons here are **arm-alternating**: the arms are three service binaries
  differing only in which `@[csimp]` rules are enabled, and a round runs every
  arm back to back before the next round starts, so a drift in host load lands
  on all arms rather than on one. Reported timings are the median over rounds;
  allocation counts are exact and identical across rounds.
- The measured service was pinned to one core, but **not** to core 0: three
  agent worktrees were measuring this corpus concurrently and the shared recipe
  pins to core 0, so all three collided there. See "a measurement trap worth
  recording" below. Phase profiles used `taskset -c 0` during windows when
  `ps -eo psr` showed no sibling service there; the corpus sweep used
  `taskset -c 8` after checking that core and its SMT sibling were idle.
- Every timing table below records the load average its rounds started at, and
  only comparisons whose rounds all ran under load average 6 are reported.
  Rounds taken under heavier load inflated *every* arm by a factor of two to
  three; they are excluded rather than averaged in. Each table is accompanied
  by exact allocation counters for the same arms, which are load-independent
  and move in the same direction.

## The coefficient-range invariant

`Hex.ZPoly.Canonical f m` states that every coefficient of `f` lies in
`[0, m)`. It is what the modular kernels produce and exactly the hypothesis
under which `reduceModPow` is the identity
(`ZPoly.reduceModPow_eq_self_of_canonical`), so it is what licenses deleting a
canonicalisation rather than merely moving one.

Every field of `quadraticHenselStepBignum` is built by `addModSquare` or
`subModSquare`, whose last action is `reduceModSquare _ m`. So a step at
working modulus `m` returns data canonical modulo `m²`
(`ZPoly.quadraticHenselStep_canonical`), and the word path denotes the same
values: its `ofWP` readback lands in the same window, and it is already proved
equal to the bignum path by `quadraticHenselStep_eq_bignum`. The factor-only
step inherits this (`quadraticHenselFactors_canonical`).

`liftExact` reaches `p^k` from `p^ceil(k/2)`. For **even** `k` the step's
working modulus squares to exactly `p^k`, so the result is already canonical at
the target; for **odd** `k` the step overshoots to `p^(k+1)` and the descent is
genuinely required. That answers the issue's question directly.

## What was removed

Three reductions, each with an explicit theorem and each landing as a
`@[csimp]` implementation paired with its unchanged specification, so no
existing proof about the lift changed:

| removal | theorem | condition |
|---|---|---|
| `reduceLift` after an even-exponent doubling | `reduceLift_step_eq_of_even` | `k` even |
| the closing pair in `henselLiftFactors` | `quadraticHenselFactors_canonical` | `k` even |
| the per-leaf reduction in the multifactor tree | `henselLiftFactors_canonical` | every leaf below the root |

The third is the one the issue did not name. Every recursive call in
`multifactorLiftQuadraticList` receives a `henselLiftFactors` output, which is
canonical at `p^k` by construction, so only the root -- whose target the caller
supplies as an arbitrary integer polynomial -- can still need the leaf
reduction.

## What that was worth

Lift-phase allocation counts, which are exact:

| instance | k | lift allocations, baseline | after removals | change |
|---|---:|---:|---:|---:|
| `cyclo_phi179` | 113 | 1,354,541 | 1,354,173 | -0.03% |
| `cyclo_phi385` | 152 | 3,767,689 | 3,761,417 | -0.17% |
| `cyclo_phi128_x_phi165` | 52 | 1,551,120 | 1,548,620 | -0.16% |
| `wilkinson_56` | -- | 607,717 | 605,515 | -0.36% |
| `xpow105_minus1` | 26 | 447,097 | 446,063 | -0.23% |
| `chebyshev_U24` (control) | 33 | 14,296 | 14,212 | -0.59% |

Lift time under load average below 5, median of three alternating rounds. The
Wilkinson rows answer from the proposal-replay tier, so their lift runs inside
`proposeFactorization` and the figure quoted for them is that whole phase, not
the lift alone; the same caveat applies to their allocation counts above.

| instance | k | lift, baseline | after removals | change |
|---|---:|---:|---:|---:|
| `sd5` | 19 | 1.961 ms | 1.869 ms | -4.7% |
| `sd5_shift1` | 19 | 1.985 ms | 1.904 ms | -4.1% |
| `sd5_shift2` | 19 | 1.981 ms | 1.912 ms | -3.5% |
| `sd4_x_sd4shift1` | 17 | 1.915 ms | 1.846 ms | -3.6% |
| `sd5_x_phi11` | 21 | 3.141 ms | 3.074 ms | -2.1% |
| `xpow48_minus1` | 14 | 1.171 ms | 1.103 ms | -5.8% |
| `xpow105_minus1` | 26 | 15.688 ms | 15.303 ms | -2.5% |
| `xpow120_minus1` | 43 | 21.476 ms | 20.979 ms | -2.3% |
| `cyclo_phi179` | 113 | 58.844 ms | 59.321 ms | +0.8% |
| `cyclo_phi64_x_phi105` | 24 | 7.780 ms | 7.529 ms | -3.2% |
| `cyclo_phi128_x_phi165` | 52 | 64.653 ms | 64.625 ms | -0.0% |
| `cyclo_phi385` | 152 | 166.572 ms | 162.070 ms | -2.7% |
| `wilkinson_40` (replay) | -- | 9.413 ms | 9.255 ms | -1.7% |
| `wilkinson_48` (replay) | -- | 19.856 ms | 19.515 ms | -1.7% |
| `wilkinson_56` (replay) | -- | 26.129 ms | 25.832 ms | -1.1% |
| `chebyshev_T24` (control) | 22 | 130 us | 117 us | -10.4% |
| `chebyshev_U24` (control) | 33 | 279 us | 268 us | -3.7% |
| `legendre_P30` (control) | 15 | 459 us | 443 us | -3.5% |
| `legendre_P38` (control) | 19 | 661 us | 642 us | -2.8% |
| `cyclo_phi17` (control) | 11 | 2.4 us | 2.4 us | -0.4% |
| `cyclo_phi41` (control) | 26 | 684 us | 650 us | -4.9% |
| `xpow24_minus1` (control) | 7 | 313 us | 301 us | -3.9% |
| `randprod_10` (control) | 11 | 177 us | 168 us | -5.0% |
| `randprod_21` (control) | 9 | 341 us | 325 us | -4.7% |

A few percent on rows with many cheap lifts, and **nothing on the two rows the
issue targets**. End-to-end factor time moves by less than the round-to-round
spread everywhere.

The reason is structural, and it is visible in the exponents. The removals fire
on even target exponents and on leaves. `cyclo_phi179` lifts to `3^113`; its
recursion visits 113, 57, 29, 15, 8, 4, 2, 1, so the three exponents whose
reduction is skipped are 8, 4 and 2 -- the cheapest three in a chain whose cost
is geometric in the exponent. Its two leaf reductions are skipped too, but a
leaf reduction reduces data that is *already* canonical, which is the case a
bignum remainder answers almost immediately. What survives is the reduction at
exponent 113, which is required because 113 is odd, and the reductions at 57,
29 and 15.

## Where the reduction cost actually is

The elbow baseline's sampling profile answers this once the inclusive tree is
read rather than the flat share. On `cyclo_phi179`:

| function | inclusive share of total |
|---|---:|
| `Hex.ZPoly.henselLiftFactors` | 72.13% |
| `Hex.ZPoly.quadraticHenselStepBignum` | 41.99% |
| `Hex.DensePoly.mulImpl` | 32.27% |
| `Hex.ZPoly.quadraticHenselFactors` | 23.72% |
| `Hex.ZPoly.reduceModPowImpl` | 20.99% |

`reduceModPowImpl` sits *under* the two step entries, not beside them. It is
`reduceModSquare`, called by `addModSquare`, `subModSquare`, `mulModSquare` and
-- decisively -- by the monic division kernel `divModMonicModSquareAux`, which
reduces a whole polynomial on every division iteration and so spends
`O(deg²)` coefficient reductions per step. The canonicalisations the issue
asked about are a rounding error next to that.

## Reducing through a window instead of a division

Rounds for this comparison started at load averages 3.56, 3.14, 3.06, 3.08,
3.05, 3.15, 3.17, 3.72, 3.42, 3.51, 3.54, 3.90 -- the quietest window this host
offered.

The operands of those internal reductions are themselves canonical. Their sum
therefore lies in `[0, 2m)` and their difference in `(-m, m)`: at worst one
modulus away from canonical. `ZPoly.intModNatImpl` tests for that first. A
value already in `[0, m)` is returned without allocating; a value in `[-m, 0)`
costs one bignum addition; only genuinely wide values -- products, and the
descent from a doubled precision -- still pay for `Int.emod`. It is a
`@[csimp]` implementation of the unchanged `intModNat`, so the entire proof
surface is untouched, and it is the "fuse addition/subtraction with reduction"
bullet of the issue's Phase 2 obtained without introducing a new type.

This is the change that pays. Six alternating rounds, every round started at
load average between 3.0 and 3.9, arms differing only in whether the
`intModNat_eq_impl` `@[csimp]` rule is enabled. Times are the minimum over
rounds; allocation counts are exact.

| instance | k | lift, removals only | + windowed | change | lift allocations | change |
|---|---:|---:|---:|---:|---:|---:|
| `cyclo_phi179` | 113 | 59.431 ms | 54.285 ms | **-8.7%** | 1,354,173 → 1,235,250 | -8.78% |
| `cyclo_phi385` | 152 | 162.716 ms | 142.995 ms | **-12.1%** | 3,761,417 → 3,439,553 | -8.56% |
| `wilkinson_56` (replay) | -- | 25.740 ms | 23.177 ms | **-10.0%** | 605,515 → 565,003 | -6.69% |
| `cyclo_phi64_x_phi105` | 24 | 7.511 ms | 6.792 ms | -9.6% | 241,538 → 226,755 | -6.12% |
| `xpow105_minus1` | 26 | 15.401 ms | 14.145 ms | -8.1% | 446,063 → 420,393 | -5.75% |
| `legendre_P30` (control) | 15 | 441 us | 409 us | -7.3% | 14,888 → 14,544 | -2.31% |
| `sd5` | 19 | 1.882 ms | 1.786 ms | -5.1% | 63,902 → 61,662 | -3.51% |
| `chebyshev_U24` (control) | 33 | 270 us | 275 us | +1.6% | 14,212 → 14,169 | -0.30% |

End-to-end factor time over the same rounds:

| instance | removals only | + windowed | change |
|---|---:|---:|---:|
| `cyclo_phi179` | 79.629 ms | 74.494 ms | **-6.4%** |
| `wilkinson_56` | 40.221 ms | 37.590 ms | **-6.5%** |
| `cyclo_phi385` | 450.467 ms | 429.291 ms | -4.7% |
| `xpow105_minus1` | 82.386 ms | 80.893 ms | -1.8% |
| `cyclo_phi64_x_phi105` | 87.283 ms | 86.219 ms | -1.2% |
| `legendre_P30` (control) | 8.327 ms | 8.291 ms | -0.4% |
| `sd5` | 107.383 ms | 107.356 ms | -0.0% |
| `chebyshev_U24` (control) | 688 us | 718 us | +4.4% |

The one row that moves the wrong way, `chebyshev_U24`, is a 700 microsecond
control whose lift is 275 microseconds; its 4.4% is within the round-to-round
spread of a row that small, and its allocation count still falls.

The rows that gain most are exactly the ones the mechanism predicts: the ones
whose lift runs on the bignum path, where a `reduceModSquare` on canonical
operands used to cost a multi-limb division and now costs a comparison.

`legendre_P30` and `cyclo_phi64_x_phi105` are the prime-walk-bound rows, where
`modP` reduces arbitrary integer coefficients rather than canonical ones. They
gain too rather than regressing, which is the case that would have exposed the
extra comparison on the slow path as a real cost.

## What is left

`cyclo_phi179` and Wilkinson 56 do improve, by 8.7% and 10.0% of lift, but the
lift is still 74% of `cyclo_phi179`'s factorization. What remains is no longer
reduction.

On `cyclo_phi179`, `Hex.DensePoly.mulImpl` is 32.27% of total time against a
72.13% lift, so **schoolbook dense multiplication is about 45% of lift time**.
The lift is two factors of degree 89 raised to `3^113`; the two widest doubling
steps run at moduli `3^29` and `3^57`, both past the `m * m < 2^64` guard, so
they take the bignum path and multiply degree-89 polynomials with 90- and
180-bit coefficients by the `O(n²)` schoolbook kernel.

That is the trigger condition the issue reserves for Phase 3 -- "at least 25% of
material lift time to polynomial multiplication" -- and the profile already
satisfies it, before any representation rewrite. Two candidate lines follow,
and they are separable:

1. **Thresholded Karatsuba for the bignum product.** At degree 89 the
   coefficient-multiplication count falls from `89² = 7921` to roughly
   `89^1.585 ~ 1100`. It needs a proof that the specialized kernel equals the
   schoolbook specification, which the issue rightly insists on.
2. **A wider word path.** The word step is capped at `m * m < 2^64`. On
   `cyclo_phi179` that admits the steps up to `3^15` and excludes `3^29` and
   `3^57`, which are the expensive ones. A 128-bit Montgomery context would
   cover `3^29`; it is a new arithmetic layer, not a lift change.

Phase 2's full `ResiduePolynomial` rewrite is not what these measurements ask
for. The reduction cost it targets is now bounded above by the windowed
implementation's remaining share, and the multiplication cost it would not
change is the larger term.

## The corpus sweep, and a measurement trap worth recording

The committed record `hexbz-factor-sweep-7200f7d1-hex-chungus2.json` is a
complete hex-only sweep of all 392 corpus rows on a clean tree, passing its
differential cross-check, solving 376 of 392 -- the same set the `c34ffbbb`
baseline solves. Against that baseline it reads p10 0.965, median 1.001, p75
1.017, p90 1.048, max 1.178.

Five earlier attempts at the same sweep did not read like that. They came out
bimodal: roughly a quarter of rows at about 1.9 times the baseline, the rest at
1.0, with the slow set differing from run to run. Two complete sweeps of the
*same* binary differed by a p90 of 1.886, a minimum of 0.367 and a maximum of
2.713, and their slow sets overlapped by a Jaccard index of only 0.27. Within a
run the slow rows fell in contiguous blocks by sweep position.

The cause is worth recording because it will recur. This corpus's measurement
recipe pins the service with `taskset -c 0`, and three agent worktrees were
working the same tracking issue concurrently, each following that recipe. All
three measurement processes were therefore competing for **core 0** on a
96-core host, while the load average -- 2 to 5 for most of those runs -- gave no
hint of it. `ps -eo pid,psr` showed three `hexbz_factor_service` processes on
processor 0 at once.

The record above was taken with `taskset -c 8`, having first checked that core
8 and its SMT sibling were idle. That is a deliberate deviation from the
protocol's `-c 0`, and it is the only reason this sweep is usable. **When more
than one measurement can run on this host, pin each to a verified-idle core
rather than to core 0.**

Sweep-level end-to-end times for the elbow rows, against the `c34ffbbb`
baseline sweep, corroborate the phase-profile A/Bs:

| instance | baseline sweep | this sweep | change |
|---|---:|---:|---:|
| `cyclo_phi179` | 80.025 ms | 75.533 ms | -5.6% |
| `cyclo_phi385` | 455.841 ms | 431.827 ms | -5.3% |
| `wilkinson_56` | 40.396 ms | 38.793 ms | -4.0% |
| `xpow105_minus1` | 84.464 ms | 81.525 ms | -3.5% |
| `cyclo_phi128_x_phi165` | 205.261 ms | 198.591 ms | -3.2% |
| `wilkinson_48` | 29.732 ms | 28.430 ms | -4.4% |
| `wilkinson_40` | 15.912 ms | 15.451 ms | -2.9% |
| `cyclo_phi64_x_phi105` | 88.460 ms | 87.112 ms | -1.5% |
| `sd5` | 106.911 ms | 108.383 ms | +1.4% |

Cactus ranks are unchanged for every representative row.

## Reproduction

```sh
lake build hexbz_factor_service
python3 scripts/bench/factor_phase_profile.py --output /tmp/phase.json
python3 scripts/profile/factor_sampling_profile.py --output /tmp/profiles.json
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144
```

The arm-alternating comparison used three service binaries built from this
branch with the `@[csimp]` attributes on `liftExact_eq_impl`,
`henselLiftFactors_eq_impl`, `multifactorLiftQuadraticList_eq_impl` and
`intModNat_eq_impl` enabled or removed, and nothing else changed between them.
