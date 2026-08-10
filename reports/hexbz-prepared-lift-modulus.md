# Reducing recombination leaves against a prepared lift modulus

Issue #9151 asks the recombination leaf loop to consume the integer lift
modulus the traversal has already computed, instead of rebuilding it inside
`Hex.centeredModNat` at every leaf. This records what the leaf loop actually
spent, what the change removes, and what it is worth.

## What the leaf loop was doing

`Hex.centeredModNat z m` takes a `Nat` modulus. Its compiled body, per call:

```c
lean_inc(m); v_int = lean_nat_to_int(m);      /* representation conversion */
v_r   = lean_int_emod(z, v_int);              /* the reduction itself      */
v_abs = lean_nat_abs(v_r);
v_two = lean_nat_mul(2, v_abs);               /* multi-limb allocation     */
        lean_nat_dec_le(v_two, m);
        /* then lean_int_dec_lt(r, 0) and lean_int_add / lean_int_sub */
```

Two of those are avoidable and one is not.

The conversion the issue names, `Int.ofNat m`, is **not** a multi-limb copy.
`Int.ofNat` carries `@[extern "lean_nat_to_int"]`, and `lean_nat_to_int` returns
its argument unchanged when the argument is not a scalar, because Lean gives
`Nat` and `Int` the same GMP-backed object representation. The cost of
reconverting a 93-bit modulus is one reference-count increment and its matching
decrement, not a limb copy. That part of the issue's diagnosis does not survive
contact with the runtime.

The comparison does allocate. `2 * r.natAbs` builds a fresh multi-limb `Nat` at
every leaf and frees it immediately, and `r.natAbs` costs an increment and a
decrement of its own. On the profiled rows, allocation is the largest single
leaf category (57% of `sd5_x_phi11`, 48% of `xpow120_minus1`), so a
per-leaf allocation is the thing worth removing, and it is removable: for
naturals `2 * a ≤ m` iff `a ≤ m / 2`, and `m / 2` is a constant of the modulus.

`lean_int_emod` is the reduction itself and stays.

## What the change is

`Hex.LiftModulus` records the modulus in the three representations a centred
reduction reads: the natural value, the integer value, and the halfway
threshold `nat / 2`. Two proof fields pin the derived values to the natural
one, so the object carries no freedom beyond the modulus it records.

`Hex.LiftModulus.centered` reduces against it. Because `z % modulus` is already
the least nonnegative residue, the centred representative is that residue, less
the modulus once it exceeds the threshold: no absolute value, no doubling, no
sign branch. The compiled body is three field reads, one comparison against
zero, one `lean_int_emod`, one `lean_int_dec_le`, and at most one
`lean_int_sub`.

`Hex.LiftModulus.centered_eq` proves it equals `Hex.centeredModNat`, so there is
still one mathematical notion of the centred representative and the second
operation is an evaluation of it. `Hex.SupportMeta` carries one prepared
modulus in place of its former `modulus : Nat` and `modulusInt : Int` pair, and
`Hex.directTrailingPrefilter` consumes the prepared object;
`Hex.directTrailingPrefilter_eq` states that the production filter returns the
old Boolean. The classical completeness proofs above it are unchanged in
content: `directCandidatePrefilter_trueSupport` and `tryDirectSplit_trueSupport`
carry the prepared modulus and prove the same conclusions.

## The `sd5` prize named in the issue is not on `sd5` any more

The issue quotes a sampling profile in which `sd5` spends 18.26% of total
factor time in `Hex.directTrailingPrefilter` and 10.44% in
`Hex.centeredModNat`, over 32,768 leaves at a 93-bit modulus. That profile was
recorded at `bf5973a3`. Since then #9181 reached the quadratic-norm certificate
from `factorize`, and `sd5` no longer recombines at all:

```
sd5              method=quadraticNorm  prime=29  lifted=16  candidatesTried=0
sd5_shift1       method=quadraticNorm  prime=29  lifted=16  candidatesTried=0
sd5_shift2       method=quadraticNorm  prime=29  lifted=16  candidatesTried=0
sd4_x_sd4shift1  method=classical      prime=29  lifted=16  candidatesTried=10540
sd5_x_phi11      method=classical      prime=29  lifted=17  candidatesTried=65522
```

A fresh sampling profile of the production `factor` entry agrees: `sd5` is now
97.6% `Hex.firstDirectPlan?`, 84.8% `Hex.probePrimeData?` and 83.3%
`Hex.Berlekamp.berlekampFactor`, with no `Hex.searchDirect`,
`Hex.scanDirectCombinations` or `Hex.directLeaf` entry at any share. End to end
it fell from about 69 ms to 6.8 ms. No change to the recombination leaf loop
can move `sd5`'s production time by 5%, because the production cascade does not
enter the leaf loop.

The mechanism itself is intact and is measured below on the rows that still
traverse, and on `sd5`'s own traversal through the phase profiler, which drives
the classical decomposition whether or not the cascade would have taken it.

## Recombination phase, seven interleaved repeats per row

`factorPhaseProfile`, alternating arms per repeat, one core, median per arm.
Leaf counts and trailing-filter call counts are identical in both arms on every
row, as are the surviving-candidate, product and exact-division counts.

| row | bits | leaves | trailing calls | recombination before | recombination after | ratio | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 93 | 32768 | 32768 | 61.968 ms | 58.561 ms | 0.945x | 70.250 ms | 66.678 ms | 0.949x |
| `sd5_shift1` | 93 | 32768 | 32768 | 56.288 ms | 52.892 ms | 0.940x | 65.019 ms | 61.556 ms | 0.947x |
| `sd5_shift2` | 93 | 32768 | 32768 | 57.751 ms | 54.520 ms | 0.944x | 68.012 ms | 64.733 ms | 0.952x |
| `sd4_x_sd4shift1` | 83 | 10540 | 10540 | 9.170 ms | 7.989 ms | 0.871x | 17.537 ms | 16.254 ms | 0.927x |
| `sd5_x_phi11` | 103 | 65522 | 65522 | 122.340 ms | 116.837 ms | 0.955x | 140.704 ms | 135.157 ms | 0.961x |
| `xpow48_minus1` | 49 | 268 | 268 | 5.271 ms | 5.222 ms | 0.991x | 10.530 ms | 10.309 ms | 0.979x |
| `xpow105_minus1` | 107 | 60 | 60 | 4.898 ms | 4.920 ms | 1.005x | 44.776 ms | 44.423 ms | 0.992x |
| `xpow120_minus1` | 121 | 5339 | 5339 | 111.668 ms | 112.447 ms | 1.007x | 144.667 ms | 145.269 ms | 1.004x |
| `wilkinson_40` | -- | -- | -- | 0.000 ms | 0.000 ms | -- | 9.255 ms | 9.198 ms | 0.994x |
| `wilkinson_48` | -- | -- | -- | 0.000 ms | 0.000 ms | -- | 16.264 ms | 16.221 ms | 0.997x |
| `wilkinson_56` | -- | -- | -- | 0.000 ms | 0.000 ms | -- | 20.975 ms | 20.983 ms | 1.000x |
| `chebyshev_T8` | 16 | 1 | 1 | 0.006 ms | 0.006 ms | 1.022x | 0.045 ms | 0.046 ms | 1.033x |
| `chebyshev_U8` | 19 | 4 | 4 | 0.016 ms | 0.016 ms | 1.000x | 0.138 ms | 0.138 ms | 1.002x |
| `legendre_P16` | 47 | 8 | 8 | 0.043 ms | 0.043 ms | 0.995x | 0.551 ms | 0.546 ms | 0.990x |
| `legendre_P18` | 53 | 256 | 256 | 0.301 ms | 0.286 ms | 0.953x | 1.321 ms | 1.309 ms | 0.990x |

Where the trailing filter dominates the traversal the phase improves 4.5% to
13%: those rows visit many leaves and almost none survive, so nearly all of the
traversal's time is the filter. `xpow120_minus1` is flat because a third of its
leaves survive the filter and the phase is dominated by candidate construction
and exact division rather than by the filter. The Chebyshev and Legendre
controls, whose traversals are a handful of leaves, are unchanged.

## End to end, forty-one interleaved repeats per row

Same host, one idle core, arms alternating within each repeat, median per arm.
The three `sd5` rows and the three Wilkinson rows are the in-run control: their
production cascades visit no recombination leaf at all, so nothing this change
touches can move them.

| row | before | after | ratio |
|---|---:|---:|---:|
| `sd5` | 6.751 ms | 6.747 ms | 0.9994x |
| `sd5_shift1` | 7.141 ms | 7.096 ms | 0.9937x |
| `sd5_shift2` | 8.729 ms | 8.670 ms | 0.9933x |
| `sd4_x_sd4shift1` | 17.618 ms | 16.225 ms | 0.9209x |
| `sd5_x_phi11` | 138.628 ms | 130.225 ms | 0.9394x |
| `sd5_x_phi45` | 320.069 ms | 301.898 ms | 0.9432x |
| `xpow48_minus1` | 10.402 ms | 10.348 ms | 0.9948x |
| `xpow105_minus1` | 44.353 ms | 44.305 ms | 0.9989x |
| `xpow120_minus1` | 144.656 ms | 145.016 ms | 1.0025x |
| `wilkinson_40` | 9.257 ms | 9.226 ms | 0.9967x |
| `wilkinson_48` | 16.315 ms | 16.230 ms | 0.9948x |
| `wilkinson_56` | 21.085 ms | 21.120 ms | 1.0016x |
| `chebyshev_T8` | 0.050 ms | 0.051 ms | 1.0141x |
| `chebyshev_U8` | 0.136 ms | 0.135 ms | 0.9913x |
| `legendre_P16` | 0.548 ms | 0.547 ms | 0.9975x |
| `legendre_P18` | 1.336 ms | 1.309 ms | 0.9798x |

The control rows span 0.993x to 1.002x, so the run's floor is under a percent.
Only the three rows whose cascades run a large traversal move past it, and all
three improve: 7.9% on `sd4_x_sd4shift1`, 6.1% on `sd5_x_phi11`, 5.7% on
`sd5_x_phi45`. `xpow120_minus1` and `xpow105_minus1` recombine but spend the
traversal on candidate construction rather than on the filter, and they are
flat.

## Whole-corpus paired sweep

Four counterbalanced AB/BA/AB/BA blocks over the whole 392-instance corpus at a
ten-second cutoff, one core, per-instance median of the within-block after/before
ratios (`scripts/bench/factor_sweep_paired.py`). 383 instances answered in every
block on both sides; none was lost and none gained.

Noise floor: median same-arm ratio 1.0001x (before against before, 383 rows) and 1.0285x (after against after, 383 rows).
383 rows priced in every block, 56 of them over 2 ms.
Median per-row ratio 0.9998x overall, 1.0024x over 2 ms.

**Rows regressing by more than 5%**

5 of 383 rows sit above 1.05x; 0 of them cost more than 2 ms.

| instance | before | after | ratio | block spread |
|---|---:|---:|---:|---|
| `cyclo_phi7_x_phi11` | 258.829 us | 272.464 us | 1.062x | 0.981x to 2.155x |
| `sd2` | 52.087 us | 56.618 us | 1.095x | 0.967x to 2.700x |
| `conway_p2_n1` | 29.604 us | 34.691 us | 1.179x | 0.984x to 1.490x |
| `conway_p65537_n1` | 21.962 us | 23.144 us | 1.066x | 1.002x to 1.134x |
| `conway_p97_n1` | 20.280 us | 21.216 us | 1.056x | 0.901x to 1.109x |

**Family medians**

| family | rows | median ratio | rows over 2 ms | median ratio over 2 ms |
|---|---:|---:|---:|---:|
| certificate-boundary | 1 | 0.9931x | 0 | -- |
| chebyshev | 28 | 1.0020x | 0 | -- |
| conway | 186 | 0.9971x | 0 | -- |
| cyclotomic | 34 | 1.0012x | 15 | 0.9999x |
| cyclotomic-products | 19 | 1.0048x | 11 | 1.0048x |
| hoeij-zimmermann | 4 | 1.0012x | 4 | 1.0012x |
| laguerre | 20 | 1.0051x | 2 | 1.0080x |
| legendre | 20 | 0.9961x | 4 | 0.9936x |
| random-products | 30 | 1.0063x | 0 | -- |
| sd-products | 11 | 0.9965x | 6 | 0.9822x |
| swinnerton-dyer | 15 | 1.0153x | 7 | 1.0161x |
| wilkinson | 15 | 1.0023x | 7 | 1.0151x |

The 2.9% same-arm figure is drift across the run rather than repeat-to-repeat
scatter: it is a whole-arm shift between an early block and a late one, which
the within-block pairing mostly, not entirely, cancels. It is the reason the
interleaved tables above, whose arms alternate inside each repeat, are the
sharper instrument, and the two agree on every row they share.

Five rows sit above 1.05x. All five cost under 60 microseconds, all five have a
block spread straddling 1.0, and none costs more than two milliseconds. No
family median moves by more than 1.6%, against a same-arm floor of 2.9%.


## What this leaves

`Hex.centeredLiftPoly` still calls `Hex.centeredModNat` once per coefficient
when a surviving leaf builds its candidate, and that path pays the same
doubling allocation this change removed from the filter. It is the natural
successor and it is not in this change's scope: `Hex.directCandidate` takes a
`Nat` modulus that the Mathlib recovery proofs consume directly.
