# Pricing one more modular observation (issue #9156)

The direct prime planner stopped shopping for a prime at a fixed width: an image
with at most eight local factors was used unexamined, and a wider one bought up
to two bounded scouts. Eight is a threshold, not a price. It cannot see that
`cyclo_phi64_x_phi105`'s first prime already costs 7.5 ms downstream while the
two scouts it triggers cost 27 ms, and that neither of the primes they find is
any better.

This report replaces that threshold with a price comparison. `Hex.scoutPays`
asks whether the walk can still afford another observation, estimating both what
is on the table and what the rest of the walk may spend from shape already
observed. It is the walk's only stopping decision: it governs the first good
prime and every scouted candidate alike, and nothing about the corpus, the
instance, or its family enters it.

**What it is, precisely.** Both sides of the comparison are worst cases -- the
most any prime could save against the most the remaining walk could spend -- so
passing means the walk *could* pay for itself, not that it will. That is an
affordability gate, weaker than a value-of-information rule, and it is why the
walk can still buy an observation that turns out worthless. The measurements
below say where it does.

Running both binaries over the whole corpus in counterbalanced blocks finds
**seven** instances whose walk the rule changes, and every one improves:

| instance | prime | full splits | prime walk saved | before | after | ratio | block spread |
|---|---|---:|---:|---:|---:|---:|---|
| `cyclo_phi105_x_phi128` | 11 -> 11 | 1 -> 1 | 49.734 ms | 86.499 ms | 35.725 ms | 0.413x | 0.411x to 0.415x |
| `cyclo_phi64_x_phi105` | 11 -> 11 | 1 -> 1 | 26.618 ms | 45.369 ms | 18.818 ms | 0.415x | 0.414x to 0.416x |
| `sd4_x_phi17` | 11 -> 11 | 1 -> 1 | 3.806 ms | 6.764 ms | 2.918 ms | 0.431x | 0.427x to 0.436x |
| `legendre_P18` | 41 -> 37 | 2 -> 1 | 1.294 ms | 2.176 ms | 1.313 ms | 0.604x | 0.598x to 0.610x |
| `legendre_P20` | 43 -> 41 | 2 -> 1 | 1.847 ms | 2.809 ms | 1.900 ms | 0.677x | 0.667x to 0.686x |
| `cyclo_phi24_x_phi35` | 17 -> 13 | 2 -> 2 | 3.534 ms | 9.010 ms | 6.750 ms | 0.749x | 0.742x to 0.756x |
| `cyclo_phi275` | 13 -> 3 | 2 -> 1 | 163.958 ms | 812.736 ms | 646.342 ms | 0.795x | 0.793x to 0.797x |

Solved coverage is identical instance for instance -- the same 377 of 392 in
every block of both arms -- no instance above 1.10x costs more than 2 ms, and the
combined-cactus cumulative curve improves at every rank in the elbow band. The
mandatory `xpow105_minus1` control keeps its plan exactly, and with it an order
of magnitude.

**And on all seven changed rows the decision is confirmed by measurement.** For
each, the best *attainable* net gain -- the incumbent's measured downstream less
the cheapest downstream any candidate still reachable within the remaining fuel
offers, less every scout and split needed to reach it -- is negative. The rule
declined seven observations that could not have paid, and declined none that
could.

## Revision and protocol

Source revision `803ffa18`, toolchain `leanprover/lean4:v4.33.0-rc1`,
host `chungus2` (96 cores, x86_64, linux), clean worktree. Corpus
`bench/corpus/hexbz-factor-corpus.jsonl` (392 instances), sha256
`619913904240`.

The host was shared with other measurement work throughout, and that is not a
detail: a first attempt at the corpus comparison used one sweep pass per arm and
reported the long Swinnerton-Dyer rows at 1.25x to 1.31x, which the paired driver
put inside its control band at the same revision. Three of my own warm services
and another session's were sharing the chosen core. Every timing below is
therefore paired and counterbalanced.

**Paired and counterbalanced.** Two service binaries built from this worktree,
differing only in `HexBerlekampZassenhaus/Modular/PrimePlan.lean` and the
diagnostic entries of `bench/HexBench/FactorService.lean`, on one core chosen by
`scripts/bench/idle_core.py` and named explicitly to both arms. Blocks alternate
AB and BA so arm and position are not confounded, and each instance's ratio is
the median of the *within-block* after/before ratios, so a block's own load
affects both arms of that ratio equally.

**Per-candidate costs** are medians of `--plan-repeats 3` calls of one service,
merged after asserting the repeats agree on everything deterministic.

**Policy comparisons** are offline replays over those recorded per-candidate
costs, by `scripts/bench/prime_policy_replay.py`. No policy is timed against
another; they are priced against the same observations. The replay checks itself:
`--agrees-with voi` confirms it reproduces the prime the measured binary selected
on 24 of 24 rows.

### Artifacts

- `reports/bench-results/hexbz-factor-sweep-803ffa18-hex-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-corpus-paired-803ffa18-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-803ffa18-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-changed-rows-803ffa18-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-pricing-paired-803ffa18-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-pricing-paired-changed-803ffa18-chungus2.json`

## The rule

Write `n` for the degree of the modular image, `q` for the prime about to be
scouted, `w` and `d` for the width and largest modular factor degree of the plan
currently held, `W` for the machine words of that plan's Hensel modulus, and
`fuel` for the observations the walk may still make.

**What is still on the table.** A recombination candidate costs about `n^2`
coefficient operations on `W`-word integers, averaged over the cheap degree and
trailing-coefficient rejections and the subsets that reach a product. A complete
head-forced search visits `2^(w-1)` candidates, but the direct engine abandons
the search at `defaultSubsetBudget = 262144`, so the work still ahead is at most
`min(2^(w-1), 262144) · n^2 · W`. That is a worst case, not a prediction: an
irreducible input inside the budget does run the search to exhaustion, and
everything else stops earlier. It is also specific to the direct route; a plan
whose search declines goes on to proposal replay, the lattice tier or trial
division, none of which this models.

**What another observation costs.** A bounded scout runs one Frobenius power and
one gcd per separated degree, about `bitLen q` squarings of the degree-`n` image
apiece, and stops at the largest factor degree of the image it separates. That
degree is unknown before scouting, so `d` stands in for it. **This is a proxy,
not a bound**, and the records contain counterexamples in the awkward direction:
`legendre_P30`'s incumbent has `d = 2` where the next candidate reaches 14, and
`legendre_P18`'s 2 against 9. A narrower candidate tends to have larger factor
degrees, and a narrower candidate is exactly what the walk hopes to find, so the
proxy under-prices the scouts most likely to matter. Acting on what a scout
learns costs one further Berlekamp split, whose matrix and row reduction are
about `bitLen q · n^3`, and a walk with `fuel` observations left may spend at
most `fuel` scouts and one split.

Both estimates carry a factor `n^2`, which cancels, leaving

```
min(2^(w-1), 262144) · W  >  bitLen q · (scoutRoundCost · fuel · d + splitColumnCost · n)
```

`scoutRoundCost` and `splitColumnCost` scale a modular word operation against a
recombination candidate, which the inequality counts as one. Changing them
changes decisions.

A safe bound for the scout depth exists -- the loop's `m < 2·d` exit gives at
most `n/2` rounds -- and was rejected on evidence: it turns
`cyclo_phi24_x_phi35`, the row where scouting genuinely pays 14.7 ms for a 2.6 ms
observation, into a 1.07x near-tie. The proxy is documented rather than replaced.

### The two constants, and how far they can move

Dividing each measured cost by its model units, over the 144 priced candidates of
the committed per-candidate profile:

| word operation | model units | median | range | samples |
|---|---|---:|---|---:|
| bounded scout | `d · bitLen p · n^2` | 20.57 ns | 1.37 to 78.10 | 144 |
| Berlekamp split | `bitLen p · n^3` | 6.79 ns | 0.43 to 28.56 | 144 |
| recombination candidate | `n^2 · W` per visited node | 1.59 ns | 0.24 to 31.57 | 52 |

That puts the ratios at 12.9 and 4.3. Three records of the same source taken the
same day under different load put them at 10.2 and 5.2, 12.9 and 4.3, and 13.4
and 4.4. These are medians of noisy, heterogeneous per-candidate prices, so the
shipped `scoutRoundCost = 10` and `splitColumnCost = 5` are not precise and are
not claimed to be.

What is claimed instead is that the policy does not balance on them:

> 116 of 120 ratio pairs over `scoutRoundCost` 6 to 20 and `splitColumnCost` 2 to
> 9 reproduce the shipped pair's whole replayed walk -- selected prime, splits
> and scouts -- on every one of the 29 recorded instances.

| scoutRoundCost | splitColumnCost | rows that move | regret |
|---:|---:|---|---:|
| 6 | 2 | `cyclo_phi24_x_phi35`, `cyclo_phi275` | +126.536 ms |
| 7 | 2 | `cyclo_phi24_x_phi35`, `cyclo_phi275` | +126.536 ms |
| 8 | 2 | `cyclo_phi24_x_phi35` | +2.273 ms |
| 9 | 2 | `cyclo_phi24_x_phi35` | +2.273 ms |

All four exceptions sit at `splitColumnCost = 2`, less than half the smallest
measured value, and all four are *worse* than the shipped pair. This is in-sample
robustness: the instances are the ones the rule was designed against, so it says
the decisions are not on a knife edge, not that they generalize.

The recombination row is calibrated against *measured* node counts rather than
`2^(w-1)`, because it prices one candidate. The model's use of the capped subset
count for how many candidates there are is the separate, deliberately
conservative step.

## Investigation

### Every decision, against what it was worth

`left` is `min(2^(w-1), 262144) · W`; `next obs` is the right-hand side. What
settles a decision is the last two columns: for every alternative still reachable
within the remaining fuel, the gain is the incumbent's measured downstream less
that alternative's and the cost is every bounded scout needed to reach it plus its
split; the column reports the best net over those. A decision is confirmed when
the sign of the best net agrees with it.

First the seven rows the rule changed. Note `cyclo_phi24_x_phi35`, where the
decision that changed is the *second* call, after prime 13 becomes the incumbent:
the walk keeps scouting when scouting pays and stops when it stops paying.

### Every `scoutPays` decision, against what it was worth

| instance | step | incumbent | w | max deg | fuel | next | left | next obs | scout? | own downstream | best attainable net | confirmed |
|---|---:|---:|---:|---:|---:|---:|---:|---:|:--:|---:|---:|:--:|
| `cyclo_phi105_x_phi128` | 1 | 11 | 10 | 32 | 2 | 13 | 1024 | 4800 | no | 12.390ms | none | yes |
| `sd4_x_phi17` | 1 | 11 | 9 | 16 | 2 | 13 | 256 | 1920 | no | 1.241ms | none | yes |
| `legendre_P18` | 1 | 37 | 9 | 2 | 2 | 41 | 256 | 780 | no | 570.826us | none | yes |
| `cyclo_phi24_x_phi35` | 1 | 11 | 12 | 3 | 2 | 13 | 2048 | 880 | yes | 15.356ms | 10.823ms at 13 | yes |
| `cyclo_phi24_x_phi35` | 2 | 13 | 10 | 4 | 1 | 17 | 512 | 1000 | no | 1.935ms | none | yes |
| `cyclo_phi275` | 1 | 3 | 10 | 20 | 2 | 5 | 2048 | 4200 | no | 610.721ms | none | yes |
| `cyclo_phi64_x_phi105` | 1 | 11 | 10 | 16 | 2 | 13 | 1024 | 2880 | no | 7.508ms | none | yes |

The measurement confirms every decision above; 0 decision(s) have no priced alternative to compare against.

`cyclo_phi105_x_phi128`, `cyclo_phi275` and `cyclo_phi64_x_phi105` have *no*
better prime reachable at all, so the observation the fixed threshold bought
could not have paid at any price. `cyclo_phi275` is the clearest: all three
priced candidates have width 10 and largest factor degree 20, and their
downstreams are 610.7, 639.2 and 613.4 ms. There is nothing there to find, and
the fixed rule spent 190 ms of prime walk looking.

Now the same table over the issue #9127 representative set and its controls.

### Every `scoutPays` decision, against what it was worth

| instance | step | incumbent | w | max deg | fuel | next | left | next obs | scout? | own downstream | best attainable net | confirmed |
|---|---:|---:|---:|---:|---:|---:|---:|---:|:--:|---:|---:|:--:|
| `sd5` | 1 | 19 | 16 | 2 | 2 | 23 | 65536 | 1000 | yes | 64.451ms | none | **no** |
| `sd5` | 2 | 23 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 63.446ms | none | **no** |
| `sd5_shift1` | 1 | 19 | 16 | 2 | 2 | 23 | 65536 | 1000 | yes | 58.440ms | none | **no** |
| `sd5_shift1` | 2 | 23 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 58.343ms | none | **no** |
| `sd5_shift2` | 1 | 19 | 16 | 2 | 2 | 23 | 65536 | 1000 | yes | 59.269ms | none | **no** |
| `sd5_shift2` | 2 | 23 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 59.210ms | none | **no** |
| `sd4_x_sd4shift1` | 1 | 13 | 16 | 2 | 2 | 17 | 65536 | 1000 | yes | 10.466ms | none | **no** |
| `sd4_x_sd4shift1` | 2 | 17 | 16 | 2 | 1 | 19 | 65536 | 900 | yes | 10.491ms | none | **no** |
| `sd4_x_sd4shift1` | 3 | 17 | 16 | 2 | 1 | 23 | 65536 | 900 | yes | 10.491ms | none | **no** |
| `sd4_x_sd4shift1` | 4 | 17 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 10.491ms | none | **no** |
| `sd5_x_phi11` | 1 | 19 | 17 | 10 | 2 | 23 | 131072 | 2050 | yes | 137.301ms | none | **no** |
| `sd5_x_phi11` | 2 | 19 | 17 | 10 | 1 | 29 | 131072 | 1550 | yes | 137.301ms | none | **no** |
| `xpow48_minus1` | 1 | 5 | 20 | 4 | 2 | 7 | 262144 | 960 | yes | 5.253ms | none | **no** |
| `xpow48_minus1` | 2 | 5 | 20 | 4 | 1 | 11 | 262144 | 1120 | yes | 5.253ms | none | **no** |
| `xpow105_minus1` | 1 | 11 | 30 | 6 | 2 | 13 | 524288 | 2580 | yes | 411.915ms | 379.097ms at 17 | yes |
| `xpow105_minus1` | 2 | 11 | 30 | 6 | 1 | 17 | 524288 | 2925 | yes | 411.915ms | 381.507ms at 17 | yes |
| `xpow120_minus1` | 1 | 7 | 39 | 4 | 2 | 11 | 524288 | 2720 | yes | 127.407ms | none | **no** |
| `xpow120_minus1` | 2 | 7 | 39 | 4 | 1 | 13 | 524288 | 2560 | yes | 127.407ms | none | **no** |
| `cyclo_phi179` | 1 | 3 | 2 | 89 | 2 | 5 | 6 | 8010 | no | 28.131ms | -- | -- |
| `cyclo_phi64_x_phi105` | 1 | 11 | 10 | 16 | 2 | 13 | 1024 | 2880 | no | 7.494ms | none | yes |
| `cyclo_phi128_x_phi165` | 1 | 7 | 8 | 20 | 2 | 11 | 384 | 4480 | no | 39.508ms | -- | -- |
| `cyclo_phi385` | 1 | 3 | 4 | 60 | 2 | 5 | 32 | 7200 | no | 85.379ms | -- | -- |
| `wilkinson_40` | 1 | 41 | 40 | 1 | 2 | 43 | 1048576 | 1320 | yes | 7.131ms | none | **no** |
| `wilkinson_40` | 2 | 41 | 40 | 1 | 1 | 47 | 1048576 | 1260 | yes | 7.131ms | none | **no** |
| `wilkinson_48` | 1 | 53 | 48 | 1 | 2 | 59 | 1310720 | 1560 | yes | 13.095ms | none | **no** |
| `wilkinson_48` | 2 | 59 | 48 | 1 | 1 | 61 | 1310720 | 1500 | yes | 13.168ms | none | **no** |
| `wilkinson_56` | 1 | 59 | 56 | 1 | 2 | 61 | 1310720 | 1800 | yes | 16.908ms | none | **no** |
| `wilkinson_56` | 2 | 61 | 56 | 1 | 1 | 67 | 1310720 | 2030 | yes | 16.838ms | none | **no** |
| `chebyshev_T24` | 1 | 5 | 3 | 8 | 2 | 7 | 4 | 840 | no | 147.549us | -- | -- |
| `chebyshev_U24` | 1 | 3 | 4 | 10 | 2 | 5 | 8 | 960 | no | 312.393us | -- | -- |
| `legendre_P30` | 1 | 61 | 15 | 2 | 2 | 67 | 32768 | 1330 | yes | 29.020ms | 23.756ms at 67 | yes |
| `legendre_P30` | 2 | 67 | 7 | 14 | 1 | 71 | 128 | 2030 | no | 1.209ms | none | yes |
| `legendre_P38` | 1 | 79 | 3 | 36 | 2 | 83 | 8 | 6370 | no | 636.333us | -- | -- |
| `cyclo_phi17` | 1 | 3 | 1 | 16 | 2 | 5 | 1 | 1200 | no | 8.704us | -- | -- |
| `cyclo_phi41` | 1 | 3 | 5 | 8 | 2 | 5 | 16 | 1080 | no | 1.479ms | -- | -- |
| `xpow24_minus1` | 1 | 5 | 14 | 2 | 2 | 7 | 8192 | 480 | yes | 943.479us | 76.294us at 7 | yes |
| `xpow24_minus1` | 2 | 5 | 14 | 2 | 1 | 11 | 8192 | 560 | yes | 943.479us | none | **no** |
| `randprod_10` | 1 | 7 | 4 | 7 | 2 | 11 | 8 | 960 | no | 194.469us | -- | -- |
| `randprod_21` | 1 | 17 | 7 | 9 | 2 | 19 | 64 | 1500 | no | 366.263us | -- | -- |

The measurement confirms all but 23 above; 10 decision(s) have no priced alternative to compare against.

Read that honestly: of 39 decisions, 6 are confirmed, 23 are not, and 10 have no
priced alternative. Two limitations and one real finding come out of it.

**Ten decisions cannot be checked from these records.** The counterfactual prices
the *fixed* rule's retained set, which stops at the first good prime when that
image is narrow, so a narrow row has no alternative downstream to compare
against. Widening it to the whole scouting horizon would price them, at the cost
of replaying the downstream of primes no policy under test would select -- on
`xpow105_minus1` alone a 36-second row. The set was left pinned so the table
stays row-for-row comparable with the recorded baseline.

**All 23 unconfirmed decisions are acceptances, and every one is an acceptance
the fixed threshold also made.** Their incumbent widths run from 14 to 56, all
above `scoutWidth = 8`, so the old rule bought the same observation. The change
therefore removes seven observations that could not pay and introduces none. It
does not make the equal-width families better and was never going to; what it
does is stop the walk where looking was hopeless.

### Where the estimate is loosest, and why it stays

The three Wilkinson rows are the extreme case: the capped estimate says 262,144
recombination candidates remain, and 40 to 56 are actually visited. A Wilkinson
image is 40 to 56 linear factors, every one a rational root, so the search finds
the whole factorization in its first cardinality level.

No *degree-only* rule can determine that, because whether the search terminates
early is a fact about the answer: integer polynomials with the same modular
degree pattern can have different rational factorizations. But the degree
multiset is not silent either, and the report should not pretend otherwise.
`maxDegree = 1` together with `w = n` says the image is entirely linear, which is
a real signal that many candidates will be rational roots; per-cardinality counts
of subsets surviving the degree filter are computable from the multiset by the
same dynamic programme `reachableProperCount` already uses. An expected-cost model
could use those. This rule does not, because it is a worst-case affordability
gate, and a worst case cannot use a probabilistic signal.

That is the honest statement of the limit: not "no signal exists", but "this rule
is the wrong shape to exploit the signal that does". Tightening it means building
an expected-cost model and validating it on held-out families, which is a larger
piece of work than this issue. The Wilkinson rows are unchanged from the fixed
threshold, so nothing regresses in the meantime.

### Offline policy comparison

Every policy replayed over the same measured per-candidate costs.

### Offline policy replay

| instance | first | fixed | minwidth | maxfield | scout | voi | reachable | oracle | primes (first/fixed/scout/voi/oracle) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `sd5` | 66.907ms | 72.496ms | 72.848ms | 72.496ms | 70.563ms | 70.563ms | 68.556ms | 66.119ms | 19/29/29/29/23 |
| `sd5_shift1` | 61.180ms | 67.097ms | 67.093ms | 67.097ms | 65.309ms | 65.309ms | 63.832ms | 61.125ms | 19/29/29/29/23 |
| `sd5_shift2` | 62.040ms | 70.183ms | 70.195ms | 70.183ms | 67.666ms | 67.666ms | 65.457ms | 62.720ms | 19/29/29/29/23 |
| `sd4_x_sd4shift1` | 12.295ms | 18.777ms | 18.480ms | 18.777ms | 17.332ms | 17.332ms | 12.295ms | 12.295ms | 13/29/29/29/13 |
| `sd5_x_phi11` | 141.861ms | 144.997ms | 155.128ms | 144.997ms | 143.223ms | 143.223ms | 139.509ms | 135.001ms | 19/29/29/29/29 |
| `xpow48_minus1` | 6.626ms | 11.973ms | 11.973ms | 11.973ms | 10.293ms | 10.293ms | 6.626ms | 6.626ms | 5/11/11/11/5 |
| `xpow105_minus1` | 423.618ms | 50.554ms | 50.554ms | 50.554ms | 44.544ms | 44.544ms | 35.851ms | 24.160ms | 11/17/17/17/17 |
| `xpow120_minus1` | 143.469ms | 189.134ms | 189.134ms | 693.051ms | 145.898ms | 145.898ms | 143.469ms | 143.469ms | 7/7/7/7/7 |
| `cyclo_phi179` | 34.777ms | 34.777ms | 34.777ms | 34.777ms | 34.777ms | 34.777ms | 34.777ms | 34.777ms | 3/3/3/3/3 |
| `cyclo_phi64_x_phi105` | 18.126ms | 48.325ms | 48.325ms | 75.978ms | 44.982ms | 18.126ms | 18.126ms | 18.126ms | 11/11/11/11/11 |
| `cyclo_phi128_x_phi165` | 73.655ms | 73.655ms | 73.655ms | 73.655ms | 73.655ms | 73.655ms | 73.655ms | 73.655ms | 7/7/7/7/7 |
| `cyclo_phi385` | 143.973ms | 143.973ms | 143.973ms | 143.973ms | 143.973ms | 143.973ms | 143.973ms | 143.973ms | 3/3/3/3/3 |
| `wilkinson_40` | 8.874ms | 12.463ms | 12.403ms | 12.463ms | 10.886ms | 10.886ms | 10.591ms | 8.855ms | 41/47/47/47/43 |
| `wilkinson_48` | 15.898ms | 21.626ms | 21.603ms | 21.626ms | 19.057ms | 19.057ms | 15.898ms | 15.898ms | 53/61/61/61/53 |
| `wilkinson_56` | 21.006ms | 29.578ms | 29.408ms | 29.578ms | 25.840ms | 25.840ms | 25.057ms | 20.978ms | 59/67/67/67/61 |
| `chebyshev_T24` | 358.382us | 358.382us | 358.382us | 358.382us | 358.382us | 358.382us | 358.382us | 358.382us | 5/5/5/5/5 |
| `chebyshev_U24` | 510.678us | 510.678us | 510.678us | 510.678us | 510.678us | 510.678us | 510.678us | 510.678us | 3/3/3/3/3 |
| `legendre_P30` | 31.875ms | 6.980ms | 6.980ms | 6.980ms | 8.137ms | 8.137ms | 5.050ms | 2.213ms | 61/71/67/67/71 |
| `legendre_P38` | 3.545ms | 3.545ms | 3.545ms | 3.545ms | 3.545ms | 3.545ms | 3.545ms | 3.545ms | 79/79/79/79/79 |
| `cyclo_phi17` | 63.915us | 63.915us | 63.915us | 63.915us | 63.915us | 63.915us | 63.915us | 63.915us | 3/3/3/3/3 |
| `cyclo_phi41` | 1.951ms | 1.951ms | 1.951ms | 1.951ms | 1.951ms | 1.951ms | 1.951ms | 1.951ms | 3/3/3/3/3 |
| `xpow24_minus1` | 1.301ms | 2.445ms | 2.445ms | 2.445ms | 2.199ms | 2.199ms | 1.196ms | 841.556us | 5/11/11/11/7 |
| `randprod_10` | 546.230us | 546.230us | 546.230us | 546.230us | 546.230us | 546.230us | 546.230us | 546.230us | 7/7/7/7/7 |
| `randprod_21` | 1.257ms | 1.257ms | 1.257ms | 1.257ms | 1.257ms | 1.257ms | 1.257ms | 1.257ms | 17/17/17/17/17 |
| **aggregate** | **1.276s** | **1.007s** | **1.017s** | **1.539s** | **936.565ms** | **909.709ms** | **872.149ms** | **839.064ms** | |


The four policies the issue asks to be controlled against all fail, each in its
own way:

* **first** -- stopping at the first acceptable prime is unusable at 1.276 s.
  `xpow105_minus1` alone is 416.045 ms of that against 44.231 ms, and
  `legendre_P30` is 32.228 ms against 8.104 ms. This is why a scout-nothing rule
  is not on the table, and why `xpow105_minus1` is a mandatory control.
* **minwidth** -- a degree cost model on its own is worse than the score at
  1.017 s. `sd5_x_phi11` is where it shows: prime 23 is widest, and prime 29 wins
  only on the tie breaks the score already carries.
* **maxfield** -- a field-size cost model on its own is the worst of all at
  1.539 s. It picks the largest prime for its smaller Hensel precision and pays
  in recombination: `xpow120_minus1` goes from 146 ms to 697 ms.
* **fixed** -- the pre-scout rule, 1.007 s. The scout replaced it in #9128.

On this 24-instance set `voi` saves 26.856 ms of 936.565 ms and closes 41.7% of
the distance from `scout` to the `reachable` floor. Over the six changed rows the
separate record covers, it saves 254.692 ms of 954.146 ms and closes 99.9% of that
distance -- there is essentially nothing left on those rows for a discovering
policy to take. The `reachable` and `oracle` floors are unreachable by
construction: neither ever scouts, and the oracle names the winner without paying
to discover it.

## Paired before and after

### The rows whose walk changes, and their controls

`--changed` names the changed rows explicitly: a dropped scout moves neither the
selected prime nor the split count, so the driver's automatic control split cannot
see it.

### Paired before/after, median of 4 counterbalanced blocks (AB/BA/AB/BA)

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `cyclo_phi105_x_phi128` | 11 | 11 | 1 -> 1 | 71.735 ms | 22.001 ms | 49.734 ms | 85.521 ms | 35.266 ms | 0.413x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 1 -> 1 | 37.321 ms | 10.649 ms | 26.618 ms | 45.262 ms | 18.781 ms | 0.416x |
| `sd4_x_phi17` | 11 | 11 | 1 -> 1 | 5.317 ms | 1.511 ms | 3.806 ms | 6.628 ms | 2.905 ms | 0.438x |
| `legendre_P18` | 41 | 37 | 2 -> 1 | 1.992 ms | 692.436 us | 1.294 ms | 2.181 ms | 1.308 ms | 0.596x |
| `cyclo_phi24_x_phi35` | 17 | 13 | 2 -> 2 | 8.107 ms | 4.627 ms | 3.534 ms | 8.884 ms | 6.717 ms | 0.754x |
| `cyclo_phi275` | 13 | 3 | 2 -> 1 | 190.390 ms | 26.406 ms | 163.958 ms | 803.086 ms | 636.467 ms | 0.796x |
| `sd4_x_sd4shift1` | 29 | 29 | 2 -> 2 | 6.865 ms | 6.855 ms | 47.075 us | 17.617 ms | 17.761 ms | 1.012x |
| `xpow105_minus1` | 17 | 17 | 2 -> 2 | 29.299 ms | 29.271 ms | -26.400 us | 44.538 ms | 44.678 ms | 1.004x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 6.466 ms | 6.554 ms | -88.201 us | 34.899 ms | 35.148 ms | 1.010x |
| `legendre_P30` | 67 | 67 | 2 -> 2 | 7.101 ms | 7.046 ms | 55.722 us | 8.502 ms | 8.485 ms | 1.000x |
| `wilkinson_40` | 47 | 47 | 2 -> 2 | 4.122 ms | 4.251 ms | -128.450 us | 12.318 ms | 12.626 ms | 1.028x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 939.843 us | 952.968 us | -8.448 us | 1.393 ms | 1.429 ms | 1.025x |
| **aggregate** | | | | | | 248.795 ms | 1.071 s | 821.570 ms | **0.7672x** |

Load control (6 instances whose plan does not change, named by --changed): 1.000x to 1.028x.

`cyclo_phi275` is the largest absolute win: 163.958 ms of prime walk, because the
fixed rule scouted two further primes at 65 ms and 45 ms apiece and then split one
of them, all to select a prime whose downstream is 2 ms *worse* than the one it
started with.

### The issue #9127 representative set

The same protocol over the elbow set, where `cyclo_phi64_x_phi105` is the only
changed row. This is the table the acceptance threshold is read from.

### Paired before/after, median of 4 counterbalanced blocks (AB/BA/AB/BA)

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 29 | 2 -> 2 | 6.622 ms | 6.729 ms | -49.729 us | 68.294 ms | 68.337 ms | 1.001x |
| `sd5_shift1` | 29 | 29 | 2 -> 2 | 7.065 ms | 7.149 ms | -72.878 us | 63.171 ms | 63.567 ms | 1.006x |
| `sd5_shift2` | 29 | 29 | 2 -> 2 | 8.642 ms | 8.703 ms | -70.500 us | 66.944 ms | 67.055 ms | 1.003x |
| `sd4_x_sd4shift1` | 29 | 29 | 2 -> 2 | 6.817 ms | 6.859 ms | -17.320 us | 17.628 ms | 17.909 ms | 1.013x |
| `sd5_x_phi11` | 29 | 29 | 2 -> 2 | 16.261 ms | 16.489 ms | -329.634 us | 139.756 ms | 138.559 ms | 0.991x |
| `xpow48_minus1` | 11 | 11 | 2 -> 2 | 3.917 ms | 3.965 ms | -48.171 us | 10.450 ms | 10.452 ms | 1.012x |
| `xpow105_minus1` | 17 | 17 | 2 -> 2 | 29.249 ms | 29.386 ms | -166.242 us | 44.119 ms | 44.883 ms | 1.017x |
| `xpow120_minus1` | 7 | 7 | 1 -> 1 | 18.635 ms | 18.767 ms | -132.411 us | 146.400 ms | 148.638 ms | 1.016x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 6.554 ms | 6.639 ms | -85.502 us | 35.022 ms | 34.932 ms | 0.999x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 1 -> 1 | 37.520 ms | 10.773 ms | 26.777 ms | 45.066 ms | 18.825 ms | 0.418x |
| `cyclo_phi128_x_phi165` | 7 | 7 | 1 -> 1 | 34.887 ms | 35.093 ms | -206.120 us | 74.987 ms | 75.717 ms | 1.012x |
| `cyclo_phi385` | 3 | 3 | 1 -> 1 | 58.878 ms | 59.003 ms | -347.190 us | 144.229 ms | 144.712 ms | 1.007x |
| `wilkinson_40` | 47 | 47 | 2 -> 2 | 4.125 ms | 4.339 ms | -193.547 us | 12.427 ms | 12.756 ms | 1.028x |
| `wilkinson_48` | 61 | 61 | 2 -> 2 | 6.559 ms | 6.829 ms | -285.443 us | 21.400 ms | 22.012 ms | 1.029x |
| `wilkinson_56` | 67 | 67 | 2 -> 2 | 9.649 ms | 9.977 ms | -315.297 us | 28.735 ms | 29.702 ms | 1.034x |
| `chebyshev_T24` | 5 | 5 | 1 -> 1 | 218.539 us | 219.480 us | -3.209 us | 436.122 us | 449.306 us | 1.032x |
| `chebyshev_U24` | 3 | 3 | 1 -> 1 | 201.594 us | 208.124 us | -6.500 us | 600.790 us | 597.000 us | 0.999x |
| `legendre_P30` | 67 | 67 | 2 -> 2 | 7.128 ms | 7.109 ms | 61.952 us | 8.408 ms | 8.506 ms | 1.010x |
| `legendre_P38` | 79 | 79 | 1 -> 1 | 2.949 ms | 3.055 ms | -105.436 us | 3.789 ms | 3.811 ms | 1.001x |
| `cyclo_phi17` | 3 | 3 | 1 -> 1 | 57.360 us | 60.656 us | -3.245 us | 105.222 us | 108.681 us | 1.022x |
| `cyclo_phi41` | 3 | 3 | 1 -> 1 | 473.041 us | 482.640 us | -11.076 us | 1.984 ms | 2.035 ms | 1.028x |
| `xpow24_minus1` | 11 | 11 | 2 -> 2 | 1.088 ms | 1.106 ms | -15.573 us | 2.316 ms | 2.323 ms | 1.004x |
| `randprod_10` | 7 | 7 | 1 -> 1 | 353.880 us | 361.656 us | -7.737 us | 631.626 us | 636.168 us | 1.018x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 938.041 us | 946.688 us | -15.352 us | 1.408 ms | 1.431 ms | 1.021x |
| **aggregate** | | | | | | 24.351 ms | 938.307 ms | 917.954 ms | **0.9783x** |

Load control (23 instances whose plan does not change, named by --changed): 0.991x to 1.034x.

Both control bands sit slightly above 1.0 (1.000x to 1.028x and 0.991x to
1.034x, medians near 1.01x). Counterbalancing removes ordering as the
explanation, so a small real cost on rows the change does not help cannot be
ruled out; it is at most a few percent and every changed row is 0.41x to 0.80x.

## Full corpus

Both arms of the whole corpus, two counterbalanced blocks, ten-second per-call
cutoff, early termination disabled, per-instance medians of within-block ratios.

| | value |
|---|---|
| solved in every block, before | 377 of 392 |
| solved in every block, after | 377 of 392 |
| instances lost | none |
| instances gained | none |
| instances priced in every block | 377 |
| median per-row ratio | 1.0349x |
| summed medians | 17.852 s to 17.389 s (0.9741x) |
| instances above 1.10x costing over 2 ms | none |

Coverage is a set difference, not a count: it is the same 377 instances in both
arms. The median row is 3.5% slower while the aggregate improves, and the rows
carrying that median are all under 2 ms, where a row's time is dominated by
protocol and startup rather than by planning. The one instance above 1.05x costing
more than 1 ms is `laguerre_L22`, 0.968 ms to 1.017 ms, 1.050x with a block spread
of 1.030x to 1.071x.

### Combined-cactus elbow

Cumulative time over the 160-instance combined mixture, both arms, independently
sorted as the figures plot it, medians across blocks. Both arms solve 145 of 160
in every block.

| rank | cumulative before | cumulative after | ratio |
|---:|---:|---:|---:|
| 118 | 84.4 ms | 80.9 ms | 0.9582x |
| 122 | 114.7 ms | 108.4 ms | 0.9447x |
| 126 | 173.6 ms | 167.2 ms | 0.9634x |
| 130 | 290.8 ms | 268.0 ms | 0.9217x |
| 134 | 504.2 ms | 473.0 ms | 0.9381x |
| 138 | 857.4 ms | 827.1 ms | 0.9646x |
| 140 | 1150.7 ms | 1119.0 ms | 0.9724x |
| 142 | 2478.5 ms | 2427.5 ms | 0.9794x |
| 144 | 8553.4 ms | 8422.8 ms | 0.9847x |
| 145 | 16710.7 ms | 16461.2 ms | 0.9851x |

The elbow improves at every rank, by 0.922x to 0.985x, with coverage unchanged.

## Proof surface

`scoutPays` is a `Bool` on `Nat` shape data; it decides which plan the walk holds
and nothing else. `DirectPrimePlan` is unchanged, and both facts about it are
unchanged and still proved:

- `directPrimePlan?_selected_spec` -- the selected cached value is exactly the
  result of its retained explicit prime trial;
- `directPrimePlan?_selected_p_le_500` -- the planner selects only from the fixed
  hot-path candidate list.

Their proofs got shorter: the width gate was a second branch in
`firstDirectPlan?`, and removing it removed a case from each induction.
`scoutBetterPattern_mem` gained the one branch where the walk stops without
scouting. The Mathlib layer needed no change -- it consumes exactly those two
theorems -- and `HexBerlekampZassenhausMathlib` builds green.

Capping the recombination estimate needed `defaultSubsetBudget` visible to both
the engine that spends it and the planner that prices it. `Classical.Search` is
downstream of `Modular.PrimePlan` through `Hensel.DirectLift`, so the constant
moved up to `FactorizationResult`, where `precisionForCoeffBound` already lives.

`conformance/HexBerlekampZassenhaus/Conformance.lean` pins both directions of the
decision, the modulus width it reads, and the budget cap: one modular factor never
pays, four factors reaching degree 16 never pay, sixteen factors of degree at most
two do, `liftWords` of the Legendre input at 3 is one machine word, and the
subset count is the complete head-forced one at width 10 and the budget at width
20.

## Acceptance criteria

**Reduces prime-walk time by at least 20% and total time by at least 10% on
`cyclo_phi64_x_phi105`.** Prime walk 37.321 ms to 10.649 ms, **-71.5%**. Total
45.262 ms to 18.781 ms, **-58.5%**. Paired, four counterbalanced blocks, against
a load control of 1.000x to 1.028x.

**Preserves the order-of-magnitude scouting benefit on `xpow105_minus1`.** It
selects prime 17 at width 14 with two splits, exactly as before, at 1.004x paired.
Its first prime is worth 389 ms of attainable saving for a 17 ms observation, and
the `first` control prices what losing the scout would cost: 416.045 ms against
44.231 ms, 9.4x.

**Does not materially regress the full corpus or reduce solved coverage.** The
same 377 of 392 instances in both arms of every block, none lost or gained; no
instance above 1.10x costs more than 2 ms; summed medians 0.9741x.

**Improves, or at least does not regress, the combined-cactus elbow.** The
cumulative curve improves at every rank from 118 to 145, by 0.922x to 0.985x,
with coverage unchanged at 145 of 160.

**Passes a fresh all-systems performance sweep and regenerates every cactus plot
in the same PR.** `scripts/bench/check_factor_sweep_freshness.py` reports
"factorization performance data covers the current corpus and source"; the Hex
sweep is fresh at this revision from a clean tree and the external comparator
records are reused unchanged. All 25 figures are regenerated and
`scripts/plots/hexbz-cactus.py --check` passes byte for byte.

**Deterministic and shape-based, no family recognizer.** `scoutPays` reads the
degree of the input, the primes involved, and the degree multisets already
observed. There is no benchmark name, corpus identity, or family recognizer in the
planner, and the policy is unchanged over a 3x range of both constants.

**Existing `DirectPrimePlan` facts and retained-prime certificates remain
proved.** Recorded under "Proof surface" above.

## What this does not establish

Worth stating plainly, because the acceptance criteria do not ask for it and the
numbers above do not supply it:

- The rule is an affordability gate, not a value-of-information calculation. It
  compares an upper bound on benefit against an upper bound on contingent cost.
  A marginal-value rule would price one scout with the split and any further
  scout as contingent outcomes, and that needs an outcome model this does not
  have.
- The scout-depth proxy has no bound behind it, and its error runs toward
  under-pricing the scouts most likely to help.
- The robustness sweep is in-sample. Family-held-out validation would be a
  stronger claim and is not made.
- The counterfactual downstream prices the direct route only. Every changed row
  answers directly, so the seven confirmations stand, but the rule is not
  validated on a plan whose search declines into the lattice or trial tiers.

## Follow-up

`powModMonicAux` remains the cost of a bounded scout, and after this change it is
charged only where the rule has priced a scout as affordable. On the rows where it
now declines the scouts are gone entirely: `cyclo_phi105_x_phi128` no longer pays
108 ms for a complete pattern it cannot use. Where it still scouts, the
equal-width families are where the observation is cheap but ex post worthless, and
the cause is the reducibility question above, not a kernel cost. Per the issue's
last dependency note, any kernel work on `powModMonicAux` belongs in a separate
issue opened from the post-change profile.

## Regeneration

```sh
lake build hexbz_factor_service

# Two arms differing only in the planner and the diagnostic service entries.
git checkout <before> -- HexBerlekampZassenhaus/Modular/PrimePlan.lean \
  HexBerlekampZassenhaus/FactorizationResult.lean \
  HexBerlekampZassenhaus/Classical/Search.lean \
  bench/HexBench/FactorService.lean
lake build hexbz_factor_service && cp .lake/build/bin/hexbz_factor_service /tmp/svc.before
git checkout HEAD -- HexBerlekampZassenhaus bench/HexBench/FactorService.lean
lake build hexbz_factor_service && cp .lake/build/bin/hexbz_factor_service /tmp/svc.after

CPU="$(python3 scripts/bench/idle_core.py)"

# Paired, counterbalanced: the representative set, then the changed rows.
python3 scripts/bench/prime_plan_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --rounds 4 --cpu "$CPU" \
  --changed cyclo_phi64_x_phi105 \
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-803ffa18-chungus2.json
python3 scripts/bench/prime_plan_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --rounds 4 --cpu "$CPU" \
  --names cyclo_phi105_x_phi128,cyclo_phi64_x_phi105,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275,sd4_x_sd4shift1,xpow105_minus1,cyclo_phi179,legendre_P30,wilkinson_40,randprod_21 \
  --changed cyclo_phi105_x_phi128,cyclo_phi64_x_phi105,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275 \
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-changed-803ffa18-chungus2.json

# The durable cross-system record needs a clean tree: the freshness check
# rejects a record whose `git_dirty` is true. Write outside the repo, install
# after.
taskset -c "$CPU" python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate --output /tmp/sweep.json

# The corpus before/after comparison, counterbalanced.
python3 scripts/bench/factor_sweep_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --blocks 2 --cpu "$CPU" \
  --output reports/bench-results/hexbz-prime-plan-corpus-paired-803ffa18-chungus2.json

# Per-candidate scout prices, counterfactual downstream, kernel attribution.
python3 scripts/bench/factor_phase_profile.py --cpu "$CPU" --output /tmp/profile.json
python3 scripts/bench/factor_phase_profile.py --cpu "$CPU" --no-kernel \
  --validate-names cyclo_phi17 \
  --names cyclo_phi105_x_phi128,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275,cyclo_phi64_x_phi105 \
  --output /tmp/profile-changed.json

# Offline policy replay, per-decision margins, ratio sensitivity over both
# records, and the replay's own check against the measured binary.
python3 scripts/bench/prime_policy_replay.py \
  reports/bench-results/hexbz-phase-profile-803ffa18-chungus2.json \
  --also reports/bench-results/hexbz-phase-profile-changed-rows-803ffa18-chungus2.json \
  --margins --sensitivity --agrees-with voi

# Rank tables and figures, and the byte-for-byte check CI runs.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
python3 scripts/bench/check_factor_sweep_freshness.py
```
