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
| `cyclo_phi105_x_phi128` | 11 -> 11 | 1 -> 1 | 50.200 ms | 86.481 ms | 35.409 ms | 0.409x | 0.408x to 0.410x |
| `cyclo_phi64_x_phi105` | 11 -> 11 | 1 -> 1 | 27.119 ms | 45.381 ms | 18.805 ms | 0.414x | 0.410x to 0.418x |
| `sd4_x_phi17` | 11 -> 11 | 1 -> 1 | 3.764 ms | 6.648 ms | 2.930 ms | 0.441x | 0.440x to 0.442x |
| `legendre_P18` | 41 -> 37 | 2 -> 1 | 1.294 ms | 2.217 ms | 1.325 ms | 0.598x | 0.595x to 0.600x |
| `legendre_P20` | 43 -> 41 | 2 -> 1 | 1.880 ms | 2.854 ms | 1.904 ms | 0.667x | 0.662x to 0.673x |
| `cyclo_phi24_x_phi35` | 17 -> 13 | 2 -> 2 | 3.438 ms | 8.935 ms | 6.730 ms | 0.753x | 0.740x to 0.767x |
| `cyclo_phi275` | 13 -> 3 | 2 -> 1 | 164.496 ms | 816.464 ms | 646.373 ms | 0.792x | 0.788x to 0.795x |

Solved coverage is identical instance for instance -- the same 377 of 392 in
every block of both arms -- no instance above 1.10x costs more than 2 ms, and the
combined-cactus cumulative curve improves at every rank in the elbow band. The
mandatory `xpow105_minus1` control keeps its plan exactly, and with it an order
of magnitude.

**And every one of the eight decisions the walk takes on those seven rows is
confirmed by measurement.** For
each, the best *attainable* net gain -- the incumbent's measured downstream less
the cheapest downstream any candidate still reachable within the remaining fuel
offers, less every scout and split needed to reach it -- is negative. The rule
declined seven observations that could not have paid, and declined none that
could.

## Revision and protocol

Source revision `6f446862`, rebased onto `747d36ed`, toolchain `leanprover/lean4:v4.33.0-rc1`,
host `chungus2` (96 cores, x86_64, linux), clean worktree. Corpus
`bench/corpus/hexbz-factor-corpus.jsonl` (392 instances), sha256
`619913904240`.

The host was shared with other measurement work throughout, and that is not a
detail: a first attempt at the corpus comparison used one sweep pass per arm and
reported the long Swinnerton-Dyer rows at 1.25x to 1.31x, which the paired driver
put inside its control band at the same revision. Every timing below is therefore
paired and counterbalanced.

The branch was also rebased onto `747d36ed`, which speeds up completely split
finite-field inputs, part-way through. Every number here is measured after that
rebase, with the before arm built from `747d36ed` itself, so the comparison
isolates this change. Its effect is visible in the controls -- `wilkinson_40`'s
prime walk is 0.92 ms where it was 4.1 ms before the rebase, in both arms.

The durable sweep record is from a clean tree, which the freshness check
requires. The diagnostic phase-profile records were written while report text was
being edited; that touches no measured code, but their `git_dirty` flag is true
and is not claimed otherwise.

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

- `reports/bench-results/hexbz-factor-sweep-6f446862-hex-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-corpus-paired-6f446862-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-6f446862-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-changed-rows-6f446862-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-pricing-paired-6f446862-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-pricing-paired-changed-6f446862-chungus2.json`

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
| bounded scout | `d · bitLen p · n^2` | 20.80 ns | 1.37 to 79.25 | 144 |
| Berlekamp split | `bitLen p · n^3` | 6.87 ns | 0.17 to 28.68 | 144 |
| recombination candidate | `n^2 · W` per visited node | 1.56 ns | 0.25 to 31.76 | 52 |

That puts the ratios at 13.3 and 4.4. Four records of the same source taken the
same day under different load, and across a rebase onto a finite-field
performance change, put them at 10.2 and 5.2, 12.9 and 4.3, 13.4 and 4.4, and
13.3 and 4.4. These are medians of noisy, heterogeneous per-candidate prices, so the
shipped `scoutRoundCost = 10` and `splitColumnCost = 5` are not precise and are
not claimed to be.

What is claimed instead is that the policy does not balance on them:

> 113 of 120 ratio pairs over `scoutRoundCost` 6 to 20 and `splitColumnCost` 2 to
> 9 reproduce the shipped pair's whole replayed walk -- selected prime, splits
> and scouts -- on every one of the 30 recorded instances.

| scoutRoundCost | splitColumnCost | rows that move | regret |
|---:|---:|---|---:|
| 6 | 2 | `cyclo_phi24_x_phi35`, `cyclo_phi275`, `legendre_P20` | +127.470 ms |
| 6 | 3 | `legendre_P20` | +903.267 us |
| 7 | 2 | `cyclo_phi24_x_phi35`, `cyclo_phi275`, `legendre_P20` | +127.470 ms |
| 8 | 2 | `cyclo_phi24_x_phi35`, `legendre_P20` | +3.215 ms |
| 9 | 2 | `cyclo_phi24_x_phi35`, `legendre_P20` | +3.215 ms |
| 10 | 2 | `legendre_P20` | +903.267 us |
| 11 | 2 | `legendre_P20` | +903.267 us |

Every exception sits at `splitColumnCost` 2 or 3, at or below the smallest
measured value of 4.3, and every one is *worse* than the shipped pair.
`legendre_P20` is the tightest row in the corpus, 512 against 840. This is
in-sample
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
| `cyclo_phi105_x_phi128` | 1 | 11 | 10 | 32 | 2 | 13 | 1024 | 4800 | no | 12.359ms | none | yes |
| `sd4_x_phi17` | 1 | 11 | 9 | 16 | 2 | 13 | 256 | 1920 | no | 1.268ms | none | yes |
| `legendre_P18` | 1 | 37 | 9 | 2 | 2 | 41 | 256 | 780 | no | 579.979us | none | yes |
| `legendre_P20` | 1 | 41 | 10 | 2 | 2 | 43 | 512 | 840 | no | 1.029ms | none | yes |
| `cyclo_phi24_x_phi35` | 1 | 11 | 12 | 3 | 2 | 13 | 2048 | 880 | yes | 15.622ms | 10.994ms at 13 | yes |
| `cyclo_phi24_x_phi35` | 2 | 13 | 10 | 4 | 1 | 17 | 512 | 1000 | no | 1.963ms | none | yes |
| `cyclo_phi275` | 1 | 3 | 10 | 20 | 2 | 5 | 2048 | 4200 | no | 613.523ms | none | yes |
| `cyclo_phi64_x_phi105` | 1 | 11 | 10 | 16 | 2 | 13 | 1024 | 2880 | no | 7.567ms | none | yes |

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
| `sd5` | 1 | 19 | 16 | 2 | 2 | 23 | 65536 | 1000 | yes | 64.665ms | none | **no** |
| `sd5` | 2 | 23 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 64.305ms | none | **no** |
| `sd5_shift1` | 1 | 19 | 16 | 2 | 2 | 23 | 65536 | 1000 | yes | 59.048ms | none | **no** |
| `sd5_shift1` | 2 | 23 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 58.800ms | none | **no** |
| `sd5_shift2` | 1 | 19 | 16 | 2 | 2 | 23 | 65536 | 1000 | yes | 60.066ms | none | **no** |
| `sd5_shift2` | 2 | 23 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 60.495ms | none | **no** |
| `sd4_x_sd4shift1` | 1 | 13 | 16 | 2 | 2 | 17 | 65536 | 1000 | yes | 10.811ms | none | **no** |
| `sd4_x_sd4shift1` | 2 | 17 | 16 | 2 | 1 | 19 | 65536 | 900 | yes | 10.867ms | none | **no** |
| `sd4_x_sd4shift1` | 3 | 17 | 16 | 2 | 1 | 23 | 65536 | 900 | yes | 10.867ms | none | **no** |
| `sd4_x_sd4shift1` | 4 | 17 | 16 | 2 | 1 | 29 | 65536 | 900 | yes | 10.867ms | none | **no** |
| `sd5_x_phi11` | 1 | 19 | 17 | 10 | 2 | 23 | 131072 | 2050 | yes | 138.538ms | none | **no** |
| `sd5_x_phi11` | 2 | 19 | 17 | 10 | 1 | 29 | 131072 | 1550 | yes | 138.538ms | none | **no** |
| `xpow48_minus1` | 1 | 5 | 20 | 4 | 2 | 7 | 262144 | 960 | yes | 5.247ms | none | **no** |
| `xpow48_minus1` | 2 | 5 | 20 | 4 | 1 | 11 | 262144 | 1120 | yes | 5.247ms | none | **no** |
| `xpow105_minus1` | 1 | 11 | 30 | 6 | 2 | 13 | 524288 | 2580 | yes | 409.051ms | 376.136ms at 17 | yes |
| `xpow105_minus1` | 2 | 11 | 30 | 6 | 1 | 17 | 524288 | 2925 | yes | 409.051ms | 378.553ms at 17 | yes |
| `xpow120_minus1` | 1 | 7 | 39 | 4 | 2 | 11 | 524288 | 2720 | yes | 128.680ms | none | **no** |
| `xpow120_minus1` | 2 | 7 | 39 | 4 | 1 | 13 | 524288 | 2560 | yes | 128.680ms | none | **no** |
| `cyclo_phi179` | 1 | 3 | 2 | 89 | 2 | 5 | 6 | 8010 | no | 28.511ms | -- | -- |
| `cyclo_phi64_x_phi105` | 1 | 11 | 10 | 16 | 2 | 13 | 1024 | 2880 | no | 7.704ms | none | yes |
| `cyclo_phi128_x_phi165` | 1 | 7 | 8 | 20 | 2 | 11 | 384 | 4480 | no | 39.786ms | -- | -- |
| `cyclo_phi385` | 1 | 3 | 4 | 60 | 2 | 5 | 32 | 7200 | no | 85.512ms | -- | -- |
| `wilkinson_40` | 1 | 41 | 40 | 1 | 2 | 43 | 1048576 | 1320 | yes | 7.146ms | none | **no** |
| `wilkinson_40` | 2 | 41 | 40 | 1 | 1 | 47 | 1048576 | 1260 | yes | 7.146ms | none | **no** |
| `wilkinson_48` | 1 | 53 | 48 | 1 | 2 | 59 | 1310720 | 1560 | yes | 13.122ms | none | **no** |
| `wilkinson_48` | 2 | 59 | 48 | 1 | 1 | 61 | 1310720 | 1500 | yes | 13.146ms | none | **no** |
| `wilkinson_56` | 1 | 59 | 56 | 1 | 2 | 61 | 1310720 | 1800 | yes | 16.717ms | none | **no** |
| `wilkinson_56` | 2 | 61 | 56 | 1 | 1 | 67 | 1310720 | 2030 | yes | 16.685ms | none | **no** |
| `chebyshev_T24` | 1 | 5 | 3 | 8 | 2 | 7 | 4 | 840 | no | 146.618us | -- | -- |
| `chebyshev_U24` | 1 | 3 | 4 | 10 | 2 | 5 | 8 | 960 | no | 310.470us | -- | -- |
| `legendre_P30` | 1 | 61 | 15 | 2 | 2 | 67 | 32768 | 1330 | yes | 29.881ms | 24.489ms at 67 | yes |
| `legendre_P30` | 2 | 67 | 7 | 14 | 1 | 71 | 128 | 2030 | no | 1.211ms | none | yes |
| `legendre_P38` | 1 | 79 | 3 | 36 | 2 | 83 | 8 | 6370 | no | 630.935us | -- | -- |
| `cyclo_phi17` | 1 | 3 | 1 | 16 | 2 | 5 | 1 | 1200 | no | 8.744us | -- | -- |
| `cyclo_phi41` | 1 | 3 | 5 | 8 | 2 | 5 | 16 | 1080 | no | 1.473ms | -- | -- |
| `xpow24_minus1` | 1 | 5 | 14 | 2 | 2 | 7 | 8192 | 480 | yes | 941.556us | 69.574us at 7 | yes |
| `xpow24_minus1` | 2 | 5 | 14 | 2 | 1 | 11 | 8192 | 560 | yes | 941.556us | none | **no** |
| `randprod_10` | 1 | 7 | 4 | 7 | 2 | 11 | 8 | 960 | no | 201.738us | -- | -- |
| `randprod_21` | 1 | 17 | 7 | 9 | 2 | 19 | 64 | 1500 | no | 370.790us | -- | -- |

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
| `sd5` | 67.150ms | 73.200ms | 73.177ms | 73.200ms | 71.234ms | 71.234ms | 69.494ms | 67.027ms | 19/29/29/29/23 |
| `sd5_shift1` | 61.775ms | 67.777ms | 67.732ms | 67.777ms | 65.982ms | 65.982ms | 64.296ms | 61.602ms | 19/29/29/29/23 |
| `sd5_shift2` | 62.841ms | 71.609ms | 71.053ms | 71.609ms | 69.081ms | 69.081ms | 62.841ms | 62.841ms | 19/29/29/29/19 |
| `sd4_x_sd4shift1` | 12.635ms | 19.067ms | 18.824ms | 19.067ms | 17.638ms | 17.638ms | 12.635ms | 12.635ms | 13/29/29/29/13 |
| `sd5_x_phi11` | 143.094ms | 147.301ms | 156.463ms | 147.301ms | 145.548ms | 145.548ms | 141.754ms | 137.249ms | 19/29/29/29/29 |
| `xpow48_minus1` | 6.656ms | 12.102ms | 12.102ms | 12.102ms | 10.385ms | 10.385ms | 6.656ms | 6.656ms | 5/11/11/11/5 |
| `xpow105_minus1` | 421.003ms | 51.282ms | 51.282ms | 51.282ms | 44.890ms | 44.890ms | 36.173ms | 24.232ms | 11/17/17/17/17 |
| `xpow120_minus1` | 144.903ms | 191.009ms | 191.009ms | 701.531ms | 147.298ms | 147.298ms | 144.903ms | 144.903ms | 7/7/7/7/7 |
| `cyclo_phi179` | 35.108ms | 35.108ms | 35.108ms | 35.108ms | 35.108ms | 35.108ms | 35.108ms | 35.108ms | 3/3/3/3/3 |
| `cyclo_phi64_x_phi105` | 18.315ms | 48.327ms | 48.327ms | 76.623ms | 45.318ms | 18.315ms | 18.315ms | 18.315ms | 11/11/11/11/11 |
| `cyclo_phi128_x_phi165` | 74.864ms | 74.864ms | 74.864ms | 74.864ms | 74.864ms | 74.864ms | 74.864ms | 74.864ms | 7/7/7/7/7 |
| `cyclo_phi385` | 144.427ms | 144.427ms | 144.427ms | 144.427ms | 144.427ms | 144.427ms | 144.427ms | 144.427ms | 3/3/3/3/3 |
| `wilkinson_40` | 7.245ms | 7.521ms | 7.479ms | 7.521ms | 7.584ms | 7.584ms | 7.346ms | 7.254ms | 41/47/47/47/43 |
| `wilkinson_48` | 13.284ms | 13.530ms | 13.673ms | 13.530ms | 13.616ms | 13.616ms | 13.374ms | 13.233ms | 53/61/61/61/61 |
| `wilkinson_56` | 16.925ms | 17.573ms | 17.396ms | 17.573ms | 17.733ms | 17.733ms | 17.111ms | 16.923ms | 59/67/67/67/61 |
| `chebyshev_T24` | 358.302us | 358.302us | 358.302us | 358.302us | 358.302us | 358.302us | 358.302us | 358.302us | 5/5/5/5/5 |
| `chebyshev_U24` | 514.662us | 514.662us | 514.662us | 514.662us | 514.662us | 514.662us | 514.662us | 514.662us | 3/3/3/3/3 |
| `legendre_P30` | 32.890ms | 7.262ms | 7.262ms | 7.262ms | 8.421ms | 8.421ms | 5.256ms | 2.265ms | 61/71/67/67/71 |
| `legendre_P38` | 3.556ms | 3.556ms | 3.556ms | 3.556ms | 3.556ms | 3.556ms | 3.556ms | 3.556ms | 79/79/79/79/79 |
| `cyclo_phi17` | 62.885us | 62.885us | 62.885us | 62.885us | 62.885us | 62.885us | 62.885us | 62.885us | 3/3/3/3/3 |
| `cyclo_phi41` | 1.939ms | 1.939ms | 1.939ms | 1.939ms | 1.939ms | 1.939ms | 1.939ms | 1.939ms | 3/3/3/3/3 |
| `xpow24_minus1` | 1.302ms | 2.474ms | 2.474ms | 2.474ms | 2.219ms | 2.219ms | 1.204ms | 846.836us | 5/11/11/11/7 |
| `randprod_10` | 553.549us | 553.549us | 553.549us | 553.549us | 553.549us | 553.549us | 553.549us | 553.549us | 7/7/7/7/7 |
| `randprod_21` | 1.261ms | 1.261ms | 1.261ms | 1.261ms | 1.261ms | 1.261ms | 1.261ms | 1.261ms | 17/17/17/17/17 |
| **aggregate** | **1.273s** | **992.678ms** | **1.001s** | **1.531s** | **929.590ms** | **902.587ms** | **864.000ms** | **838.625ms** | |

The four policies the issue asks to be controlled against all fail, each in its
own way:

* **first** -- stopping at the first acceptable prime is unusable at 1.273 s.
  `xpow105_minus1` alone is 415.564 ms of that against 43.949 ms, and
  `legendre_P30` is 31.867 ms against 8.045 ms. This is why a scout-nothing rule
  is not on the table, and why `xpow105_minus1` is a mandatory control.
* **minwidth** -- a degree cost model on its own is worse than the score at
  1.001 s. `sd5_x_phi11` is where it shows: prime 23 is widest, and prime 29 wins
  only on the tie breaks the score already carries.
* **maxfield** -- a field-size cost model on its own is the worst of all at
  1.531 s. It picks the largest prime for its smaller Hensel precision and pays
  in recombination: `xpow120_minus1` goes from 146 ms to 697 ms.
* **fixed** -- the pre-scout rule, 992.678 ms. The scout replaced it in #9128.

On this 24-instance set `voi` saves 27.003 ms of 929.590 ms and closes 41.2% of
the distance from `scout` to the `reachable` floor. Over the seven changed rows
the separate record covers, it saves 255.350 ms of 960.779 ms and closes 99.7% of
that distance -- there is essentially nothing left on those rows for a discovering
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
| `cyclo_phi105_x_phi128` | 11 | 11 | 1 -> 1 | 72.107 ms | 21.834 ms | 50.200 ms | 86.294 ms | 35.342 ms | 0.409x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 1 -> 1 | 37.811 ms | 10.674 ms | 27.119 ms | 45.424 ms | 18.611 ms | 0.409x |
| `sd4_x_phi17` | 11 | 11 | 1 -> 1 | 5.296 ms | 1.512 ms | 3.764 ms | 6.638 ms | 2.898 ms | 0.438x |
| `legendre_P18` | 41 | 37 | 2 -> 1 | 1.995 ms | 696.153 us | 1.294 ms | 2.185 ms | 1.311 ms | 0.601x |
| `legendre_P20` | 43 | 41 | 2 -> 1 | 2.726 ms | 836.080 us | 1.880 ms | 2.815 ms | 1.892 ms | 0.668x |
| `cyclo_phi24_x_phi35` | 17 | 13 | 2 -> 2 | 8.076 ms | 4.608 ms | 3.438 ms | 9.001 ms | 6.684 ms | 0.747x |
| `cyclo_phi275` | 13 | 3 | 2 -> 1 | 190.950 ms | 26.564 ms | 164.496 ms | 814.394 ms | 639.391 ms | 0.783x |
| `sd4_x_sd4shift1` | 29 | 29 | 2 -> 2 | 6.872 ms | 6.945 ms | -92.912 us | 17.812 ms | 17.737 ms | 1.000x |
| `xpow105_minus1` | 17 | 17 | 2 -> 2 | 29.372 ms | 29.403 ms | -38.657 us | 44.958 ms | 44.834 ms | 0.997x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 6.441 ms | 6.621 ms | -196.962 us | 35.266 ms | 34.860 ms | 0.986x |
| `legendre_P30` | 67 | 67 | 2 -> 2 | 7.090 ms | 7.097 ms | -35.623 us | 8.572 ms | 8.431 ms | 0.985x |
| `wilkinson_40` | 47 | 47 | 2 -> 2 | 922.778 us | 1.007 ms | -86.028 us | 9.135 ms | 9.164 ms | 1.002x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 938.496 us | 950.354 us | -8.332 us | 1.403 ms | 1.406 ms | 1.003x |
| **aggregate** | | | | | | 251.733 ms | 1.084 s | 822.560 ms | **0.7589x** |

Load control (6 instances whose plan does not change, named by --changed): 0.985x to 1.003x.

`cyclo_phi275` is the largest absolute win: 164.496 ms of prime walk, because the
fixed rule scouted two further primes at 65 ms and 45 ms apiece and then split one
of them, all to select a prime whose downstream is 2 ms *worse* than the one it
started with.

### The issue #9127 representative set

The same protocol over the elbow set, where `cyclo_phi64_x_phi105` is the only
changed row. This is the table the acceptance threshold is read from.

### Paired before/after, median of 4 counterbalanced blocks (AB/BA/AB/BA)

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 29 | 2 -> 2 | 6.574 ms | 6.701 ms | -128.836 us | 68.709 ms | 68.262 ms | 0.993x |
| `sd5_shift1` | 29 | 29 | 2 -> 2 | 7.062 ms | 7.097 ms | -55.246 us | 63.289 ms | 63.129 ms | 0.997x |
| `sd5_shift2` | 29 | 29 | 2 -> 2 | 8.621 ms | 8.730 ms | -102.543 us | 66.706 ms | 66.742 ms | 0.999x |
| `sd4_x_sd4shift1` | 29 | 29 | 2 -> 2 | 6.810 ms | 6.897 ms | -84.355 us | 17.666 ms | 17.813 ms | 1.007x |
| `sd5_x_phi11` | 29 | 29 | 2 -> 2 | 16.279 ms | 16.412 ms | -72.817 us | 138.434 ms | 139.078 ms | 1.004x |
| `xpow48_minus1` | 11 | 11 | 2 -> 2 | 3.972 ms | 3.952 ms | 7.436 us | 10.390 ms | 10.440 ms | 1.005x |
| `xpow105_minus1` | 17 | 17 | 2 -> 2 | 29.549 ms | 29.433 ms | 121.611 us | 44.458 ms | 45.066 ms | 1.014x |
| `xpow120_minus1` | 7 | 7 | 1 -> 1 | 18.688 ms | 18.656 ms | 37.406 us | 145.838 ms | 147.145 ms | 1.008x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 6.469 ms | 6.574 ms | -104.049 us | 34.640 ms | 34.972 ms | 1.011x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 1 -> 1 | 37.475 ms | 10.647 ms | 26.827 ms | 45.177 ms | 18.841 ms | 0.416x |
| `cyclo_phi128_x_phi165` | 7 | 7 | 1 -> 1 | 34.400 ms | 34.857 ms | -456.532 us | 75.179 ms | 75.499 ms | 1.007x |
| `cyclo_phi385` | 3 | 3 | 1 -> 1 | 58.601 ms | 58.880 ms | -364.070 us | 142.849 ms | 143.775 ms | 1.008x |
| `wilkinson_40` | 47 | 47 | 2 -> 2 | 921.191 us | 1.009 ms | -90.430 us | 9.080 ms | 9.176 ms | 1.012x |
| `wilkinson_48` | 61 | 61 | 2 -> 2 | 1.428 ms | 1.546 ms | -116.573 us | 15.883 ms | 16.243 ms | 1.019x |
| `wilkinson_56` | 67 | 67 | 2 -> 2 | 1.870 ms | 2.003 ms | -133.848 us | 20.660 ms | 21.045 ms | 1.019x |
| `chebyshev_T24` | 5 | 5 | 1 -> 1 | 213.000 us | 218.799 us | -5.098 us | 431.775 us | 444.800 us | 1.029x |
| `chebyshev_U24` | 3 | 3 | 1 -> 1 | 201.508 us | 207.608 us | -7.016 us | 584.091 us | 595.273 us | 1.017x |
| `legendre_P30` | 67 | 67 | 2 -> 2 | 6.975 ms | 7.115 ms | -150.768 us | 8.378 ms | 8.612 ms | 1.024x |
| `legendre_P38` | 79 | 79 | 1 -> 1 | 3.009 ms | 3.030 ms | -21.832 us | 3.789 ms | 3.875 ms | 1.024x |
| `cyclo_phi17` | 3 | 3 | 1 -> 1 | 57.154 us | 60.275 us | -3.120 us | 102.472 us | 107.325 us | 1.054x |
| `cyclo_phi41` | 3 | 3 | 1 -> 1 | 471.870 us | 479.881 us | -5.734 us | 1.984 ms | 2.003 ms | 1.012x |
| `xpow24_minus1` | 11 | 11 | 2 -> 2 | 1.090 ms | 1.111 ms | -20.660 us | 2.288 ms | 2.325 ms | 1.013x |
| `randprod_10` | 7 | 7 | 1 -> 1 | 354.611 us | 362.182 us | -7.121 us | 625.212 us | 632.763 us | 1.012x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 939.543 us | 956.298 us | -14.101 us | 1.401 ms | 1.417 ms | 1.019x |
| **aggregate** | | | | | | 25.049 ms | 918.539 ms | 897.239 ms | **0.9768x** |

Load control (23 instances whose plan does not change, named by --changed): 0.993x to 1.054x.

The changed-row control band straddles 1.0 (0.985x to 1.003x); the
representative one sits slightly above (0.993x to 1.054x). Counterbalancing
removes ordering as the explanation, so a small real cost on rows the change
does not help cannot be ruled out from these numbers; it is at most a few
percent, and every changed row is 0.41x to 0.79x.

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
| median per-row ratio | 1.0202x |
| summed medians | 17.789 s to 17.502 s (0.9839x) |
| instances above 1.10x costing over 2 ms | none |

Coverage is a set difference, not a count: it is the same 377 instances in both
arms. The median row is 2.0% slower while the aggregate improves, and the rows carrying
that median are all under 2 ms, where a row's time is dominated by protocol and
startup rather than by planning.

### Combined-cactus elbow

Cumulative time over the 160-instance combined mixture, both arms, independently
sorted as the figures plot it, medians across blocks. Both arms solve 145 of 160
in every block.

| rank | cumulative before | cumulative after | ratio |
|---:|---:|---:|---:|
| 118 | 83.9 ms | 80.8 ms | 0.9626x |
| 122 | 113.2 ms | 106.8 ms | 0.9442x |
| 126 | 166.8 ms | 160.9 ms | 0.9646x |
| 130 | 272.1 ms | 250.1 ms | 0.9190x |
| 134 | 486.9 ms | 455.1 ms | 0.9348x |
| 138 | 840.4 ms | 811.0 ms | 0.9650x |
| 140 | 1133.3 ms | 1102.2 ms | 0.9725x |
| 142 | 2450.3 ms | 2408.3 ms | 0.9829x |
| 144 | 8434.1 ms | 8373.1 ms | 0.9928x |
| 145 | 16642.5 ms | 16574.6 ms | 0.9959x |

The elbow improves at every rank, by 0.919x to 0.996x, with coverage unchanged
at 145 of 160 in every block of both arms.

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
`cyclo_phi64_x_phi105`.** Prime walk 37.811 ms to 10.674 ms, **-71.8%**. Total
45.424 ms to 18.611 ms, **-59.0%**. Paired, four counterbalanced blocks, against
a load control of 0.985x to 1.003x.

**Preserves the order-of-magnitude scouting benefit on `xpow105_minus1`.** It
selects prime 17 at width 14 with two splits, exactly as before, at 0.997x paired.
The `first` control prices what losing the scout would cost: 415.564 ms against
43.949 ms, 9.5x.

**Does not materially regress the full corpus or reduce solved coverage.** The
same 377 of 392 instances in both arms of every block, none lost or gained; no
instance above 1.10x costs more than 2 ms; summed medians 0.9839x.

**Improves, or at least does not regress, the combined-cactus elbow.** The
cumulative curve improves at every rank from 118 to 145, by 0.919x to 0.996x,
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
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-6f446862-chungus2.json
python3 scripts/bench/prime_plan_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --rounds 4 --cpu "$CPU" \
  --names cyclo_phi105_x_phi128,cyclo_phi64_x_phi105,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275,sd4_x_sd4shift1,xpow105_minus1,cyclo_phi179,legendre_P30,wilkinson_40,randprod_21 \
  --changed cyclo_phi105_x_phi128,cyclo_phi64_x_phi105,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275 \
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-changed-6f446862-chungus2.json

# The durable cross-system record needs a clean tree: the freshness check
# rejects a record whose `git_dirty` is true. Write outside the repo, install
# after.
taskset -c "$CPU" python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate --output /tmp/sweep.json

# The corpus before/after comparison, counterbalanced.
python3 scripts/bench/factor_sweep_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --blocks 2 --cpu "$CPU" \
  --output reports/bench-results/hexbz-prime-plan-corpus-paired-6f446862-chungus2.json

# Per-candidate scout prices, counterfactual downstream, kernel attribution.
python3 scripts/bench/factor_phase_profile.py --cpu "$CPU" --output /tmp/profile.json
python3 scripts/bench/factor_phase_profile.py --cpu "$CPU" --no-kernel \
  --validate-names cyclo_phi17 \
  --names cyclo_phi105_x_phi128,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275,cyclo_phi64_x_phi105 \
  --output /tmp/profile-changed.json

# Offline policy replay, per-decision margins, ratio sensitivity over both
# records, and the replay's own check against the measured binary.
python3 scripts/bench/prime_policy_replay.py \
  reports/bench-results/hexbz-phase-profile-6f446862-chungus2.json \
  --also reports/bench-results/hexbz-phase-profile-changed-rows-6f446862-chungus2.json \
  --margins --sensitivity --agrees-with voi

# Rank tables and figures, and the byte-for-byte check CI runs.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
python3 scripts/bench/check_factor_sweep_freshness.py
```
