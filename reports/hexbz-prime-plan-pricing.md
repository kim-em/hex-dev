# Pricing one more modular observation (issue #9156)

The direct prime planner stopped shopping for a prime at a fixed width: an image
with at most eight local factors was used unexamined, and a wider one bought up
to two bounded scouts. Eight is a threshold, not a price. It cannot see that
`cyclo_phi64_x_phi105`'s first prime already costs 7.5 ms downstream while the
two scouts it triggers cost 27 ms, and that neither of the primes they find is
any better.

This report replaces that threshold with a price comparison. `Hex.scoutPays`
asks whether the plan in hand still has enough recombination work left to repay
another observation, estimating both sides from shape already observed. It is the
walk's only stopping decision: it governs the first good prime and every scouted
candidate alike, and nothing about the corpus, the instance, or its family enters
it.

The full corpus finds six instances whose walk the rule changes, and every one of
the six improves:

| instance | prime | full splits | prime walk | total before | total after | ratio |
|---|---|---:|---:|---:|---:|---:|
| `cyclo_phi105_x_phi128` | 11 -> 11 | 1 -> 1 | -49.625 ms | 86.349 ms | 35.378 ms | 0.410x |
| `cyclo_phi64_x_phi105` | 11 -> 11 | 1 -> 1 | -26.820 ms | 45.992 ms | 18.700 ms | 0.407x |
| `sd4_x_phi17` | 11 -> 11 | 1 -> 1 | -3.761 ms | 6.645 ms | 2.922 ms | 0.440x |
| `legendre_P18` | 41 -> 37 | 2 -> 1 | -1.290 ms | 2.181 ms | 1.315 ms | 0.603x |
| `cyclo_phi24_x_phi35` | 17 -> 13 | 2 -> 2 | -3.412 ms | 8.891 ms | 6.682 ms | 0.752x |
| `cyclo_phi275` | 13 -> 3 | 2 -> 1 | -163.223 ms | 806.894 ms | 637.863 ms | 0.791x |

No instance regresses beyond a paired load control of 0.989x to 1.049x, solved
coverage is identical at 377 of 392, and the combined-cactus cumulative curve
improves at every rank in the elbow band. The mandatory `xpow105_minus1` control
keeps its plan exactly, and with it an order of magnitude.

And the decision is confirmed where it matters most. On all six rows the rule
changed, the *attainable* saving -- the incumbent's measured downstream less the
cheapest downstream any other priced candidate offers -- is smaller than what the
observation measurably costs, or negative outright. The rule declined six
observations that could not have paid, and it did not decline a single one that
could.

## Revision and protocol

Source revision `9710df88`, toolchain `leanprover/lean4:v4.33.0-rc1`,
host `chungus2` (96 cores, x86_64, linux), clean worktree. Corpus
`bench/corpus/hexbz-factor-corpus.jsonl` (392 instances), sha256
`619913904240`.

The host was shared with other measurement work throughout, so absolute wall
times are not comparable with earlier reports. Four protocols make the
comparisons here safe anyway.

Every before/after timing comes from a **paired** run: two service binaries built
from this worktree, differing only in
`HexBerlekampZassenhaus/Modular/PrimePlan.lean` and in the diagnostic entries of
`bench/HexBench/FactorService.lean`, alternated on the same pinned core over
three rounds. The core is chosen by `scripts/bench/idle_core.py` and named
explicitly to both arms, so neither arm can drift onto a different core.

Every **corpus** comparison is likewise two arms of the same sweep, the same day
on the same core, with only the installed binary differing. The before arm is a
control and is not committed; the after arm is the record the figures are built
from.

Every per-candidate cost is the median of `--plan-repeats 3` calls of the same
service, merged field by field after asserting that the repeats agree on
everything deterministic.

Every **policy** comparison is an offline replay over those recorded
per-candidate costs, by `scripts/bench/prime_policy_replay.py`. No policy is
timed against another on the machine; they are priced against the same
observations, so the comparison cannot depend on what the host was doing when
each row was measured. The replay checks itself: `--agrees-with voi` confirms
that the replayed rule reproduces the prime the measured binary selected, on
24 of 24 rows.

### Artifacts

- `reports/bench-results/hexbz-factor-sweep-9710df88-hex-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-9710df88-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-changed-rows-9710df88-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-pricing-paired-9710df88-chungus2.json`
- `reports/bench-results/hexbz-prime-plan-pricing-paired-changed-9710df88-chungus2.json`

## The rule

Write `n` for the degree of the modular image, `q` for the prime about to be
scouted, `w` and `d` for the width and largest modular factor degree of the plan
currently held, `W` for the machine words of that plan's Hensel modulus, and
`fuel` for the observations the walk may still make.

**What is still on the table.** A recombination candidate multiplies a subset of
the lifted factors and trial-divides the result: about `n^2` coefficient
operations on `W`-word integers. A complete head-forced search visits
`directSubsetCost w = 2^(w-1)` candidates. So the plan's remaining recombination
is about `2^(w-1) · n^2 · W` word operations. That is an *upper* bound on what
another prime could save, and the bound is attained: an irreducible input runs
the search to exhaustion, and a reducible one stops earlier.

**What another observation costs.** A bounded scout runs about `d` rounds, since
the distinct-degree loop stops at the largest factor degree, and each round is
one Frobenius power, about `bitLen q` squarings of the degree-`n` image:
`d · bitLen q · n^2` word operations. Acting on what it learns costs a further
Berlekamp split, whose fixed-space matrix and row reduction are about
`bitLen q · n^3`. A walk with `fuel` observations left is committing to at most
`fuel` scouts and one split.

Both estimates carry a factor `n^2`, which cancels, leaving

```
2^(w-1) · W  >  bitLen q · (scoutRoundCost · fuel · d + splitColumnCost · n)
```

`scoutRoundCost` and `splitColumnCost` state what a scout and a split word
operation cost in recombination word operations.

### The two constants, and how little they matter

Dividing each measured cost by its model units, over the 144 priced candidates of
the committed per-candidate profile:

| word operation | model units | median | range | samples |
|---|---|---:|---|---:|
| bounded scout | `d · bitLen p · n^2` | 20.72 ns | 1.33 to 78.15 | 144 |
| Berlekamp split | `bitLen p · n^3` | 6.84 ns | 0.43 to 29.03 | 144 |
| recombination candidate | `n^2 · W` per visited node | 1.54 ns | 0.17 to 30.92 | 52 |

That puts the ratios at 13.4 and 4.4. A second record of the same source, taken
earlier the same day under different load, puts them at 10.2 and 5.2. The
per-candidate prices are noisy medians and the ratios inherit that, so the
shipped `scoutRoundCost = 10` and `splitColumnCost = 5` should not be read as
precise.

They do not need to be. Sweeping both:

> 120 of 120 ratio pairs over `scoutRoundCost` 6 to 20 and `splitColumnCost` 2 to
> 9 give the identical decision on every instance.

The recombination row above is calibrated against *measured* node counts rather
than `2^(w-1)`, because it prices one candidate; the model's use of `2^(w-1)` for
how many candidates there are is the separate, deliberately conservative step.

## Investigation

### The decision, against what it was worth

The first `scoutPays` call on each instance. `left` is `2^(w-1) · W`; `next obs`
is the right-hand side at the next candidate prime with `fuel = 2`. What settles
the decision is the last three columns: the *attainable saving* is the
incumbent's measured downstream less the cheapest measured downstream any other
priced candidate offers, and the observation cost is the measured bounded scout
plus full split at the next good prime. A decision is confirmed when the sign of
`saving - cost` agrees with it.

First, the six rows the rule changed:

| instance | n | p | w | max deg | W | left | next obs | scout? | own downstream | best other | attainable saving | observation cost | confirmed |
|---|---:|---:|---:|---:|---:|---:|---:|:--:|---:|---:|---:|---:|:--:|
| `cyclo_phi105_x_phi128` | 112 | 11 | 10 | 32 | 3 | 1536 | 4800 | no | 12.321ms | 74.411ms | none | 35.663ms | yes |
| `sd4_x_phi17` | 32 | 11 | 9 | 16 | 1 | 256 | 1920 | no | 1.255ms | 1.107ms | 148.599us | 3.071ms | yes |
| `legendre_P18` | 18 | 37 | 9 | 2 | 1 | 256 | 780 | no | 577.978us | 105.496us | 472.482us | 1.316ms | yes |
| `cyclo_phi24_x_phi35` | 32 | 11 | 12 | 3 | 1 | 2048 | 880 | yes | 15.405ms | 689.973us | 14.715ms | 2.630ms | yes |
| `cyclo_phi275` | 200 | 3 | 10 | 20 | 4 | 2048 | 4200 | no | 611.149ms | 613.442ms | none | 97.014ms | yes |
| `cyclo_phi64_x_phi105` | 80 | 11 | 10 | 16 | 2 | 1024 | 2880 | no | 7.496ms | 35.201ms | none | 18.825ms | yes |

**Six of six confirmed.** Three of them -- `cyclo_phi105_x_phi128`,
`cyclo_phi275`, `cyclo_phi64_x_phi105` -- have *no* better prime at all in the
comparison set, so the observation the fixed threshold bought could not have paid
at any price. `cyclo_phi275` is the clearest: all three priced candidates have
width 10 and largest factor degree 20, and their downstreams are 611.1, 639.2 and
613.4 ms. There is nothing there to find, and the rule declines to look.

`cyclo_phi24_x_phi35` is the row where the rule *keeps* scouting and moves the
prime, 17 to 13: its first prime costs 15.4 ms downstream against 0.7 ms at the
best alternative, so 14.7 ms is genuinely attainable for a 2.6 ms observation.
The decision is not a bias toward declining; it is a comparison.

Now the same table over the issue #9127 representative set and its controls:

| instance | n | p | w | max deg | W | left | next obs | scout? | own downstream | best other | attainable saving | observation cost | confirmed |
|---|---:|---:|---:|---:|---:|---:|---:|:--:|---:|---:|---:|---:|:--:|
| `sd5` | 32 | 19 | 16 | 2 | 2 | 65536 | 1000 | yes | 64.813ms | 64.668ms | 144.804us | 3.040ms | **no** |
| `sd5_shift1` | 32 | 19 | 16 | 2 | 2 | 65536 | 1000 | yes | 59.307ms | 59.038ms | 268.167us | 3.198ms | **no** |
| `sd5_shift2` | 32 | 19 | 16 | 2 | 2 | 65536 | 1000 | yes | 60.098ms | 60.219ms | none | 3.952ms | **no** |
| `sd4_x_sd4shift1` | 32 | 13 | 16 | 2 | 2 | 65536 | 1000 | yes | 10.876ms | 10.866ms | 10.056us | 2.509ms | **no** |
| `sd5_x_phi11` | 42 | 19 | 17 | 10 | 2 | 131072 | 2050 | yes | 137.753ms | 128.093ms | 9.660ms | 6.294ms | yes |
| `xpow48_minus1` | 48 | 5 | 20 | 4 | 1 | 524288 | 960 | yes | 5.179ms | 6.359ms | none | 2.323ms | **no** |
| `xpow105_minus1` | 105 | 11 | 30 | 6 | 2 | 1073741824 | 2580 | yes | 404.377ms | 15.090ms | 389.287ms | 17.086ms | yes |
| `xpow120_minus1` | 120 | 7 | 39 | 4 | 3 | 824633720832 | 2720 | yes | 127.937ms | 356.611ms | none | 30.460ms | **no** |
| `cyclo_phi179` | 178 | 3 | 2 | 89 | 4 | 8 | 8010 | no | 28.058ms | -- | -- | 131.476ms | -- |
| `cyclo_phi64_x_phi105` | 80 | 11 | 10 | 16 | 2 | 1024 | 2880 | no | 7.532ms | 35.607ms | none | 19.121ms | yes |
| `cyclo_phi128_x_phi165` | 144 | 7 | 8 | 20 | 3 | 384 | 4480 | no | 39.435ms | -- | -- | 240.385ms | -- |
| `cyclo_phi385` | 240 | 3 | 4 | 60 | 5 | 40 | 7200 | no | 83.891ms | -- | -- | 266.690ms | -- |
| `wilkinson_40` | 40 | 41 | 40 | 1 | 4 | 2199023255552 | 1320 | yes | 6.979ms | 6.957ms | 21.893us | 2.007ms | **no** |
| `wilkinson_48` | 48 | 53 | 48 | 1 | 5 | 703687441776640 | 1560 | yes | 12.854ms | 12.866ms | none | 3.242ms | **no** |
| `wilkinson_56` | 56 | 59 | 56 | 1 | 5 | 180143985094819840 | 1800 | yes | 16.455ms | 16.356ms | 98.306us | 4.736ms | **no** |
| `chebyshev_T24` | 24 | 5 | 3 | 8 | 2 | 8 | 840 | no | 168.039us | -- | -- | 397.369us | -- |
| `chebyshev_U24` | 24 | 3 | 4 | 10 | 2 | 16 | 960 | no | 315.969us | -- | -- | 619.689us | -- |
| `legendre_P30` | 30 | 61 | 15 | 2 | 2 | 32768 | 1330 | yes | 29.342ms | 463.328us | 28.879ms | 4.003ms | yes |
| `legendre_P38` | 38 | 79 | 3 | 36 | 3 | 12 | 6370 | no | 627.811us | -- | -- | 12.258ms | -- |
| `cyclo_phi17` | 16 | 3 | 1 | 16 | 1 | 1 | 1200 | no | 8.973us | -- | -- | 210.733us | -- |
| `cyclo_phi41` | 40 | 3 | 5 | 8 | 1 | 16 | 1080 | no | 1.453ms | -- | -- | 2.266ms | -- |
| `xpow24_minus1` | 24 | 5 | 14 | 2 | 1 | 8192 | 480 | yes | 949.247us | 479.331us | 469.916us | 390.429us | yes |
| `randprod_10` | 20 | 7 | 4 | 7 | 1 | 8 | 960 | no | 203.191us | -- | -- | 872.474us | -- |
| `randprod_21` | 24 | 17 | 7 | 9 | 1 | 64 | 1500 | no | 366.614us | -- | -- | 2.680ms | -- |

Across both tables, **all five checkable declines are confirmed**, and 5 of 14
checkable acceptances are. Two limitations and one real finding come out of that.

The limitation: nine declines cannot be checked from these records at all. The
counterfactual prices the *fixed* rule's retained set, which stops at the first
good prime when that image is narrow, so a narrow row has no alternative
downstream to compare against. Those nine are `cyclo_phi179`,
`cyclo_phi128_x_phi165`, `cyclo_phi385`, both Chebyshev rows, `legendre_P38`,
`cyclo_phi17`, `cyclo_phi41` and both `randprod` rows. Widening the
counterfactual to the whole scouting horizon would price them, at the cost of
replaying the downstream of primes no policy under test would select -- on
`xpow105_minus1` alone that is a 36-second row. The set was left pinned so this
table stays row-for-row comparable with the recorded baseline.

The finding: **all nine unconfirmed decisions are acceptances, and every one of
them is an acceptance the fixed threshold also made.** Each has width above
eight, so `scoutWidth = 8` bought the same observation. The change therefore
removes six observations that could not pay and introduces none. It does not
make the equal-width families better, and it was never going to; what it does is
stop the walk on the rows where looking was hopeless.

### Where the estimate is loosest, and why it stays

The three Wilkinson rows are the extreme case: `2^(w-1)` says 2·10^12 to 2·10^17
recombination candidates remain, and 40 to 56 are actually visited. A Wilkinson
image is 40 to 56 linear factors, every one of them a rational root, so the
search finds the whole factorization in its first cardinality level.

No shape-only rule can fix that, and the reason is worth stating precisely.
`sd5`'s image is sixteen quadratics and `legendre_P30`'s at `p = 61` is fifteen;
both look exactly like a Wilkinson image to any function of the degree multiset --
equal degrees, maximal width. But `sd5` is irreducible over the integers, so its
search does exhaust all `2^15` candidates and costs 63 ms, and `legendre_P30`'s
at `p = 61` costs 28 ms and is worth 28.9 ms of attainable saving. Whether the
search terminates in its first cardinality level or its last is a fact about the
*answer*, which the planner has not computed yet. Given that, the honest bound is
the exhaustive one, and the rule buys the observation.

Tightening this would need evidence about reducibility, not a better cost model.
Those rows are unchanged from the fixed threshold, so nothing regresses.

### Offline policy comparison

Every policy replayed over the same measured per-candidate costs. Modular costs
come from the scout section, where the good-prime test, the bounded scout and the
full split are timed adjacently in one process; downstream costs come from the
counterfactual section.

| instance | first | fixed | minwidth | maxfield | scout | voi | reachable | oracle | primes (first/fixed/scout/voi/oracle) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `sd5` | 67.344ms | 73.290ms | 73.434ms | 73.290ms | 71.296ms | 71.296ms | 70.588ms | 68.076ms | 19/29/29/29/29 |
| `sd5_shift1` | 62.069ms | 67.925ms | 68.047ms | 67.925ms | 66.106ms | 66.106ms | 64.585ms | 61.857ms | 19/29/29/29/23 |
| `sd5_shift2` | 62.909ms | 71.347ms | 71.225ms | 71.347ms | 68.785ms | 68.785ms | 62.909ms | 62.909ms | 19/29/29/29/19 |
| `sd4_x_sd4shift1` | 12.700ms | 19.172ms | 18.923ms | 19.172ms | 17.732ms | 17.732ms | 14.942ms | 13.151ms | 13/29/29/29/17 |
| `sd5_x_phi11` | 142.377ms | 146.253ms | 155.912ms | 146.253ms | 144.424ms | 144.424ms | 140.654ms | 136.082ms | 19/29/29/29/29 |
| `xpow48_minus1` | 6.572ms | 11.952ms | 11.952ms | 11.952ms | 10.268ms | 10.268ms | 6.572ms | 6.572ms | 5/11/11/11/5 |
| `xpow105_minus1` | 416.045ms | 50.206ms | 50.206ms | 50.206ms | 44.231ms | 44.231ms | 35.529ms | 23.872ms | 11/17/17/17/17 |
| `xpow120_minus1` | 143.933ms | 189.308ms | 189.308ms | 696.913ms | 146.379ms | 146.379ms | 143.933ms | 143.933ms | 7/7/7/7/7 |
| `cyclo_phi179` | 34.616ms | 34.616ms | 34.616ms | 34.616ms | 34.616ms | 34.616ms | 34.616ms | 34.616ms | 3/3/3/3/3 |
| `cyclo_phi64_x_phi105` | 18.137ms | 48.508ms | 48.508ms | 76.583ms | 45.395ms | 18.137ms | 18.137ms | 18.137ms | 11/11/11/11/11 |
| `cyclo_phi128_x_phi165` | 74.180ms | 74.180ms | 74.180ms | 74.180ms | 74.180ms | 74.180ms | 74.180ms | 74.180ms | 7/7/7/7/7 |
| `cyclo_phi385` | 142.763ms | 142.763ms | 142.763ms | 142.763ms | 142.763ms | 142.763ms | 142.763ms | 142.763ms | 3/3/3/3/3 |
| `wilkinson_40` | 8.911ms | 12.855ms | 12.825ms | 12.855ms | 11.073ms | 11.073ms | 10.841ms | 8.916ms | 41/47/47/47/43 |
| `wilkinson_48` | 15.985ms | 22.332ms | 22.320ms | 22.332ms | 19.438ms | 19.438ms | 15.985ms | 15.985ms | 53/61/61/61/53 |
| `wilkinson_56` | 21.084ms | 30.675ms | 30.537ms | 30.675ms | 26.392ms | 26.392ms | 25.639ms | 21.029ms | 59/67/67/67/61 |
| `chebyshev_T24` | 373.984us | 373.984us | 373.984us | 373.984us | 373.984us | 373.984us | 373.984us | 373.984us | 5/5/5/5/5 |
| `chebyshev_U24` | 513.262us | 513.262us | 513.262us | 513.262us | 513.262us | 513.262us | 513.262us | 513.262us | 3/3/3/3/3 |
| `legendre_P30` | 32.228ms | 6.983ms | 6.983ms | 6.983ms | 8.104ms | 8.104ms | 5.057ms | 2.189ms | 61/71/67/67/71 |
| `legendre_P38` | 3.468ms | 3.468ms | 3.468ms | 3.468ms | 3.468ms | 3.468ms | 3.468ms | 3.468ms | 79/79/79/79/79 |
| `cyclo_phi17` | 63.734us | 63.734us | 63.734us | 63.734us | 63.734us | 63.734us | 63.734us | 63.734us | 3/3/3/3/3 |
| `cyclo_phi41` | 1.917ms | 1.917ms | 1.917ms | 1.917ms | 1.917ms | 1.917ms | 1.917ms | 1.917ms | 3/3/3/3/3 |
| `xpow24_minus1` | 1.312ms | 2.462ms | 2.462ms | 2.462ms | 2.212ms | 2.212ms | 1.205ms | 844.711us | 5/11/11/11/7 |
| `randprod_10` | 550.917us | 550.917us | 550.917us | 550.917us | 550.917us | 550.917us | 550.917us | 550.917us | 7/7/7/7/7 |
| `randprod_21` | 1.256ms | 1.256ms | 1.256ms | 1.256ms | 1.256ms | 1.256ms | 1.256ms | 1.256ms | 17/17/17/17/17 |
| **aggregate** | **1.271s** | **1.013s** | **1.022s** | **1.549s** | **941.538ms** | **914.279ms** | **876.277ms** | **843.253ms** | |

The four policies the issue asks to be controlled against all fail, each in its
own way:

* **first** -- stopping at the first acceptable prime is unusable at 1.271 s.
  `xpow105_minus1` alone is 416.045 ms of that against 44.231 ms, and
  `legendre_P30` is 32.228 ms against 8.104 ms. This is why a scout-nothing rule
  is not on the table, and why `xpow105_minus1` is a mandatory control.
* **minwidth** -- a degree cost model on its own is worse than the score at
  1.022 s. `sd5_x_phi11` is where it shows: prime 23 is widest, and prime 29 wins
  only on the tie breaks the score already carries.
* **maxfield** -- a field-size cost model on its own is the worst of all at
  1.549 s. It picks the largest prime for its smaller Hensel precision and pays
  in recombination: `xpow120_minus1` goes from 146 ms to 696.913 ms.
* **fixed** -- the pre-scout rule, 1.013 s. The scout replaced it in #9128.

On this 24-instance set `voi` saves 27.258 ms of 941.538 ms and closes 41.8% of
the distance from `scout` to the `reachable` floor. Over the six rows the rule
actually changes it saves 253.414 ms of 953.972 ms and closes 99.9% of that
distance -- there is essentially nothing left on those rows for a discovering
policy to take. The `reachable` and `oracle` floors are unreachable by
construction: neither ever scouts, and the oracle names the winner without paying
to discover it.

## Paired before and after

The two service binaries were built from this worktree and differ only in the
planner and the diagnostic service entries, and the arms were alternated on the
same pinned core, so host load hits both equally.

### The rows whose walk changes, and their controls

`--changed` names the six changed rows explicitly: a dropped scout moves neither
the selected prime nor the split count, so the driver's automatic control split
cannot see it. The other six rows are the load control.

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `cyclo_phi105_x_phi128` | 11 | 11 | 1 -> 1 | 71.829 ms | 22.204 ms | 49.625 ms | 86.349 ms | 35.378 ms | 0.410x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 1 -> 1 | 37.545 ms | 10.725 ms | 26.820 ms | 45.992 ms | 18.700 ms | 0.407x |
| `sd4_x_phi17` | 11 | 11 | 1 -> 1 | 5.278 ms | 1.517 ms | 3.761 ms | 6.645 ms | 2.922 ms | 0.440x |
| `legendre_P18` | 41 | 37 | 2 -> 1 | 1.985 ms | 695.492 us | 1.290 ms | 2.181 ms | 1.315 ms | 0.603x |
| `cyclo_phi24_x_phi35` | 17 | 13 | 2 -> 2 | 8.094 ms | 4.681 ms | 3.412 ms | 8.891 ms | 6.682 ms | 0.752x |
| `cyclo_phi275` | 13 | 3 | 2 -> 1 | 189.673 ms | 26.451 ms | 163.223 ms | 806.894 ms | 637.863 ms | 0.791x |
| `sd4_x_sd4shift1` | 29 | 29 | 2 -> 2 | 6.935 ms | 6.902 ms | 32.808 us | 17.918 ms | 17.719 ms | 0.989x |
| `xpow105_minus1` | 17 | 17 | 2 -> 2 | 29.228 ms | 29.408 ms | -179.237 us | 44.621 ms | 44.653 ms | 1.001x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 6.440 ms | 6.602 ms | -162.011 us | 34.931 ms | 35.707 ms | 1.022x |
| `legendre_P30` | 67 | 67 | 2 -> 2 | 7.080 ms | 7.163 ms | -83.053 us | 8.406 ms | 8.480 ms | 1.009x |
| `wilkinson_40` | 47 | 47 | 2 -> 2 | 4.127 ms | 4.707 ms | -580.471 us | 12.301 ms | 12.899 ms | 1.049x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 943.168 us | 953.514 us | -10.346 us | 1.408 ms | 1.418 ms | 1.007x |
| **aggregate** | | | | | | 247.149 ms | 1.077 s | 823.735 ms | **0.7652x** |

Load control (6 instances whose plan does not change): 0.989x to 1.049x.

`cyclo_phi275` is the largest absolute win: 163.223 ms of prime walk, because the
fixed rule scouted two further primes at 65 ms and 45 ms apiece and then split
one of them, all to select a prime whose downstream is 2 ms *worse* than the one
it started with.

### The issue #9127 representative set

The same protocol over the elbow set, where `cyclo_phi64_x_phi105` is the only
changed row. This is the table the acceptance threshold is read from.

| instance | prime before | prime after | full splits | prime walk before | prime walk after | walk saved | total before | total after | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 29 | 2 -> 2 | 6.551 ms | 6.699 ms | -147.458 us | 67.942 ms | 67.985 ms | 1.001x |
| `sd5_shift1` | 29 | 29 | 2 -> 2 | 7.158 ms | 7.164 ms | -5.188 us | 63.118 ms | 62.972 ms | 0.998x |
| `sd5_shift2` | 29 | 29 | 2 -> 2 | 8.563 ms | 8.711 ms | -147.589 us | 66.655 ms | 66.431 ms | 0.997x |
| `sd4_x_sd4shift1` | 29 | 29 | 2 -> 2 | 6.743 ms | 6.928 ms | -184.874 us | 17.695 ms | 17.750 ms | 1.003x |
| `sd5_x_phi11` | 29 | 29 | 2 -> 2 | 16.195 ms | 16.412 ms | -217.042 us | 139.999 ms | 138.988 ms | 0.993x |
| `xpow48_minus1` | 11 | 11 | 2 -> 2 | 3.922 ms | 3.990 ms | -67.951 us | 10.377 ms | 10.364 ms | 0.999x |
| `xpow105_minus1` | 17 | 17 | 2 -> 2 | 29.041 ms | 29.621 ms | -580.179 us | 44.313 ms | 44.539 ms | 1.005x |
| `xpow120_minus1` | 7 | 7 | 1 -> 1 | 18.436 ms | 18.639 ms | -203.723 us | 145.844 ms | 145.933 ms | 1.001x |
| `cyclo_phi179` | 3 | 3 | 1 -> 1 | 6.482 ms | 6.717 ms | -235.118 us | 34.775 ms | 34.991 ms | 1.006x |
| `cyclo_phi64_x_phi105` | 11 | 11 | 1 -> 1 | 38.110 ms | 10.759 ms | 27.351 ms | 45.068 ms | 18.762 ms | 0.416x |
| `cyclo_phi128_x_phi165` | 7 | 7 | 1 -> 1 | 35.000 ms | 35.295 ms | -295.157 us | 75.101 ms | 75.002 ms | 0.999x |
| `cyclo_phi385` | 3 | 3 | 1 -> 1 | 58.839 ms | 59.612 ms | -773.447 us | 143.366 ms | 144.368 ms | 1.007x |
| `wilkinson_40` | 47 | 47 | 2 -> 2 | 4.134 ms | 4.417 ms | -282.669 us | 12.367 ms | 12.497 ms | 1.010x |
| `wilkinson_48` | 61 | 61 | 2 -> 2 | 6.535 ms | 6.887 ms | -352.603 us | 21.199 ms | 21.384 ms | 1.009x |
| `wilkinson_56` | 67 | 67 | 2 -> 2 | 9.636 ms | 10.024 ms | -388.046 us | 28.320 ms | 28.945 ms | 1.022x |
| `chebyshev_T24` | 5 | 5 | 1 -> 1 | 213.176 us | 222.199 us | -9.023 us | 435.947 us | 444.499 us | 1.020x |
| `chebyshev_U24` | 3 | 3 | 1 -> 1 | 203.001 us | 214.738 us | -11.737 us | 593.950 us | 609.203 us | 1.026x |
| `legendre_P30` | 67 | 67 | 2 -> 2 | 7.103 ms | 7.193 ms | -89.863 us | 8.385 ms | 8.385 ms | 1.000x |
| `legendre_P38` | 79 | 79 | 1 -> 1 | 2.985 ms | 3.035 ms | -50.615 us | 3.801 ms | 3.845 ms | 1.012x |
| `cyclo_phi17` | 3 | 3 | 1 -> 1 | 56.964 us | 60.900 us | -3.936 us | 105.166 us | 109.212 us | 1.038x |
| `cyclo_phi41` | 3 | 3 | 1 -> 1 | 471.218 us | 490.718 us | -19.500 us | 1.992 ms | 2.006 ms | 1.007x |
| `xpow24_minus1` | 11 | 11 | 2 -> 2 | 1.095 ms | 1.121 ms | -25.387 us | 2.296 ms | 2.323 ms | 1.012x |
| `randprod_10` | 7 | 7 | 1 -> 1 | 355.417 us | 365.882 us | -10.465 us | 619.288 us | 638.166 us | 1.030x |
| `randprod_21` | 17 | 17 | 1 -> 1 | 950.869 us | 952.983 us | -2.114 us | 1.400 ms | 1.430 ms | 1.021x |
| **aggregate** | | | | | | 23.247 ms | 935.767 ms | 910.701 ms | **0.9732x** |

Load control (23 instances whose plan does not change): 0.993x to 1.038x.

The control band is one-sided in both tables: its median is 1.007x, and every
unchanged row shows a slightly slower walk in the second arm. The driver runs the
before arm first in each round, so whatever drift a round accumulates is charged
to the after arm. That biases against the change, which makes the changed rows'
ratios conservative rather than flattering.

## Full corpus

Both arms of the same sweep, same day, same core, ten-second per-call cutoff,
early termination disabled.

| | before | after |
|---|---:|---:|
| solved | 377 of 392 | 377 of 392 |
| instances lost | | none |
| instances gained | | none |
| aggregate over the 377 rows both solve | 17.980 s | 17.663 s (0.9824x) |
| median per-row ratio | | 1.0257x |

The aggregate improves by 317 ms while the *median* row is 2.6% slower, which is
the same one-sided drift the paired control shows, amplified because a sweep is a
single pass rather than three alternating rounds. Read that way the corpus result
is: six large wins, and no row whose slowdown exceeds what the instrument itself
contributes.

One row exceeds 1.10x while costing more than 2 ms: `sd4_x_sd4shift1`, 17.795 ms
to 21.860 ms, 1.228x. It is not a plan change -- both arms select prime 29 with
two splits -- and the paired driver, which is the better instrument for it, puts
it at 0.989x over three alternating rounds. It is recorded here rather than
dropped, and attributed to single-pass noise.

### Combined-cactus elbow

Cumulative time over the 160-instance combined mixture, both arms, independently
sorted as the figures plot it. Both arms solve 145 of 160.

| rank | cumulative before | cumulative after | ratio |
|---:|---:|---:|---:|
| 118 | 85.2 ms | 82.7 ms | 0.9703x |
| 122 | 115.5 ms | 110.7 ms | 0.9588x |
| 126 | 173.8 ms | 171.5 ms | 0.9866x |
| 130 | 292.7 ms | 277.4 ms | 0.9478x |
| 134 | 509.5 ms | 483.4 ms | 0.9489x |
| 138 | 861.1 ms | 838.2 ms | 0.9734x |
| 140 | 1152.5 ms | 1133.1 ms | 0.9832x |
| 142 | 2459.2 ms | 2441.6 ms | 0.9929x |
| 144 | 8489.1 ms | 8395.2 ms | 0.9889x |
| 145 | 16835.5 ms | 16727.8 ms | 0.9936x |

The elbow improves at every rank, by 0.948x to 0.994x, and coverage is
unchanged. `cyclo_phi64_x_phi105` moves from rank 132 to rank 126 in the Hex
ordering, and `cyclo_phi105_x_phi128` and `cyclo_phi275` leave the elbow band
entirely.

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

`conformance/HexBerlekampZassenhaus/Conformance.lean` pins both directions of the
decision and the modulus width it reads: one modular factor never pays, four
factors reaching degree 16 never pay, ten quadratic factors do, and `liftWords`
of the Legendre input at 3 is two machine words.

## Acceptance criteria

**Reduces prime-walk time by at least 20% and total time by at least 10% on
`cyclo_phi64_x_phi105`.** Prime walk 38.110 ms to 10.759 ms, **-71.8%**. Total
45.068 ms to 18.762 ms, **-58.4%**. Paired, three alternating rounds, against a
load control of 0.993x to 1.038x whose bias runs against the change.

**Preserves the order-of-magnitude scouting benefit on `xpow105_minus1`.** It
selects prime 17 at width 14 with two splits, exactly as before, at 1.001x
paired. Its first prime is worth 389.287 ms of attainable saving for a 17.086 ms
observation, and the `first` control prices what losing the scout would cost:
416.045 ms against 44.231 ms, 9.4x.

**Does not materially regress the full corpus or reduce solved coverage.**
377 of 392 in both arms, no instance lost or gained, aggregate 0.9824x. The one
row above 1.10x and 2 ms is `sd4_x_sd4shift1`, which the paired driver puts at
0.989x; it is not a plan change.

**Improves, or at least does not regress, the combined-cactus elbow.** The
cumulative curve improves at every rank from 118 to 145, by 0.948x to 0.994x,
with coverage unchanged at 145 of 160.

**Passes a fresh all-systems performance sweep and regenerates every cactus plot
in the same PR.** `scripts/bench/check_factor_sweep_freshness.py` reports
"factorization performance data covers the current corpus and source"; the Hex
sweep is fresh at this revision from a clean tree and the external comparator
records are reused unchanged. All 25 figures are regenerated and
`scripts/plots/hexbz-cactus.py --check` passes byte for byte.

**Deterministic and shape-based, no family recognizer.** `scoutPays` reads the
degree of the input, the primes involved, and the degree multisets already
observed. There is no benchmark name, corpus identity, or family recognizer in
the planner, and the two constants are integers whose decisions are invariant
over a 3x range in either direction.

**Existing `DirectPrimePlan` facts and retained-prime certificates remain
proved.** Recorded under "Proof surface" above.

## Follow-up

`powModMonicAux` remains the cost of a bounded scout, and after this change it is
charged only where the rule has priced a scout as worthwhile. On the rows where
the rule now declines, the scouts are gone entirely: `cyclo_phi105_x_phi128` no
longer pays 108 ms for a complete pattern it cannot use. Where it still scouts,
the equal-width families are where the observation is cheap but ex post
worthless, and the cause is the reducibility question above, not a kernel cost.
Per the issue's last dependency note, any kernel work on `powModMonicAux` belongs
in a separate issue opened from the post-change profile rather than folded in
here.

## Regeneration

```sh
lake build hexbz_factor_service

# Two arms differing only in the planner and the diagnostic service entries.
git checkout <before> -- HexBerlekampZassenhaus/Modular/PrimePlan.lean \
  bench/HexBench/FactorService.lean
lake build hexbz_factor_service && cp .lake/build/bin/hexbz_factor_service /tmp/svc.before
git checkout HEAD -- HexBerlekampZassenhaus/Modular/PrimePlan.lean \
  bench/HexBench/FactorService.lean
lake build hexbz_factor_service && cp .lake/build/bin/hexbz_factor_service /tmp/svc.after

CPU="$(python3 scripts/bench/idle_core.py)"

# Paired, the representative set and the changed rows.
python3 scripts/bench/prime_plan_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --rounds 3 --cpu "$CPU" \
  --changed cyclo_phi64_x_phi105 \
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-9710df88-chungus2.json
python3 scripts/bench/prime_plan_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --rounds 3 --cpu "$CPU" \
  --names cyclo_phi105_x_phi128,cyclo_phi64_x_phi105,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275,sd4_x_sd4shift1,xpow105_minus1,cyclo_phi179,legendre_P30,wilkinson_40,randprod_21 \
  --changed cyclo_phi105_x_phi128,cyclo_phi64_x_phi105,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275 \
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-changed-9710df88-chungus2.json

# Full Hex sweep, both arms, on a clean tree. The freshness check rejects a
# record whose tree was dirty, so write outside the repo and install after.
taskset -c "$CPU" python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate --output /tmp/sweep-after.json
cp /tmp/svc.before .lake/build/bin/hexbz_factor_service
taskset -c "$CPU" python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate --output /tmp/sweep-before.json
cp /tmp/svc.after .lake/build/bin/hexbz_factor_service

# Per-candidate scout prices, counterfactual downstream, kernel attribution.
python3 scripts/bench/factor_phase_profile.py --cpu "$CPU" \
  --output /tmp/profile.json
python3 scripts/bench/factor_phase_profile.py --cpu "$CPU" --no-kernel \
  --validate-names cyclo_phi17 \
  --names cyclo_phi105_x_phi128,sd4_x_phi17,legendre_P18,cyclo_phi24_x_phi35,cyclo_phi275,cyclo_phi64_x_phi105 \
  --output /tmp/profile-changed.json

# Offline policy replay, decision margins, ratio sensitivity, and the replay's
# own check that the rule reproduces the measured binary's selection.
python3 scripts/bench/prime_policy_replay.py \
  reports/bench-results/hexbz-phase-profile-9710df88-chungus2.json \
  --margins --sensitivity --agrees-with voi

# Rank tables and figures, and the byte-for-byte check CI runs.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
python3 scripts/bench/check_factor_sweep_freshness.py
```
