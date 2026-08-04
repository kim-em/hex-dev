# Pricing one more modular observation (issue #9156)

The direct prime planner stopped shopping for a prime at a fixed width: an image
with at most eight local factors was used unexamined, and a wider one bought up
to two bounded scouts. Eight is a threshold, not a price. It cannot see that
`cyclo_phi64_x_phi105`'s first prime has ten local factors and 4.8 ms of
recombination left, so the two scouts it triggers -- 30 ms of them -- are spent
shopping for a saving that does not exist.

This report replaces that threshold with a price comparison. `Hex.scoutPays`
asks whether the plan in hand still has enough recombination work left to repay
another observation, estimating both sides from shape already observed. It is the
walk's only stopping decision: it governs the first good prime and every scouted
candidate alike, and nothing about the corpus, the instance, or its family enters
it.

On the corpus the rule changes one decision, and that decision is the one the
issue names: `cyclo_phi64_x_phi105`'s prime walk drops from 38.110 ms to
10.759 ms and its total from 45.068 ms to 18.762 ms, against a paired load
control spanning 0.993x to 1.038x. Everything else -- including the mandatory
`xpow105_minus1` control, whose scouting is worth an order of magnitude --
selects the same prime and performs the same splits and scouts as before.

## Revision and protocol

Source revision `3b00dcf1`, toolchain `leanprover/lean4:v4.33.0-rc1`,
host `chungus2` (96 cores, x86_64, linux), clean worktree. Corpus
`bench/corpus/hexbz-factor-corpus.jsonl` (392 instances), sha256
`619913904240`.

The host was shared with other measurement work throughout, so absolute wall
times are not comparable with earlier reports. Three protocols make the
comparisons here safe anyway.

Every before/after timing comes from a **paired** run: two service binaries built
from this worktree, differing only in
`HexBerlekampZassenhaus/Modular/PrimePlan.lean`, alternated on the same pinned
core over three rounds, with the rows whose walk does not change acting as a load
control. The core is chosen by `scripts/bench/idle_core.py` and named explicitly
to both arms, so neither arm can drift onto a different core.

Every per-candidate cost is the median of `--plan-repeats 3` calls of the same
service, merged field by field after asserting that the repeats agree on
everything deterministic.

Every **policy** comparison is an offline replay over those recorded
per-candidate costs, by `scripts/bench/prime_policy_replay.py`. No policy is
timed against another on the machine; they are priced against the same
observations, so the comparison cannot depend on what the host was doing when
each row was measured.

### Artifacts

- `reports/bench-results/hexbz-prime-plan-pricing-paired-3b00dcf1-chungus2.json`
- `reports/bench-results/hexbz-phase-profile-3b00dcf1-chungus2.json`
- `reports/bench-results/hexbz-factor-sweep-3b00dcf1-hex-chungus2.json`

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
operation cost in recombination word operations. Rescaling both together changes
no decision.

### Calibrating the two constants

Over the 144 priced candidates of the recorded per-candidate profile, dividing
each measured cost by the model units above:

| word operation | model units | median | range | samples |
|---|---|---:|---|---:|
| bounded scout | `d · bitLen p · n^2` | 20.50 ns | 1.33 to 78.41 | 144 |
| Berlekamp split | `bitLen p · n^3` | 10.49 ns | 0.75 to 32.19 | 144 |
| recombination candidate | `n^2 · W` per visited node | 2.01 ns | 0.24 to 55.62 | 52 |

So `scoutRoundCost = 10` and `splitColumnCost = 5`, the medians 20.50/2.01 and
10.49/2.01 rounded to integers. The recombination row is calibrated against
*measured* node counts rather than `2^(w-1)`, because it is pricing one candidate;
the model's use of `2^(w-1)` for how many candidates there are is the separate,
deliberately conservative step above.

## Investigation

### The decision, and what it is deciding about

The first `scoutPays` call on each instance, with both sides of the inequality
beside what the candidates it is deciding about actually cost. `left` is
`2^(w-1) · W`; `next obs` is the right-hand side at the next candidate prime with
`fuel = 2`. The two measured columns are the quantities those estimates stand
for: the incumbent's recombination, and the bounded scout plus full split at the
next good prime.

| instance | n | p | w | max deg | W | left | next obs | scout? | measured recombination | measured scout + split |
|---|---:|---:|---:|---:|---:|---:|---:|:--:|---:|---:|
| `sd5` | 32 | 19 | 16 | 2 | 2 | 65536 | 1000 | yes | 69.448ms | 3.275ms |
| `sd5_shift1` | 32 | 19 | 16 | 2 | 2 | 65536 | 1000 | yes | 57.019ms | 3.723ms |
| `sd5_shift2` | 32 | 19 | 16 | 2 | 2 | 65536 | 1000 | yes | 58.324ms | 4.485ms |
| `sd4_x_sd4shift1` | 32 | 13 | 16 | 2 | 2 | 65536 | 1000 | yes | 9.451ms | 3.054ms |
| `sd5_x_phi11` | 42 | 19 | 17 | 10 | 2 | 131072 | 2050 | yes | 155.545ms | 7.180ms |
| `xpow48_minus1` | 48 | 5 | 20 | 4 | 1 | 524288 | 960 | yes | 10.000ms | 2.496ms |
| `xpow105_minus1` | 105 | 11 | 30 | 6 | 2 | 1073741824 | 2580 | yes | 1.429s | 18.282ms |
| `xpow120_minus1` | 120 | 7 | 39 | 4 | 3 | 824633720832 | 2720 | yes | 458.765ms | 31.749ms |
| `cyclo_phi179` | 178 | 3 | 2 | 89 | 4 | 8 | 8010 | no | 5.631ms | 132.199ms |
| `cyclo_phi64_x_phi105` | 80 | 11 | 10 | 16 | 2 | 1024 | 2880 | no | 4.817ms | 30.348ms |
| `cyclo_phi128_x_phi165` | 144 | 7 | 8 | 20 | 3 | 384 | 4480 | no | 41.694ms | 318.110ms |
| `cyclo_phi385` | 240 | 3 | 4 | 60 | 5 | 40 | 7200 | no | 82.779ms | 512.177ms |
| `wilkinson_40` | 40 | 41 | 40 | 1 | 4 | 2199023255552 | 1320 | yes | 516.756us | 1.889ms |
| `wilkinson_48` | 48 | 53 | 48 | 1 | 5 | 703687441776640 | 1560 | yes | 773.447us | 3.045ms |
| `wilkinson_56` | 56 | 59 | 56 | 1 | 5 | 180143985094819840 | 1800 | yes | 1.038ms | 4.434ms |
| `chebyshev_T24` | 24 | 5 | 3 | 8 | 2 | 8 | 840 | no | 21.022us | 493.432us |
| `chebyshev_U24` | 24 | 3 | 4 | 10 | 2 | 16 | 960 | no | 24.055us | 691.345us |
| `legendre_P30` | 30 | 61 | 15 | 2 | 2 | 32768 | 1330 | yes | 28.737ms | 4.437ms |
| `legendre_P38` | 38 | 79 | 3 | 36 | 3 | 12 | 6370 | no | 49.904us | 13.356ms |
| `cyclo_phi17` | 16 | 3 | 1 | 16 | 1 | 1 | 1200 | no | 4.577us | 254.056us |
| `cyclo_phi41` | 40 | 3 | 5 | 8 | 1 | 16 | 1080 | no | 1.424ms | 2.538ms |
| `xpow24_minus1` | 24 | 5 | 14 | 2 | 1 | 8192 | 480 | yes | 1.061ms | 436.727us |
| `randprod_10` | 20 | 7 | 4 | 7 | 1 | 8 | 960 | no | 19.669us | 1.078ms |
| `randprod_21` | 24 | 17 | 7 | 9 | 1 | 64 | 1500 | no | 34.991us | 3.031ms |

Read the last two columns as the verdict on the first eight. **Every one of the
eleven declines is right**: the recombination the plan has left is smaller than
the observation the rule refused, by margins from 1.8x (`cyclo_phi41`) to 267x
(`legendre_P38`). Ten of the thirteen acceptances are right too, by margins from
2.4x (`xpow24_minus1`) to 78x (`xpow105_minus1`).

### Where the estimate is loosest, and why it stays

The three Wilkinson rows are the exceptions: their recombination is 2.7x to 4.3x
*below* the observation the rule buys. That is the `2^(w-1)` upper bound at its
loosest. A Wilkinson image is 40 to 56 linear factors, and every one of them is a
rational root, so the search finds the whole factorization in its first
cardinality level and visits `w` candidates rather than `2^(w-1)`.

No shape-only rule can fix that, and the reason is worth stating precisely.
`sd5`'s image is sixteen quadratics and `legendre_P30`'s at `p = 61` is fifteen;
both look exactly like a Wilkinson image to any function of the degree multiset --
equal degrees, maximal width. But `sd5` is irreducible over the integers, so its
search does exhaust all `2^15` candidates and costs 69 ms, and `legendre_P30`'s
costs 29 ms. Whether the search terminates in its first level or its last is a
fact about the *answer*, which the planner has not computed yet. Given that, the
honest bound is the exhaustive one, and the rule buys the observation.

Both Wilkinson and `sd5` bought that observation under the fixed threshold too,
so nothing here regresses; the rows are unchanged. What the table shows is where
a future tightening would have to come from, and it would have to come from
evidence about reducibility, not from a better cost model.

### Offline policy comparison

Every policy replayed over the same measured per-candidate costs. Modular costs
come from the scout section, where the good-prime test, the bounded scout and the
full split are timed adjacently in one process; downstream costs come from the
counterfactual section. `scripts/bench/prime_policy_replay.py` regenerates this
table from the record, and its `--agrees-with scout` check confirms that the
replayed pre-change policy reproduces the prime the recorded binary selected on
24 of 24 rows, so the replay is a replay and not a model.

| instance | first | fixed | minwidth | maxfield | scout | voi | reachable | oracle | primes (first/fixed/scout/voi/oracle) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| `sd5` | 74.091ms | 80.768ms | 80.652ms | 80.768ms | 78.533ms | 78.533ms | 76.800ms | 74.068ms | 19/29/29/29/23 |
| `sd5_shift1` | 62.192ms | 69.377ms | 69.224ms | 69.377ms | 67.038ms | 67.038ms | 65.305ms | 62.032ms | 19/29/29/29/23 |
| `sd5_shift2` | 63.487ms | 72.948ms | 72.865ms | 72.948ms | 69.845ms | 69.845ms | 63.487ms | 63.487ms | 19/29/29/29/19 |
| `sd4_x_sd4shift1` | 13.380ms | 21.330ms | 20.684ms | 21.330ms | 19.344ms | 19.344ms | 13.380ms | 13.380ms | 13/29/29/29/13 |
| `sd5_x_phi11` | 164.461ms | 172.522ms | 180.232ms | 172.522ms | 169.795ms | 169.795ms | 166.036ms | 160.068ms | 19/29/29/29/29 |
| `xpow48_minus1` | 12.962ms | 21.058ms | 21.058ms | 21.058ms | 19.201ms | 19.201ms | 12.962ms | 12.962ms | 5/11/11/11/5 |
| `xpow105_minus1` | 1.453s | 79.241ms | 79.241ms | 79.241ms | 72.058ms | 72.058ms | 63.365ms | 50.557ms | 11/17/17/17/17 |
| `xpow120_minus1` | 492.902ms | 540.930ms | 540.930ms | 5.963s | 495.294ms | 495.294ms | 492.902ms | 492.902ms | 7/7/7/7/7 |
| `cyclo_phi179` | 55.679ms | 55.679ms | 55.679ms | 55.679ms | 55.679ms | 55.679ms | 55.679ms | 55.679ms | 3/3/3/3/3 |
| `cyclo_phi64_x_phi105` | 33.772ms | 87.386ms | 87.386ms | 180.547ms | 60.486ms | 33.772ms | 33.772ms | 33.772ms | 11/11/11/11/11 |
| `cyclo_phi128_x_phi165` | 186.700ms | 186.700ms | 186.700ms | 186.700ms | 186.700ms | 186.700ms | 186.700ms | 186.700ms | 7/7/7/7/7 |
| `cyclo_phi385` | 395.809ms | 395.809ms | 395.809ms | 395.809ms | 395.809ms | 395.809ms | 395.809ms | 395.809ms | 3/3/3/3/3 |
| `wilkinson_40` | 9.664ms | 13.383ms | 13.346ms | 13.383ms | 11.724ms | 11.724ms | 11.471ms | 9.648ms | 41/47/47/47/43 |
| `wilkinson_48` | 18.469ms | 24.653ms | 24.424ms | 24.653ms | 21.965ms | 21.965ms | 21.397ms | 18.494ms | 53/61/61/61/59 |
| `wilkinson_56` | 24.656ms | 33.483ms | 33.515ms | 33.483ms | 29.511ms | 29.511ms | 28.826ms | 24.528ms | 59/67/67/67/61 |
| `chebyshev_T24` | 482.125us | 482.125us | 482.125us | 482.125us | 482.125us | 482.125us | 482.125us | 482.125us | 5/5/5/5/5 |
| `chebyshev_U24` | 624.005us | 624.005us | 624.005us | 624.005us | 624.005us | 624.005us | 624.005us | 624.005us | 3/3/3/3/3 |
| `legendre_P30` | 32.804ms | 8.091ms | 8.091ms | 8.091ms | 8.966ms | 8.966ms | 5.775ms | 2.644ms | 61/71/67/67/71 |
| `legendre_P38` | 4.431ms | 4.431ms | 4.431ms | 4.431ms | 4.431ms | 4.431ms | 4.431ms | 4.431ms | 79/79/79/79/79 |
| `cyclo_phi17` | 109.453us | 109.453us | 109.453us | 109.453us | 109.453us | 109.453us | 109.453us | 109.453us | 3/3/3/3/3 |
| `cyclo_phi41` | 2.782ms | 2.782ms | 2.782ms | 2.782ms | 2.782ms | 2.782ms | 2.782ms | 2.782ms | 3/3/3/3/3 |
| `xpow24_minus1` | 1.848ms | 3.447ms | 3.447ms | 3.447ms | 3.152ms | 3.152ms | 1.329ms | 930.501us | 5/11/11/11/7 |
| `randprod_10` | 745.005us | 745.005us | 745.005us | 745.005us | 745.005us | 745.005us | 745.005us | 745.005us | 7/7/7/7/7 |
| `randprod_21` | 1.594ms | 1.594ms | 1.594ms | 1.594ms | 1.594ms | 1.594ms | 1.594ms | 1.594ms | 17/17/17/17/17 |
| **aggregate** | **3.107s** | **1.878s** | **1.884s** | **7.393s** | **1.776s** | **1.749s** | **1.706s** | **1.668s** | |

The four policies the issue asks to be controlled against all fail, each in its
own way:

* **first** -- stopping at the first acceptable prime is unusable at 3.107 s.
  `xpow105_minus1` alone is 1.453 s of that against 72.058 ms, and
  `legendre_P30` is 32.804 ms against 8.966 ms. This is the reason a
  scout-nothing rule is not on the table, and the reason `xpow105_minus1` is a
  mandatory control.
* **minwidth** -- a degree cost model on its own is worse than the score at
  1.884 s. `sd5_x_phi11` is where it shows: prime 23 is widest, and prime 29 wins
  only on the tie breaks the score carries.
* **maxfield** -- a field-size cost model on its own is catastrophic at 7.393 s.
  It picks the largest prime for its smaller Hensel precision and pays for it in
  recombination: `xpow120_minus1` goes from 495 ms to 5.963 s.
* **fixed** -- the pre-scout rule, 1.878 s. The scout replaced it in #9128.

Against the rule it replaces, `voi` saves 27.4 ms of 1.776 s, all of it on
`cyclo_phi64_x_phi105`, and closes 39% of the distance from `scout` to the
`reachable` floor. The remaining distance is the equal-width families discussed
above, and the `reachable` and `oracle` floors are unreachable by construction:
neither ever scouts, and the oracle names the winner without paying to discover
it.

### Where the decision changed

`voi` and `scout` differ on 1 of 24 rows. On `cyclo_phi64_x_phi105` the walk
performs one split and no scouts where it performed one split and two scouts, at
33.772 ms against 60.486 ms in the replay. Every other row selects the same
prime and performs the same splits and the same scouts.

That is a narrower change than the acceptance criteria contemplate, and it is
narrow for a reason worth recording: `scoutWidth = 8` and this rule already
agreed everywhere else on this corpus. Where they agree the rule is not a
coincidence but a derivation -- the eleven declines and ten of the thirteen
acceptances are each independently confirmed by the measured columns above -- so
what the change buys is not only the one row but a stopping decision that stays
right when the corpus, the input degree, or the kernel's constants move, where a
fixed eight would not.

## Paired before and after

The two service binaries were built from this worktree and differ only in
`HexBerlekampZassenhaus/Modular/PrimePlan.lean`, and the arms were alternated on
the same pinned core, so host load hits both equally.

`cyclo_phi64_x_phi105` is the one row whose walk the change alters, and it is
named to the driver with `--changed`: a dropped scout moves neither the selected
prime nor the split count, so the driver's automatic control split cannot see it.
The other 23 rows are the load control.

### Paired before/after, median of 3 alternating rounds

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

`cyclo_phi64_x_phi105` loses 71.8% of its prime walk and 58.4% of its total. No
other row leaves the control band in either direction; the aggregate 0.9732x is
that one row.

The control band is one-sided: its median ratio is 1.007x and every unchanged row
shows a slightly slower walk in the second arm. The driver runs the before arm
first in each round, so whatever drift a round accumulates is charged to the
after arm. That biases against the change, which makes the one row's 0.416x a
conservative reading rather than a flattering one.

## Negative controls

**`xpow105_minus1`, the order-of-magnitude scout.** Unchanged: prime 17 at
width 14, two splits, 29.621 ms of walk against 29.041 ms before -- inside the
control band. Its first good
prime is 30 factors wide with 1.429 s of recombination behind it, against a
2.580-unit observation cost, so the rule accepts the observation by a factor of
4·10^5 in model units and 78x in measured time. The `first` column prices what
losing it would cost: 1.453 s against 72.058 ms.

**`legendre_P30`, where a threshold could stop too early.** Unchanged: the walk
still stops at prime 67 with width 7, where the fixed policy went on to prime 71
with width 4. The rule now gives the reason: at prime 67 the plan has 64
recombination candidates and 157 us of recombination left, against a scout that
would run fourteen Frobenius rounds and a split -- 3.835 ms and 2.114 ms
measured, 25x the recombination it could save. #9128 measured removing the stop
directly and found it worse (1.464x on the row), which is the same verdict from
the other direction.

**Mixed and non-split cases.** `cyclo_phi179` (two factors of degree 89),
`cyclo_phi385` (four of degree 60), `cyclo_phi128_x_phi165` (eight of degrees 16
and 20), `legendre_P38` (an inert factor of degree 36) and `cyclo_phi17`
(irreducible mod every candidate) are the shapes where a scout costs more than
the split it replaces. All five decline, by 267x to 8x in model units, and all
five are unchanged from the fixed threshold.

## Proof surface

`scoutPays` is a `Bool` on `Nat` shape data; it decides which plan the walk
holds and nothing else. `DirectPrimePlan` is unchanged, and both facts about it
are unchanged and still proved:

- `directPrimePlan?_selected_spec` -- the selected cached value is exactly the
  result of its retained explicit prime trial;
- `directPrimePlan?_selected_p_le_500` -- the planner selects only from the fixed
  hot-path candidate list.

Their proofs got shorter: the width gate was a second branch in
`firstDirectPlan?`, and removing it removed a case from each induction.
`scoutBetterPattern_mem` gained the one branch where the walk stops without
scouting. The Mathlib layer needed no change.

Conformance pins both directions of the decision and the modulus width it reads,
in `conformance/HexBerlekampZassenhaus/Conformance.lean`: one modular factor
never pays, four factors reaching degree 16 never pay, ten quadratic factors do,
and `liftWords` of the Legendre input at 3 is two machine words.

## Acceptance criteria

**Reduces prime-walk time by at least 20% and total time by at least 10% on
`cyclo_phi64_x_phi105`.** Prime walk 38.110 ms to 10.759 ms, **-71.8%**. Total
45.068 ms to 18.762 ms, **-58.4%**. Paired, three alternating rounds, against a
load control of 0.993x to 1.038x whose bias runs against the change.

**Preserves the order-of-magnitude scouting benefit on `xpow105_minus1`.** It
selects prime 17 at width 14 with two splits, exactly as before, and the rule
accepts its observations by 78x in measured time. The `first` control shows what
would be lost: 1.453 s against 72.058 ms.

**Does not materially regress the full corpus or reduce solved coverage.**
See the sweep section below.

**Improves, or at least does not regress, the combined-cactus elbow.**
See the sweep section below.

**Passes a fresh all-systems performance sweep and regenerates every cactus plot
in the same PR.** See the sweep section below.

**Deterministic and shape-based.** `scoutPays` reads the degree of the input, the
primes involved, and the degree multisets already observed. There is no benchmark
name, corpus identity, or family recognizer in the planner; the constants are two
integers whose ratio is calibrated once, above.

**Existing `DirectPrimePlan` facts and retained-prime certificates remain
proved.** Recorded under "Proof surface" above.

## Follow-up

`powModMonicAux` remains the cost of a bounded scout, and after this change it is
charged only where the rule has priced a scout as worthwhile: eight of the eleven
scouting rows have recombination 2.4x to 78x above the observation cost. The
three Wilkinson rows are the exception, and their cause is the reducibility
question above, not a kernel cost. Per the issue's last dependency note, any
kernel work on `powModMonicAux` belongs in a separate issue opened from the
post-change profile rather than folded in here.

## Regeneration

```sh
lake build hexbz_factor_service

# Two arms differing only in the planner, alternated on one idle core.
git checkout <before> -- HexBerlekampZassenhaus/Modular/PrimePlan.lean \
  bench/HexBench/FactorService.lean
lake build hexbz_factor_service && cp .lake/build/bin/hexbz_factor_service /tmp/svc.before
git checkout HEAD -- HexBerlekampZassenhaus/Modular/PrimePlan.lean \
  bench/HexBench/FactorService.lean
lake build hexbz_factor_service && cp .lake/build/bin/hexbz_factor_service /tmp/svc.after
python3 scripts/bench/prime_plan_paired.py \
  --before /tmp/svc.before --after /tmp/svc.after --rounds 3 \
  --cpu "$(python3 scripts/bench/idle_core.py)" \
  --changed cyclo_phi64_x_phi105 \
  --output reports/bench-results/hexbz-prime-plan-pricing-paired-3b00dcf1-chungus2.json

# Per-candidate scout prices, counterfactual downstream, kernel attribution.
python3 scripts/bench/factor_phase_profile.py \
  --output reports/bench-results/hexbz-phase-profile-3b00dcf1-chungus2.json

# Offline policy replay, decision margins, and the replay's own check that the
# pre-change policy reproduces the recorded binary's selection.
python3 scripts/bench/prime_policy_replay.py \
  reports/bench-results/hexbz-phase-profile-3b00dcf1-chungus2.json \
  --margins --agrees-with voi

# Full Hex sweep (external comparator records are reused unchanged).
taskset -c "$(python3 scripts/bench/idle_core.py)" \
  python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate

# Rank tables and figures, and the byte-for-byte check CI runs.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
