# HexBZ recombination: testing candidate degrees against every retained prime

Classical recombination filters a selected support by its degree at the
selected prime and by the target degree. A genuine integer factor also reduces,
at every *other* good prime the planner retained, to a subproduct of that
prime's modular irreducible factors, so its degree must be a subset sum of that
prime's factor degrees too. This page records what the extra test rejects, what
it costs, and why it does not earn a place in production.

It is issue #9153's record and continues
[reports/hexbz-modular-obstruction.md](hexbz-modular-obstruction.md), whose
word-prime divisibility obstruction sits one stage later in the same leaf.

## The proof bridge

The cached Booleans are not self-authenticating, so the mathematics came first
and stands whatever the measurement says.

`Hex.directDegreeBits` is the `O(factors × degree)` subset-sum fold each probe
records. `HexBerlekampZassenhausMathlib.directDegreeBits_getElem?_iff` gives it
its meaning: for any index within the recorded range, the bit is true **exactly
when** some sub-multiset of the recorded modular factor degrees sums to that
index. This is an iff against the mathematical predicate, not a relation to the
certificate checker's separate `hasSubsetDegreeAux` procedure; the two
specifications are still stated independently.

`Hex.DirectPrimeProbe.Trial` says a probe *is* its own good-prime trial: its
recorded factorization is what the explicit trial at its candidate returned,
and its degree array and bitset were computed from that factorization.
`Hex.directPrimePlan?_probes_trial` proves it of every retained probe, not only
the selected one, so `directPrimePlan_probes_modPFactorization` and
`directPrimePlan_probes_facts` now supply the whole `ModPFactorization` bundle
and the whole `DirectPrimeFacts` contract for each. The former selected-only
theorems are corollaries at `plan.selected`.

`HexBerlekampZassenhausMathlib.exists_subMultiset_directFactorDegrees_of_dvd`
is the mathematics: at a good prime, an integer divisor of the input reduces to
a divisor of the modular image, its leading coefficient survives reduction so
its degree is preserved, and the modular image is the product of the recorded
irreducible factors, so its degree is a subset sum of the recorded degrees.
`reachableDegrees_of_dvd` composes that with the bitset specification, and
`directPrimePlan_probes_reachableDegrees` states the result over a whole plan:
**the degree of a genuine integer divisor of the input is marked reachable at
every trial the planner retained**, so a traversal that discards a support
whose degree is not marked discards no genuine factor.

No `axiom`, `sorry`, `native_decide` or unchecked oracle. The theorems are in
`HexBerlekampZassenhausMathlib/Modular/PrimePlan.lean`, which `ci.yml` builds.

## The counterfactual

`hexbz_factor_service --entry retainedPrimeProbe` mirrors the production
proposal peel run leaf for leaf -- same cardinality schedule, same budget, same
filters in the same order, same accepting step -- in four arms:

- **plain**: the production traversal.
- **counting**: at every leaf that passes the production selected-support
  degree check, each retained probe's bitset is read at that degree; the answer
  is recorded and discarded, so this arm visits exactly the leaves production
  visits and its counters are the counterfactual.
- **predicate**: a leaf no retained probe admits returns immediately, before
  the multi-limb trailing-residue test, the candidate product and exact
  division. The test is a short-circuiting scan that allocates nothing and
  records nothing, so this arm prices what production would run.
- **counting and acting**: both, used only for the equivalence check.

Both acting arms are compared against the plain arm on the peeled polynomials
themselves, the residual polynomial, the complementary support, the unconsumed
budget and the decline reason -- not on degree summaries, which two arms could
match while peeling different factors. They agree on all 392 rows, which is the
executable check on the no-false-rejection theorem.

`rejectableDegrees` answers the same question without reference to any
traversal: the degrees the selected prime's own factorization can form that
some retained prime cannot. When it is empty, no traversal over that lift can
be helped by this filter, whatever order it visits supports in.

`scripts/bench/retained_prime_probe.py` drives all 392 corpus rows and writes
one durable record; `--from-record ... ` regenerates the tables below.

### Protocol

- Source revision `1e00c8ee` plus this branch's bench driver, Lean toolchain
  `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, service pinned to
  CPU 70.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Six rounds per row, the four arms run in order on even rounds and in reverse
  order on odd rounds, so the round's cache warm-up does not land preferentially
  on one arm. Every span is in the record; the numbers below are medians of six.
- Record: `reports/bench-results/hexbz-retained-prime-probe.json`, SHA-256
  `955be2a23e03526d2a9c86b5e69f902a8f26d9e5d38cd2e11013eea9de991b42`.
- End-to-end times are quoted from the current published curve,
  `hexbz-factor-sweep-hex-d4b93a54-chungus2.json`.

### Noise floor, and why the counting arm is not the price

On the 347 rows with no retained probe every arm does the same work. Their
per-row medians give predicate/plain `1.0018`, p10--p90 `0.995`--`1.014`. So a
per-row difference under about 1.5% is not resolved here.

The counting arm is *not* a price for the filter and must not be read as one:
it allocates two arrays per tested leaf and sums a per-probe counter array up
the recursion. On the 43 rows that retain a prime and reject nothing it runs
`1.024` median and `1.091` worst against plain, while the predicate arm on the
same rows runs `1.0006` median and `1.0096` worst. Consulting the bitsets, done
the way production would, is free within the floor.

## What the retained primes reject

The planner retains at most one trial beyond the selected one, and only when a
bounded scout beat the first good prime and the split of the scouted winner
succeeded. Across the corpus:

| | rows |
|---|---|
| measured | 392 |
| reaching a modular plan | 392 |
| retaining a second good prime | 45 |
| retained pattern differs from the selected one | 14 |
| **retained prime can reject some selected-prime degree** | **2** |
| intersection removes a leaf the traversal visits | 2 |

The 12 rows whose retained pattern differs but rejects nothing are the reason
the filter is nearly always vacuous: a retained pattern containing 1s and 2s
reaches every subset sum the selected prime can form, so the intersection is
the selected prime's own reachable set. What makes the two exceptional rows
exceptional is a *parity* mismatch:

| row | selected prime and pattern | retained prime and pattern | rejectable degrees |
|---|---|---|---|
| `hoeij_M12_f132` | 13, twelve factors of degree 11 | 7, all degrees even | 11, 33, 55, 77, 99, 121 |
| `legendre_P26` | 59, `[2, 9, 9, 3, 3]` | 53, thirteen factors of degree 2 | 3, 5, 9, 11, 15, 17, 21, 23 |

On those two the rejection rate clears the issue's 20% bar comfortably:

| row | leaves | passing the degree check | passing every retained prime | removed |
|---|---|---|---|---|
| `hoeij_M12_f132` | 298 | 298 | 66 | 232 (**77.9%**) |
| `legendre_P26` | 25 | 25 | 13 | 12 (**48.0%**) |

`hoeij_M12_f132` is a Hoeij--Zimmermann row that reaches a plan, one of the
families the issue asked to report separately, so the rejection half of the
gate is met on a material row.

### The removed leaves are ones the trailing filter already rejects

They are not, however, leaves that cost anything downstream. On both rows the
acting arms and the plain arm construct the same number of candidates and
perform the same number of exact divisions:

| row | trailing survivors | candidates constructed | obstruction rejections | exact divisions |
|---|---|---|---|---|
| `hoeij_M12_f132` | 36 → 36 | 36 → 36 | 36 → 36 | 0 → 0 |
| `legendre_P26` | 0 → 0 | 0 → 0 | 0 → 0 | 0 → 0 |

The reason is visible level by level on `hoeij_M12_f132`. Its selected prime
has twelve degree-11 factors, so cardinality `c` gives candidate degree `11c`.

| level | leaves | passing the degree check | intersection | trailing survivors |
|---|---|---|---|---|
| cardinality 1 (degree 11) | 12 | 12 | 0 | 0 |
| cardinality 2 (degree 22) | 66 | 66 | 66 | 36 |
| cardinality 3 (degree 33) | 220 | 220 | 0 | 0 |

The retained prime rejects exactly the odd-degree levels, and the trailing
filter had already rejected every leaf of those levels. The level that produces
all 36 candidates is the even one, which the retained prime admits in full.

**Candidate and exact-division reductions across the whole corpus are zero.**
The most this filter can buy is the trailing test on leaves that build nothing.

## The reporting groups

Aggregates over each group the issue asked to report separately; per-row tables
for the named families follow. `--from-record` regenerates all of them.

| group | rows | retaining a prime | with a rejectable degree | leaves | passing the degree check | passing every retained prime | median predicate/plain | worst predicate/plain |
|---|---|---|---|---|---|---|---|---|
| sd5 and shifts | 15 | 7 | 0 | 20956 | 20956 | 20956 | 1.001 | 1.017 |
| SD products | 14 | 7 | 0 | 17288 | 17288 | 17288 | 1.001 | 1.006 |
| xpow48/105/120 | 3 | 2 | 0 | 1206 | 1206 | 1206 | 1.000 | 1.002 |
| cyclotomic products | 16 | 4 | 0 | 722 | 722 | 722 | 1.000 | 1.008 |
| Hoeij-Zimmermann | 10 | 10 | 1 | 36760 | 36760 | 36528 | 1.000 | 1.010 |
| Wilkinson | 15 | 12 | 0 | 336 | 336 | 336 | 0.999 | 1.002 |
| easy controls | 319 | 3 | 1 | 2770 | 2770 | 2758 | 1.002 | 1.053 |

Every Hoeij--Zimmermann row reaches a plan and every one retains a second
prime, which is the best case the corpus offers; nine of the ten still have
nothing to reject.

#### Hoeij-Zimmermann

| row | degree | retained primes | leaves | passing the degree check | passing every retained prime | rejectable degrees | plain | predicate |
|---|---|---|---|---|---|---|---|---|
| `hoeij_F190` | 190 | 1 | 1265 | 1265 | 1265 | 0 | 2879.5 µs | 2880.7 µs |
| `hoeij_F192` | 192 | 1 | 4656 | 4656 | 4656 | 0 | 8499.6 µs | 8511.8 µs |
| `hoeij_F256` | 256 | 1 | 8256 | 8256 | 8256 | 0 | 18287.9 µs | 18252.2 µs |
| `hoeij_F351` | 351 | 1 | 1891 | 1891 | 1891 | 0 | 7255.1 µs | 7253.0 µs |
| `hoeij_F630` | 630 | 1 | 5886 | 5886 | 5886 | 0 | 37511.1 µs | 37375.5 µs |
| `hoeij_M12_f132` | 132 | 1 | 298 | 298 | 66 | 6 | 4625.2 µs | 4547.7 µs |
| `hoeij_P7` | 384 | 1 | 3916 | 3916 | 3916 | 0 | 60372.7 µs | 60951.5 µs |
| `hoeij_S7` | 128 | 1 | 2080 | 2080 | 2080 | 0 | 3029.4 µs | 3052.1 µs |
| `hoeij_S8` | 256 | 1 | 8256 | 8256 | 8256 | 0 | 20121.7 µs | 20094.4 µs |
| `hoeij_S9` | 512 | 1 | 256 | 256 | 256 | 0 | 1080.7 µs | 1083.8 µs |

#### sd5 and shifts

| row | degree | retained primes | leaves | passing the degree check | passing every retained prime | rejectable degrees | plain | predicate |
|---|---|---|---|---|---|---|---|---|
| `sd2` | 4 | 0 | 3 | 3 | 3 | 0 | 4.3 µs | 4.3 µs |
| `sd2_shift1` | 4 | 0 | 3 | 3 | 3 | 0 | 3.8 µs | 3.8 µs |
| `sd3` | 8 | 0 | 14 | 14 | 14 | 0 | 17.0 µs | 16.9 µs |
| `sd3_shift1` | 8 | 0 | 14 | 14 | 14 | 0 | 5.3 µs | 5.4 µs |
| `sd3_shift2` | 8 | 0 | 14 | 14 | 14 | 0 | 5.4 µs | 5.4 µs |
| `sd4` | 16 | 0 | 92 | 92 | 92 | 0 | 48.6 µs | 48.4 µs |
| `sd4_shift1` | 16 | 0 | 92 | 92 | 92 | 0 | 46.3 µs | 46.3 µs |
| `sd4_shift3` | 16 | 0 | 92 | 92 | 92 | 0 | 46.8 µs | 46.8 µs |
| `sd5` | 32 | 1 | 696 | 696 | 696 | 0 | 540.8 µs | 541.7 µs |
| `sd5_shift1` | 32 | 1 | 696 | 696 | 696 | 0 | 511.6 µs | 512.3 µs |
| `sd5_shift2` | 32 | 1 | 696 | 696 | 696 | 0 | 531.9 µs | 532.6 µs |
| `sd6` | 64 | 1 | 5488 | 5488 | 5488 | 0 | 5497.1 µs | 5514.8 µs |
| `sd6_shift1` | 64 | 1 | 5488 | 5488 | 5488 | 0 | 5600.1 µs | 5595.5 µs |
| `sd6_shift5` | 64 | 1 | 5488 | 5488 | 5488 | 0 | 5344.3 µs | 5348.6 µs |
| `sd7` | 128 | 1 | 2080 | 2080 | 2080 | 0 | 3004.4 µs | 3022.6 µs |

#### SD products

| row | degree | retained primes | leaves | passing the degree check | passing every retained prime | rejectable degrees | plain | predicate |
|---|---|---|---|---|---|---|---|---|
| `sd2_x_phi12` | 8 | 0 | 8 | 8 | 8 | 0 | 15.0 µs | 15.1 µs |
| `sd2_x_sd2shift1` | 8 | 0 | 8 | 8 | 8 | 0 | 9.8 µs | 9.7 µs |
| `sd3_x_phi15` | 16 | 0 | 17 | 17 | 17 | 0 | 25.9 µs | 25.9 µs |
| `sd3_x_phi24` | 16 | 0 | 92 | 92 | 92 | 0 | 64.8 µs | 64.3 µs |
| `sd3_x_sd3shift1` | 16 | 0 | 92 | 92 | 92 | 0 | 69.9 µs | 70.1 µs |
| `sd4_x_phi17` | 32 | 0 | 42 | 42 | 42 | 0 | 39.7 µs | 39.9 µs |
| `sd4_x_phi35` | 40 | 1 | 62 | 62 | 62 | 0 | 126.7 µs | 126.9 µs |
| `sd4_x_sd4shift1` | 32 | 1 | 696 | 696 | 696 | 0 | 501.1 µs | 500.6 µs |
| `sd5_x_phi11` | 42 | 1 | 152 | 152 | 152 | 0 | 167.9 µs | 168.8 µs |
| `sd5_x_phi45` | 56 | 1 | 196 | 196 | 196 | 0 | 299.6 µs | 298.2 µs |
| `sd5_x_sd5shift1` | 64 | 1 | 5488 | 5488 | 5488 | 0 | 5234.1 µs | 5224.8 µs |
| `sd6_x_phi105` | 112 | 1 | 7806 | 7806 | 7806 | 0 | 10854.9 µs | 10861.5 µs |
| `sd6_x_phi13` | 76 | 0 | 549 | 549 | 549 | 0 | 682.1 µs | 680.7 µs |
| `sd6_x_sd6shift1` | 128 | 1 | 2080 | 2080 | 2080 | 0 | 2875.8 µs | 2884.4 µs |

#### xpow48/105/120

| row | degree | retained primes | leaves | passing the degree check | passing every retained prime | rejectable degrees | plain | predicate |
|---|---|---|---|---|---|---|---|---|
| `xpow48_minus1` | 48 | 1 | 145 | 145 | 145 | 0 | 1092.6 µs | 1094.4 µs |
| `xpow105_minus1` | 105 | 1 | 96 | 96 | 96 | 0 | 4361.3 µs | 4358.8 µs |
| `xpow120_minus1` | 120 | 0 | 965 | 965 | 965 | 0 | 9090.2 µs | 9092.8 µs |

#### Wilkinson

Every Wilkinson residual succeeds at cardinality one, so the whole family
visits one leaf per lifted factor and the filter has nothing to work with.

| row | degree | retained primes | leaves | passing the degree check | passing every retained prime | rejectable degrees | plain | predicate |
|---|---|---|---|---|---|---|---|---|
| `wilkinson_4` | 4 | 0 | 4 | 4 | 4 | 0 | 10.3 µs | 10.2 µs |
| `wilkinson_6` | 6 | 0 | 6 | 6 | 6 | 0 | 17.1 µs | 17.1 µs |
| `wilkinson_8` | 8 | 0 | 8 | 8 | 8 | 0 | 25.1 µs | 25.0 µs |
| `wilkinson_10` | 10 | 1 | 10 | 10 | 10 | 0 | 40.8 µs | 40.7 µs |
| `wilkinson_12` | 12 | 1 | 12 | 12 | 12 | 0 | 52.5 µs | 52.5 µs |
| `wilkinson_14` | 14 | 1 | 14 | 14 | 14 | 0 | 77.5 µs | 77.5 µs |
| `wilkinson_16` | 16 | 1 | 16 | 16 | 16 | 0 | 103.1 µs | 103.0 µs |
| `wilkinson_18` | 18 | 1 | 18 | 18 | 18 | 0 | 132.9 µs | 132.9 µs |
| `wilkinson_20` | 20 | 1 | 20 | 20 | 20 | 0 | 165.4 µs | 165.0 µs |
| `wilkinson_24` | 24 | 1 | 24 | 24 | 24 | 0 | 245.7 µs | 241.7 µs |
| `wilkinson_28` | 28 | 1 | 28 | 28 | 28 | 0 | 339.7 µs | 340.4 µs |
| `wilkinson_32` | 32 | 1 | 32 | 32 | 32 | 0 | 444.2 µs | 442.6 µs |
| `wilkinson_40` | 40 | 1 | 40 | 40 | 40 | 0 | 720.0 µs | 719.4 µs |
| `wilkinson_48` | 48 | 1 | 48 | 48 | 48 | 0 | 1056.9 µs | 1057.4 µs |
| `wilkinson_56` | 56 | 1 | 56 | 56 | 56 | 0 | 1438.6 µs | 1438.2 µs |

## Verdict: no-go

Both halves of the issue's gate are met on their own terms. The intersection
removes 77.9% of the post-degree-check leaves on `hoeij_M12_f132`, well above
the 20% bar and on one of the families the issue names. And the prototyped cost
is favourable: the predicate arm's worst per-row regression anywhere in the
corpus is 0.96%, inside the 1.5% floor, and it is faster on the two rows that
have something to reject -- `hoeij_M12_f132` 4625.2 µs → 4547.7 µs (−1.7%) and
`legendre_P26` 24.4 µs → 21.0 µs (−14.0%), both with cleanly separated spans.

What fails is the acceptance criterion those two thresholds exist to serve:
"candidate/leaves reductions translate into a material improvement on the rows
that justified the change". There are no candidate or leaf reductions to
translate -- every leaf the filter rejects is a leaf the existing trailing
filter already rejects, so nothing downstream of the leaf changes anywhere in
the corpus. And the peel run is a small part of the rows in question:

| row | end-to-end | proposal peel | peel saving | as a share of end-to-end |
|---|---|---|---|---|
| `hoeij_M12_f132` | 960.894 ms | 4.625 ms (0.48%) | 77.5 µs | **0.008%** |
| `legendre_P26` | 6.913 ms | 0.024 ms (0.35%) | 3.4 µs | **0.049%** |

Neither figure is measurable in the sweep protocol the issue requires a
production PR to run: the published curve's own repeat-to-repeat floor is
around 1%, two orders of magnitude above the effect. A production change here
would be a real code and proof change -- the predicate belongs in the traversal
data, and the head-forced tier's completeness proofs quantify over it -- bought
with a fresh full Hex sweep and a regeneration of every cactus and
runtime-by-degree figure, in exchange for an improvement no sweep could show.

So: nothing is installed in production. The proof bridge is landed, and the
counterfactual is committed, so the gate can be re-run in one command against
any future planner.

## What would change the answer

The filter is vacuous because of what the planner retains, not because the
mathematics is weak. Three observations for whoever revisits this:

- The planner keeps at most one other trial, and keeps it for having *lost* a
  lexicographic score whose first key is the subset cost. Nothing in that score
  rewards a degree pattern that is *complementary* to the selected one. A
  planner that deliberately retained a prime with a coarse pattern -- all
  degrees even, say -- would make this filter bite on far more than two rows.
  `rejectableDegrees` in the record is the cheap way to measure such a change:
  it is a property of the two degree multisets alone, and needs no traversal.
- Even then the filter would have to reject leaves the trailing test lets
  through, not leaves it already stops. On `hoeij_M12_f132` the two filters
  reject the same set, and the cheaper one runs first only by accident of the
  candidate-degree arithmetic. A version worth installing would have to remove
  candidate constructions or exact divisions, which this one never does.
- The proposal peel is well under 1% of the end-to-end time on both rows that
  the filter touches. Anything aimed at those rows should be aimed at where
  their time actually goes.

## Reproducing

```bash
lake build hexbz_factor_service
taskset -c 70 python3 scripts/bench/retained_prime_probe.py \
    --output reports/bench-results/hexbz-retained-prime-probe.json
# regenerate the tables above from the committed record
python3 scripts/bench/retained_prime_probe.py --output /dev/null \
    --from-record reports/bench-results/hexbz-retained-prime-probe.json
```

The driver exits non-zero if any row's acting arms disagree with its plain arm
on the peeled polynomials, the residual, the complementary support, the
unconsumed budget or the decline reason.
