# HexBZ recombination: testing candidate degrees against every retained prime

Classical recombination filters a selected support by its degree at the
selected prime and by the target degree. A genuine integer factor also reduces,
at every *other* good prime the planner retained, to a subproduct of that
prime's modular irreducible factors, so its degree must be a subset sum of that
prime's factor degrees too. This page records what the extra test would reject,
what consulting it costs, and why it does not earn a place in production.

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
`reachableDegrees_of_dvd` composes that with the bitset specification into the
no-false-rejection statement: **a probe that is its own trial marks the degree
of every genuine integer divisor of the input as reachable**, so a traversal
that discards a support whose degree is not marked discards no genuine factor.

No `axiom`, `sorry`, `native_decide` or unchecked oracle. The theorems are in
`HexBerlekampZassenhausMathlib/Modular/PrimePlan.lean`, which `ci.yml` builds.

## The counterfactual

`hexbz_factor_service --entry retainedPrimeProbe` mirrors the production
proposal peel run leaf for leaf -- same cardinality schedule, same budget, same
filters in the same order, same accepting step -- in three arms:

- **plain**: the production traversal.
- **counting**: at every leaf that passes the production selected-support
  degree check, each retained probe's bitset is read at that degree; the answer
  is recorded and discarded, so this arm visits exactly the leaves production
  visits and its counters are the counterfactual.
- **acting**: the same, except a leaf no retained probe admits returns
  immediately, before the multi-limb trailing-residue test, the candidate
  product and exact division. This is the prototype.

The acting arm's peeled factor degrees, residual degree and decline reason are
compared against the plain arm's on every row; they agree everywhere, which is
the executable check on the no-false-rejection theorem.

`rejectableDegrees` answers the same question without reference to any
traversal: the degrees the selected prime's own factorization can form that
some retained prime cannot. When it is empty, no traversal over that lift can
be helped by this filter, whatever order it visits supports in.

`scripts/bench/retained_prime_probe.py` drives all 392 corpus rows and writes
one durable record.

### Protocol

- Source revision `4d23c458` plus this branch's bench driver, Lean toolchain
  `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores, service pinned to
  CPU 70.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Six rounds per row, the three arms run in order on even rounds and in reverse
  order on odd rounds, so the round's cache warm-up does not land preferentially
  on one arm. Every span is in the record; the numbers below are medians of six.
- Record: `reports/bench-results/hexbz-retained-prime-probe.json`, SHA-256
  `1dee4dbff4c830ac5f5ea58b037c88b3e268f37a9e74a7f8031e08970af9e00d`.

### Noise floor

On the 347 rows with no retained probe the three arms do the same work. Their
per-row medians give counting/plain `1.0105` and acting/plain `1.0099`, with a
p10--p90 spread of about `0.998`--`1.049`. So a per-row difference under about
1% is not resolved here, and the residual 1% is itself the prototype's own
overhead: `retainedTests` allocates two small arrays per leaf even when there
is nothing to consult. Every cost below is therefore an upper bound on what a
production implementation would pay.

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
acting arm and the plain arm construct the same number of candidates and
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

## What it costs

| row | plain | acting | ratio |
|---|---|---|---|
| `sd5_shift1` | 494.2 µs | 541.0 µs | 1.095 |
| `sd5` | 516.5 µs | 562.2 µs | 1.088 |
| `sd4_x_sd4shift1` | 497.4 µs | 539.9 µs | 1.085 |
| `sd6_shift5` | 5371.7 µs | 5784.1 µs | 1.077 |
| `sd5_x_sd5shift1` | 5072.3 µs | 5455.2 µs | 1.075 |
| `legendre_P30` | 56.0 µs | 60.9 µs | 1.086 |
| `wilkinson_56` | 1434.7 µs | 1437.9 µs | 1.002 |
| `xpow105_minus1` | 4365.8 µs | 4373.2 µs | 1.002 |
| **`hoeij_M12_f132`** | **4561.5 µs** | **4497.8 µs** | **0.986** |
| **`legendre_P26`** | **24.1 µs** | **22.4 µs** | **0.931** |

The cost tracks leaves per unit of leaf work. The Swinnerton-Dyer rows visit
hundreds or thousands of cheap leaves and pay 7.5--9.5%; `xpow105_minus1` and
Wilkinson visit few expensive leaves and pay 0.2%. The median over the 43 rows
that retain a prime and reject nothing is 1.026 against the 1.010 floor.

The two rows that gain, gain 1.4% and 6.9%, the first of which is the same
order as the floor bias, though its six spans (4.494--4.527 ms acting against
4.547--4.594 ms plain) do not overlap.

Rows with no retained probe are unaffected: `xpow120_minus1` 8988.2 µs →
9017.3 µs, `cyclo_phi128_x_phi165` 6953.3 µs → 6952.2 µs.

## Verdict: no-go

The issue's gate is a conjunction -- at least 20% of the post-degree-check
leaves removed on a material row **and** a favourable measured net cost. The
first half is met on `hoeij_M12_f132`. The second is not, and not marginally:

- The filter removes no candidate construction and no exact division anywhere
  in the corpus, because every leaf it rejects is a leaf the existing trailing
  filter already rejects. Its whole possible benefit is one multi-limb trailing
  test per rejected leaf, measured at −1.4% on one 4.6 ms row and −6.9% on one
  24 µs row.
- Against that, every post-degree-check leaf on the other 43 rows that retain a
  prime pays a lookup, costing up to 9.5% on the Swinnerton-Dyer rows -- above
  the issue's own 5% per-row regression tolerance.

A leaner production implementation would narrow the cost side: the prototype
allocates per leaf where production would short-circuit, and the whole test can
be skipped when no probe is retained, which is 347 of 392 rows. It cannot widen
the benefit side, which is bounded above by the trailing tests on 232 leaves of
one row and 12 leaves of another. So the conclusion does not depend on tuning
the prototype.

Nothing is installed in production. The proof bridge is landed, and the
counterfactual is committed, so the gate can be re-run in one command.

## What would change the answer

The filter is vacuous because of what the planner retains, not because the
mathematics is weak. Two observations for whoever revisits this:

- The planner keeps at most one other trial, and keeps it for having *lost* a
  lexicographic score whose first key is the subset cost. Nothing in that score
  rewards a degree pattern that is *complementary* to the selected one. A
  planner that deliberately retained a prime with a coarse pattern -- all
  degrees even, say -- would make this filter bite on far more than two rows.
  `rejectableDegrees` in the record is the cheap way to measure such a change:
  it is a property of the two degree multisets alone.
- Even then the filter would have to reject leaves the trailing test lets
  through, not leaves it already stops. On `hoeij_M12_f132` the two filters
  reject the same set, and the cheaper one runs first only by accident of the
  candidate-degree arithmetic.

## Reproducing

```bash
lake build hexbz_factor_service
taskset -c 70 python3 scripts/bench/retained_prime_probe.py \
    --output reports/bench-results/hexbz-retained-prime-probe.json
```

The driver exits non-zero if any row's acting arm disagrees with its plain arm
on the peeled factors, the residual degree or the decline reason.
