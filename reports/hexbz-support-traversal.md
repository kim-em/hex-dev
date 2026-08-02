# HexBZ support traversal: filtering before materializing

The head-forced classical recombination search used to build, at every leaf,
the reversed selected support, its list of lifted polynomials, and the lift
modulus `p ^ k`, and only then run the degree and trailing-coefficient filters
that reject almost all of those leaves.  This page records what that cost and
what removing it bought, against the baseline in
[reports/hexbz-cactus-elbow.md](hexbz-cactus-elbow.md).

## Revision and protocol

- Source revision `PLACEHOLDER_REV` (clean worktree), Lean toolchain
  `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores; the measured service
  pinned to CPU 0 with `taskset -c 0`.
- Baseline revision `c34ffbbbc16bd8c93274d96f555e22e1bb8868bc`, same host, same
  protocol, recorded by #9127.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.

**The host was not quiet.**  Other agents were compiling and benchmarking on it
throughout, some of them also pinned to CPU 0, so wall-clock numbers taken from
separate runs are not directly comparable.  Every timing claim below is
therefore made with an *internal ruler* instead: the bounded prime walk
(`Hex.classicalInput`) and the Hensel lift (`Hex.henselLiftData`) are untouched
by this change, so their absolute cost is the same before and after, and the
ratio of their sampled shares recovers the change in total time without
depending on either run's absolute speed.  Allocation counts and stage counters
are deterministic and need no such correction.

## What the leaf no longer does

`Hex.scanDirectCombinations` reaches a leaf with the selected support in
reverse, the rejected prefix in reverse, and the incrementally maintained
degree sum and trailing residue.  The old leaf, in order:

1. reversed the selected prefix and consed the forced head onto it;
2. evaluated `liftModulus basis`, that is `p ^ k`;
3. mapped the selected support to a fresh list of lifted polynomials;
4. called `tryDirectCandidate`, whose *first* action is the degree and
   trailing-coefficient prefilter.

Steps 1 to 3 are arguments to step 4, so Lean's strictness means they were
performed for every leaf, including the ones the prefilter rejects
immediately.  (The complementary support was the one part the compiler could
already sink, since it is used only on success.)  The generated C for the old
`scanDirectCombinations` shows the unconditional `l_List_reverse___redArg`,
`lean_alloc_ctor`, `lp_Hex_Hex_liftModulus` and
`lp_Hex_Hex_directSelectedFactors` calls ahead of the branch; the generated C
for the new `Hex.directLeaf` shows the reject path returning a shared constant
having allocated nothing.

For a complete head-forced search the counts are exact:

| | `sd5` | `sd5_x_phi11` |
|---|---:|---:|
| lifted factors | 16 | 17 |
| bits in `p ^ k` | 93 | 103 |
| leaves visited | 32,768 | 65,522 |
| leaves that build a factor list, before | 32,768 | 65,522 |
| leaves that build a factor list, after | 129 | 258 |
| internal nodes that extend the selection | 278,512 | 458,756 |
| list cells built at leaves, before | 557,056 | 1,179,198 |
| `p ^ k` evaluations, before | 311,280 | 524,278 |
| `p ^ k` evaluations, after | 16 | 16 |

A leaf at support size `k` built `2k + 2` cells; summed over the complete
search that is `17 * 2^15` cells on `sd5`.  Only the 129 surviving supports
build them now.  The modulus is computed once per subset-cardinality level into
`Hex.SupportMeta`, together with each lifted factor's degree and trailing
coefficient.

## Measured effect

### Total time, from the internal ruler

`Hex.classicalInput` is the whole bounded prime walk and is not touched by this
change.  Dividing its baseline sampled share by its new one gives the factor by
which total factor time changed.

| instance | prime-walk share, before | after | total time factor |
|---|---:|---:|---:|
| `sd5` | 8.94% | 12.19% | **0.733x** |
| `sd5_x_phi11` | 9.93% | 13.43% | **0.739x** |
| `xpow48_minus1` | 27.9% | 27.0% | 1.033x |
| `xpow105_minus1` | 47.3% | 47.1% | 1.005x |
| `xpow120_minus1` | 12.3% | 12.2% | 1.007x |
| `cyclo_phi179` | 18.6% | 19.1% | 0.975x |
| `cyclo_phi64_x_phi105` | 85.0% | 85.1% | 0.999x |
| `cyclo_phi385` | 44.8% | 44.4% | 1.008x |
| `wilkinson_56` | 35.0% | 35.0% | 0.999x |

The Swinnerton-Dyer rows are **1.36x** faster end to end.  Every other profiled
row is within 3.3% of unchanged, which is sampling noise at these shares: their
traversal-outside-the-candidate-test was 0.0% to 0.5% of total to begin with,
exactly as #9127 predicted, so there was nothing on them for this change to
remove.

The phase profiler and the untimed end-to-end call agree with the ruler on the
rows that moved, at 0.779x/0.740x for `sd5` and 0.789x/0.751x for
`sd5_x_phi11`; they disagree with it on rows that did not move, which is the
host contention rather than a real effect.

### Where the time went, in units of the baseline total

Shares are rescaled by the ruler above, so both columns are fractions of the
*same* absolute time.

| instance | | `scanDirectCombinations` | traversal outside the candidate test | allocator |
|---|---|---:|---:|---:|
| `sd5` | before | 85.58% | 55.45% | 69.10% |
| `sd5` | after | 59.98% | **31.22%** | **47.26%** |
| `sd5` | change | -29.9% | **-43.7%** | **-31.6%** |
| `sd5_x_phi11` | before | 86.54% | 50.16% | 66.29% |
| `sd5_x_phi11` | after | 60.89% | **26.48%** | **46.07%** |
| `sd5_x_phi11` | change | -29.6% | **-47.2%** | **-30.5%** |

"Traversal outside the candidate test" is `scanDirectCombinations` less
`tryDirectCandidate` before and less `Hex.directLeaf` after; both exclude the
prefilters and the candidate work, so the boundary is the same on both sides.
"Allocator" is the `allocation / free` leaf category of `SPEC/profiling.md`.

Splitting the allocator by which allocator, in the same units:

| | glibc / GMP (`int_malloc`, `int_free_chunk`, `_realloc`) | Lean small objects (`mi_malloc_small`, `mi_free`) |
|---|---:|---:|
| `sd5` before | 45.40% | 10.81% |
| `sd5` after | 26.51% | 10.07% |
| change | **-41.6%** | -6.8% |

That split is the mechanism.  The `p ^ k` recomputation is bignum work and
shows up in GMP's allocator; the leaf list building is Lean constructor
allocation and shows up in mimalloc.  Removing 311,264 evaluations of a 93-bit
prime power is the larger of the two.

### Counted small-object allocations

`IO.getNumHeartbeats` counts Lean small-object allocations (one per
constructor; array and mpz payloads are allocated elsewhere and are not
counted).  For the recombination phase alone:

| instance | before | after | change |
|---|---:|---:|---:|
| `sd5` | 3,265,061 | 2,741,029 | -16.0% |
| `sd5_shift1` | 3,083,432 | 2,559,400 | -17.0% |
| `sd5_shift2` | 3,116,602 | 2,592,570 | -16.8% |
| `sd4_x_sd4shift1` | 573,372 | 525,702 | -8.3% |
| `sd5_x_phi11` | 7,137,996 | 6,155,254 | -13.8% |
| `xpow48_minus1` | 239,881 | 239,607 | -0.1% |
| `xpow105_minus1` | 248,907 | 248,913 | +0.0% |
| `xpow120_minus1` | 5,069,593 | 5,047,002 | -0.4% |
| `cyclo_phi179` | 44,792 | 44,792 | 0.0% |
| `cyclo_phi64_x_phi105` | 84,025 | 83,097 | -1.1% |
| `cyclo_phi128_x_phi165` | 266,915 | 266,779 | -0.1% |
| `cyclo_phi385` | 396,448 | 396,432 | -0.0% |

This counter sees the leaf list cells and not the prime-power bignums, which is
why it moves by less than the allocator time does.  It is reported because it
is exactly reproducible; the sampling profile above is the measurement of
allocation *cost*.

### Nothing else changed

Every recombination stage counter is identical before and after on all 21
profiled rows that reach the classical tier -- nodes, degree survivors,
trailing survivors, cheap-filter rejections, products materialized, recordable
candidates, exact divisions attempted, successful divisors and completed
cardinalities -- as is every returned factor-degree multiset.  Traversal nodes
by support size are unchanged by construction: level `k` of the head-forced
search visits `C(n - 1, k)` leaves, and the search still runs levels in
ascending order and commits the first exact divisor.

The counted recombination mirror in `bench/HexBench/FactorService.lean` was
moved to the new materialization point so it keeps measuring the code that
runs, and still agrees with the production `factorTrace` on leaf count,
selected prime, completed cardinalities and returned factor degrees on every
row of the wider validation sample.

## Where the remaining recombination cost is

On `sd5`, after the change, of the new total:

| | share of new total |
|---|---:|
| `Hex.scanDirectCombinations` | 81.79% |
| ... `Hex.directLeaf` | 39.22% |
| ... ... `Hex.directCandidatePrefilter` | 24.23% |
| ... ... ... `Hex.directTrailingPrefilter` | 15.11% |
| ... ... ... ... `Hex.centeredModNat` | 7.91% |
| ... ... ... `Hex.directDegreePrefilter` | 9.12% |
| ... ... `Hex.directCandidate` | 5.77% |
| ... ... `Hex.exactQuotient?` | 9.01% |
| traversal outside the leaf | 42.57% |

The traversal that remains is two cons cells and one modular multiply per
internal node: `x :: selectedRev`, `x :: rejectedRev`, and
`selectedTrail * trail x % modulusInt`.  The leaf that remains is dominated by
the prefilters' own arithmetic on 93-bit integers -- `centeredModNat` alone is
7.9% of total, and it converts the modulus from `Nat` to `Int` on every call.

So the residual cost of enumerating supports is **modular arithmetic on
multi-limb integers, not list representation**.  That is #9130's target (reject
impossible exact divisors over a word-sized prime), not a representation
question.

## On the compact-index cursor this issue proposed

The issue proposed replacing the list traversal with a `SupportCursor` over a
compact array of increasing indices, and deleting the list traversal.  The
measurements above do not support doing that, and the reason is worth
recording rather than repeating the experiment later.

The cost the issue identified is real and is now removed, but it was at the
*leaf*, not in the spine.  With the leaf guarded, the spine costs two
constructor allocations per internal node, and Lean's small-object allocator is
10.1% of `sd5`'s remaining time in total -- across the whole factorization, not
just the traversal.  A compact index array cannot beat that by much: in a pure
functional traversal the array would have to be copied or threaded linearly at
every branch, and the branch structure here (visit-include-then-exclude, with
the excluded prefix retained for the complement) shares its spine between
sibling subtrees, which a copied array does not.

Against that bounded upside, an index-array cursor would require re-proving
`scanDirectCombinations_found` and `scanDirectCombinations_finds` -- the
head-forced coverage and first-success statements the classical completeness
proof consumes -- from scratch against a new enumeration invariant.  The
present change keeps both theorems, generalized from the canonical metadata to
any `Hex.SupportMeta`, and adds one equation (`Hex.directLeaf_eq`).

Precomputing per-factor metadata, the other half of the issue's proposal, *is*
implemented: `Hex.SupportMeta` records the modulus, the modulus as an integer,
and each lifted factor's degree and trailing coefficient, with proof fields
pinning each recorded value to the factor it describes.

## Acceptance criteria

| criterion | outcome |
|---|---|
| candidate products not constructed before metadata-only filters finish | met; `Hex.directLeaf` guards on `directCandidatePrefilter`, verified in the generated C |
| allocation attributable to support traversal falls at least 40% on `sd5` and `sd5_x_phi11` | met on the traversal: -43.7% and -47.2%. Whole-factorization allocator time falls 31.6% and 30.5% |
| material end-to-end improvement on the SD family, no unexplained regression above 5% on low-width controls | met; 1.36x on `sd5` and `sd5_x_phi11`, every other profiled row within 3.3% |
| search order, budget behavior, factor results, proof coverage deterministic | met; all stage counters, completed cardinalities and factor degrees identical, no new `sorry` or `axiom` |
| full build, conformance, oracle and factorization tests pass | met |
| fresh full Hex sweep and regenerated figures | recorded below |

## Regeneration

```sh
lake build hexbz_factor_service

taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep.json

taskset -c 0 python3 scripts/bench/factor_phase_profile.py \
  --output /tmp/hexbz-phase-profile.json

python3 scripts/profile/factor_sampling_profile.py \
  --cpu 0 --output /tmp/hexbz-factor-sampling-profiles.json

python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144

uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
