# HexBZ support traversal: filtering before materializing

The head-forced classical recombination search used to build, at every leaf,
the reversed selected support, its list of lifted polynomials, and the lift
modulus `p ^ k`, and only then run the degree and trailing-coefficient filters
that reject almost all of those leaves.  This page records what that cost and
what removing it bought, against the baseline in
[reports/hexbz-cactus-elbow.md](hexbz-cactus-elbow.md).

## Revision and protocol

- Source revision `635854b7c4ba01cf81ccdcb40ed38e52cde2e7e8` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Baseline revision `c34ffbbbc16bd8c93274d96f555e22e1bb8868bc`, same host, same
  protocol, recorded by #9127.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Sweep: persistent warm service, ten-second per-call cutoff, median of five
  calls below one second and one call otherwise, early termination disabled.
  Measured protocol overhead 22.063 us per Hex call; reported times do not
  subtract it.

### Pinning, and why it is not CPU 0

The baseline pinned the measured service to CPU 0.  Three other agents were
running the same CPU-0-pinned protocol on this host throughout, so CPU 0 was
shared by up to three concurrent factorization services; sweeps taken there had
a median of 1.10x and outliers to 6.8x on rows that cannot have changed.  The
records below are pinned to CPU 70 instead, which was idle.

That substitution is validated rather than assumed.  Across the 354 corpus rows
outside the Swinnerton-Dyer families -- none of which this change can affect --
the new sweep divided by the baseline has median **1.0026** and p90 **1.0295**,
with no row above 100 us moving more than 10%.  CPU 70 is therefore
interchangeable with the baseline's CPU 0 for timing.  Allocation *shares* from
the sampling profiler are less robust to the substitution; see the caveat under
"Allocator time" below.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-factor-sweep-635854b7-hex-chungus2.json` | `99828b911190f4482c17434bde949f09f8e929df5ee775ec30f0fd4fdbd6b16e` |
| `reports/bench-results/hexbz-phase-profile-635854b7-chungus2.json` | `d69ddd1bc54d980a43b1ad28793f309b840177d3dc446a570fe8faaf6f9af70c` |
| `reports/bench-results/hexbz-factor-sampling-profiles-635854b7-chungus2.json` | `f0e71c356f2f8173ee710a02bd6d3f9db394898490144bd1af7fd4b32d39db65` |

The comparator record `hexbz-factor-sweep-aa68c920-chungus2.json` (FLINT, NTL,
PARI, both Isabelle extractions) is reused unchanged.

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
`lp_Hex_Hex_directSelectedFactors` ahead of the branch; the generated C for the
new `Hex.directLeaf` shows the reject path returning a shared constant having
allocated nothing.

For the two Swinnerton-Dyer representatives the counts are exact, and follow
from the definition rather than from measurement:

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

### Total factor time (sweep)

| instance | baseline | now | |
|---|---:|---:|---:|
| `sd5_shift1` | 96.670 ms | 69.739 ms | **0.721x** |
| `sd5_shift2` | 99.713 ms | 73.258 ms | **0.735x** |
| `sd5` | 106.911 ms | 79.159 ms | **0.740x** |
| `sd5_x_phi11` | 222.540 ms | 165.971 ms | **0.746x** |
| `sd5_x_phi45` | 514.710 ms | 409.586 ms | **0.796x** |
| `sd4_x_sd4shift1` | 25.091 ms | 21.400 ms | **0.853x** |
| `xpow24_minus1` (control) | 3.714 ms | 3.583 ms | 0.965x |
| `xpow105_minus1` | 84.464 ms | 82.707 ms | 0.979x |
| `xpow48_minus1` | 21.635 ms | 21.280 ms | 0.984x |
| `cyclo_phi41` (control) | 2.981 ms | 2.936 ms | 0.985x |
| `cyclo_phi385` | 455.841 ms | 450.096 ms | 0.987x |
| `wilkinson_48` | 29.732 ms | 29.615 ms | 0.996x |
| `cyclo_phi179` | 80.025 ms | 79.815 ms | 0.997x |
| `chebyshev_T24` (control) | 570.606 us | 570.085 us | 0.999x |
| `xpow120_minus1` | 523.812 ms | 527.521 ms | 1.007x |
| `wilkinson_56` | 40.396 ms | 41.081 ms | 1.017x |
| `legendre_P30` (control) | 8.333 ms | 8.496 ms | 1.020x |
| `randprod_21` (control) | 1.771 ms | 1.809 ms | 1.022x |
| `sd6` | 8.115 s | 8.444 s | 1.041x |

`sd6` is the row that reaches the subset budget: its head-forced search over 32
lifted factors declines on `defaultSubsetBudget` and the answer comes from a
later tier, so there is nothing here for this change to remove. It is a
single-call row under the repetition policy, and repeated sweeps put it between
1.017x and 1.041x, which is that call's variance rather than an effect.

The phase profiler agrees on the rows that moved -- 0.770x on `sd5`, 0.752x and
0.759x on its shifts, 0.788x on `sd5_x_phi11`, 0.896x on `sd4_x_sd4shift1` --
and puts every non-SD row within 2% of unchanged.

### Total factor time, independently, from the sampling profiles

The bounded prime walk (`Hex.classicalInput`) is untouched by this change, so
its absolute cost is the same in both records and the ratio of its sampled
shares recovers the change in total time without depending on either run's
absolute speed.

| instance | prime-walk share, before | after | implied total-time factor |
|---|---:|---:|---:|
| `sd5` | 8.94% | 12.03% | **0.743x** |
| `sd5_x_phi11` | 9.93% | 13.32% | **0.745x** |
| `wilkinson_56` | 35.04% | 35.86% | 0.977x |
| `cyclo_phi385` | 44.83% | 45.40% | 0.987x |
| `xpow120_minus1` | 12.33% | 12.39% | 0.995x |
| `cyclo_phi64_x_phi105` | 85.03% | 85.20% | 0.998x |
| `cyclo_phi179` | 18.61% | 18.60% | 1.001x |
| `xpow105_minus1` | 47.30% | 47.14% | 1.003x |
| `xpow48_minus1` | 27.92% | 27.58% | 1.012x |

Three independent measurements -- the sweep, the phase profiler, and this
ruler -- put `sd5` at 0.740x, 0.770x and 0.743x, and `sd5_x_phi11` at 0.746x,
0.788x and 0.745x.

### Traversal time

Rescaled by the ruler above, so both columns are fractions of the *same*
absolute time.  "Traversal outside the candidate test" is
`scanDirectCombinations` less `tryDirectCandidate` before and less
`Hex.directLeaf` after; both exclude the prefilters and the candidate work, so
the boundary is the same on each side.

| instance | before | after | |
|---|---:|---:|---:|
| `sd5` | 55.45% of total | 33.17% of the old total | **-40.2%** |
| `sd5_x_phi11` | 50.16% of total | 27.09% of the old total | **-46.0%** |
| `xpow48_minus1` | 0.53% | 0.13% | (already nothing) |
| every other profiled row | < 0.5% | < 0.5% | (already nothing) |

### Allocator time

Same rescaling, on the `allocation / free` leaf category of
`SPEC/profiling.md`, split by which allocator: glibc's, which is where GMP's
bignum limbs come from, and mimalloc, which is Lean's small-object path.

| | glibc / GMP | Lean small objects | all allocation |
|---|---:|---:|---:|
| `sd5` before | 57.24% | 10.81% | 69.10% |
| `sd5` after | 39.12% | 8.27% | 47.98% |
| | **-31.7%** | **-23.5%** | **-30.6%** |
| `sd5_x_phi11` before | 53.75% | 11.46% | 66.29% |
| `sd5_x_phi11` after | 36.80% | 8.95% | 46.27% |
| | **-31.5%** | **-21.9%** | **-30.2%** |

The split is the mechanism: `p ^ k` is bignum work and shows up in glibc's
allocator, the leaf list building is Lean constructor allocation and shows up
in mimalloc, and both fell.

**Caveat.**  Unlike the timing comparison, this one is not validated against
unchanged rows: the allocation share of `cyclo_phi64_x_phi105`, whose code path
this change does not touch at all, moves by -23% between the two records, and
`xpow48_minus1` by +6%.  Some of that is sampling variance and some is likely
the core substitution.  So treat these three figures as good to roughly ten
points, not to one.  The two allocation measurements that carry no such
uncertainty are the exact counts in the table above and the deterministic
counter below.

### Counted small-object allocations

`IO.getNumHeartbeats` counts one per Lean small-object allocation; array and
mpz payloads are allocated elsewhere and are not counted.  It is exactly
reproducible.  For the recombination phase alone:

| instance | before | after | |
|---|---:|---:|---:|
| `sd5` | 3,265,061 | 2,741,029 | **-16.0%** |
| `sd5_shift1` | 3,083,432 | 2,559,400 | **-17.0%** |
| `sd5_shift2` | 3,116,602 | 2,592,570 | **-16.8%** |
| `sd5_x_phi11` | 7,137,996 | 6,155,254 | **-13.8%** |
| `sd4_x_sd4shift1` | 573,372 | 525,702 | -8.3% |
| `xpow120_minus1` | 5,069,593 | 5,047,002 | -0.4% |
| `xpow48_minus1` | 239,881 | 239,607 | -0.1% |
| `cyclo_phi128_x_phi165` | 266,915 | 266,779 | -0.1% |
| `xpow105_minus1` | 248,907 | 248,913 | +0.0% |
| `cyclo_phi179` | 44,792 | 44,792 | 0.0% |

### Nothing else changed

Every recombination stage counter is identical before and after on all 21
profiled rows that reach the classical tier -- nodes, degree survivors,
trailing survivors, cheap-filter rejections, products materialized, recordable
candidates, exact divisions attempted, successful divisors and completed
cardinalities -- as is every returned factor-degree multiset.  Traversal nodes
by support size are unchanged by construction: level `k` of the head-forced
search visits `C(n - 1, k)` leaves, levels still run in ascending order, and
the search still commits the first exact divisor.

The counted recombination mirror in `bench/HexBench/FactorService.lean` was
moved to the new materialization point so it keeps measuring the code that
runs.  It agrees with the production `factorTrace` on leaf count, selected
prime, completed cardinalities and returned factor degrees on **367 of 367**
rows of the wider validation sample, and the phase-decomposed total tracks the
untimed end-to-end call with median ratio 0.988 and maximum 1.034.

## Where the remaining recombination cost is

On `sd5`, as shares of the new total:

| | share of new total |
|---|---:|
| `Hex.scanDirectCombinations` | 83.93% |
| ... `Hex.directLeaf` | 39.30% |
| ... ... `Hex.directCandidatePrefilter` | 24.53% |
| ... ... ... `Hex.directTrailingPrefilter` | 15.87% |
| ... ... ... ... `Hex.centeredModNat` | 9.12% |
| ... ... ... `Hex.directDegreePrefilter` | 8.61% |
| ... ... `Hex.directCandidate` | 5.88% |
| ... ... `Hex.exactQuotient?` | 8.69% |
| traversal outside the leaf | 44.63% |

The traversal that remains is two cons cells and one modular multiply per
internal node: `x :: selectedRev`, `x :: rejectedRev`, and
`selectedTrail * trail x % modulusInt`.  The leaf that remains is dominated by
the prefilters' own arithmetic on 93-bit integers; `Hex.centeredModNat` alone
is 9.1% of total, and it reconverts the modulus from `Nat` to `Int` on every
call.

So the residual cost of enumerating supports is **modular arithmetic on
multi-limb integers, not list representation**.  That is #9130's target --
reject impossible exact divisors over a word-sized prime -- and this profile is
its starting point.

## On the compact-index cursor this issue proposed

The issue proposed replacing the list traversal with a `SupportCursor` over a
compact array of increasing indices, and deleting the list traversal.  The
measurements do not support doing that, and the reason is worth recording
rather than rediscovering later.

The cost the issue identified is real and is now removed, but it was at the
*leaf*, not in the spine.  With the leaf guarded, the spine costs two
constructor allocations per internal node, and Lean's small-object allocator is
8.5% of `sd5`'s remaining time across the whole factorization, not just the
traversal.  A compact index array cannot beat that by much: in a pure
functional traversal the array has to be copied or threaded linearly at every
branch, whereas the present branch structure -- visit include, then exclude,
with the excluded prefix retained for the complement -- shares its spine
between sibling subtrees, which a copied array does not.

Against that bounded upside, an index-array cursor would require re-proving
`scanDirectCombinations_found` and `scanDirectCombinations_finds` -- the
head-forced coverage and first-success statements the classical completeness
proof consumes -- from scratch against a new enumeration invariant.  The
present change keeps both theorems, generalized from the canonical metadata to
any `Hex.SupportMeta`, and adds one equation, `Hex.directLeaf_eq`.

Precomputing per-factor metadata, the other half of the issue's proposal, *is*
implemented: `Hex.SupportMeta` records the modulus, the modulus as an integer,
and each lifted factor's degree and trailing coefficient, with proof fields
pinning the arrays to the factors elementwise and to their length.  It is
rebuilt once per subset-cardinality level rather than once per whole search:
on `sd5` that is 16 constructions against 32,768 leaves, and hoisting it
further would have to thread it through `findDirectHead` and
`searchDirectAux`, whose signatures the completeness proofs consume.

## Acceptance criteria

| criterion | outcome |
|---|---|
| candidate products not constructed before metadata-only filters finish | met; `Hex.directLeaf` guards on `directCandidatePrefilter`, confirmed in the generated C |
| allocation attributable to support traversal falls at least 40% on `sd5` and `sd5_x_phi11` | met on the traversal: -40.2% and -46.0%. Whole-factorization allocator time falls 30.6% and 30.2%, with the sampling caveat above |
| material end-to-end improvement on the SD family, no unexplained regression above 5% on low-width controls | met; 0.721x to 0.853x across the SD family, and every non-SD row within 4.1% (the largest, `sd6` at 1.041x, is a single-call eight-second row) |
| search order, budget behavior, factor results, proof coverage deterministic | met; all stage counters, completed cardinalities and factor degrees identical, no new `sorry` or `axiom` |
| full build, conformance, oracle and factorization tests pass | met; all oracles pass, `bz_trace_gate.py` checks 54 traces with 0 failures |
| fresh full Hex sweep and regenerated figures | recorded above; all 25 SVGs regenerated |

## Regeneration

```sh
lake build hexbz_factor_service

# Pin to an idle core and check the result against the baseline on rows this
# change cannot affect before trusting it.
taskset -c 70 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep.json

taskset -c 70 python3 scripts/bench/factor_phase_profile.py \
  --output /tmp/hexbz-phase-profile.json

python3 scripts/profile/factor_sampling_profile.py \
  --cpu 70 --output /tmp/hexbz-factor-sampling-profiles.json

python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144

uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
