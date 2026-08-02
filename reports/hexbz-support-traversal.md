# HexBZ support traversal: filtering before materializing

The head-forced classical recombination search used to build, at every leaf,
the reversed selected support, its list of lifted polynomials, and the lift
modulus `p ^ k`, and only then run the degree and trailing-coefficient filters
that reject almost all of those leaves.  This page records what that cost and
what removing it bought, against the baseline in
[reports/hexbz-cactus-elbow.md](hexbz-cactus-elbow.md).

## Revision and protocol

- Source revision `f8477abd0639062e1f81e9eaa62dc429631706d6` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Two baselines, same host and protocol. `c34ffbbb` is #9127's elbow record and
  is the only committed sampling profile. `7200f7d1` is main's record after
  #9136's canonical Hensel lift, which landed while this was in review; it is
  the one that isolates *this* change, and the sweep is reported against both.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Sweep: persistent warm service, ten-second per-call cutoff, median of five
  calls below one second and one call otherwise, early termination disabled.
  Measured protocol overhead 22.033 us per Hex call; reported times do not
  subtract it.

### Pinning, and why it is not CPU 0

The baseline pinned the measured service to CPU 0.  Three other agents were
running the same CPU-0-pinned protocol on this host throughout, so CPU 0 was
shared by up to three concurrent factorization services; sweeps taken there had
a median of 1.10x and outliers to 6.8x on rows that cannot have changed.  The
records below are pinned to CPU 70 instead, which was idle.

That substitution is validated rather than assumed.  Across the 354 corpus rows
outside the Swinnerton-Dyer families -- none of which this change can affect --
the new sweep divided by `7200f7d1` has median **0.9899** and p90 **1.0190**,
with no row above 100 us moving more than 10%.  CPU 70 is therefore
interchangeable with the baseline's CPU 0 for timing.  Allocation *shares* from
the sampling profiler are less robust to the substitution; see the caveat under
"Allocator time" below.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-factor-sweep-f8477abd-hex-chungus2.json` | `6fb6e0a5d2e4d67db59ea804e5030789419438f723048493da1a1806a0c63dda` |
| `reports/bench-results/hexbz-phase-profile-f8477abd-chungus2.json` | `1013de979034a7b4dd0554df97a4ed206da56457c9586106d12d3e70414cd67e` |
| `reports/bench-results/hexbz-factor-sampling-profiles-f8477abd-chungus2.json` | `8def3c0f4aa3d431dfb85ecaa3d3638790c55dd902b48c27fd301c5701aab89e` |

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
| `p ^ k` evaluations, after | 16 | 17 |

A leaf at support size `k` built `2k + 2` cells; summed over the complete search
that is `17 * 2^15` cells on `sd5`.  Only the 129 surviving supports build them
now.  The `sd5` column is exact for its whole search, which is one head search
over the 15-element tail running cardinalities 0 through 15.  `sd5_x_phi11`
answers with two divisors: a head search over its 16-element tail that
completes cardinalities 0 through 14 and succeeds in 15, then a one-factor
residual search that succeeds at cardinality 0; its column counts the first
search, which is 65,519 of its 65,522 leaves.

The modulus is computed once per subset-cardinality level into
`Hex.SupportMeta`, together with each lifted factor's degree and trailing
coefficient, which is why the last row is the number of levels entered rather
than a function of the leaf count.

## Measured effect

### Total factor time (sweep)

The middle columns divide by `7200f7d1`, so they are this change alone.  The
last column divides by the #9127 elbow baseline, so it is the cumulative
movement since that record and also contains #9136.

| instance | `7200f7d1` | now | this change | vs `c34ffbbb` |
|---|---:|---:|---:|---:|
| `sd5_shift1` | 97.735 ms | 66.864 ms | **0.684x** | 0.692x |
| `sd5_shift2` | 102.167 ms | 70.184 ms | **0.687x** | 0.704x |
| `sd5` | 108.383 ms | 77.927 ms | **0.719x** | 0.729x |
| `sd5_x_phi11` | 227.060 ms | 166.576 ms | **0.734x** | 0.749x |
| `sd5_x_phi45` | 524.304 ms | 409.671 ms | **0.781x** | 0.796x |
| `sd4_x_sd4shift1` | 25.073 ms | 21.300 ms | **0.850x** | 0.849x |
| `sd6` | 8.711 s | 8.367 s | 0.960x | 1.031x |
| `xpow48_minus1` | 21.852 ms | 21.052 ms | 0.963x | 0.973x |
| `randprod_21` (control) | 1.801 ms | 1.746 ms | 0.970x | 0.986x |
| `chebyshev_T24` (control) | 568.403 us | 552.299 us | 0.972x | 0.968x |
| `legendre_P30` (control) | 8.381 ms | 8.290 ms | 0.989x | 0.995x |
| `cyclo_phi41` (control) | 2.934 ms | 2.910 ms | 0.992x | 0.976x |
| `cyclo_phi179` | 75.533 ms | 74.967 ms | 0.993x | 0.937x |
| `xpow24_minus1` (control) | 3.583 ms | 3.568 ms | 0.996x | 0.961x |
| `xpow120_minus1` | 527.749 ms | 527.227 ms | 0.999x | 1.007x |
| `xpow105_minus1` | 81.525 ms | 81.724 ms | 1.002x | 0.968x |
| `cyclo_phi385` | 431.827 ms | 438.628 ms | 1.016x | 0.962x |
| `wilkinson_48` | 28.430 ms | 28.904 ms | 1.017x | 0.972x |
| `wilkinson_56` | 38.793 ms | 39.740 ms | 1.024x | 0.984x |

The Swinnerton-Dyer family is **0.684x to 0.850x**.  The largest movement on
any other row is 2.4%, and across the 354 corpus rows outside the two
Swinnerton-Dyer families the median is 0.9899 with p90 1.0190.

`sd6` is the row that reaches the subset budget: its head-forced search over 32
lifted factors declines on `defaultSubsetBudget` and the answer comes from a
later tier, so there is nothing here for this change to remove.  It is a
single-call row under the repetition policy and repeated sweeps put it between
0.960x and 1.041x, which is that call's variance rather than an effect.

The phase profiler agrees on the rows that moved, and puts every non-SD row
within 2% of unchanged.

### Total factor time, independently, from the sampling profiles

The bounded prime walk (`Hex.classicalInput`) is untouched by this change, so
its absolute cost is the same in both records and the ratio of its sampled
shares recovers the change in total time without depending on either run's
absolute speed.

| instance | prime-walk share, before | after | implied total-time factor |
|---|---:|---:|---:|
| `sd5` | 8.94% | 12.16% | **0.735x** |
| `sd5_x_phi11` | 9.93% | 13.45% | **0.738x** |
| `cyclo_phi179` | 18.61% | 20.04% | 0.929x |
| `cyclo_phi385` | 44.83% | 47.27% | 0.948x |
| `wilkinson_56` | 35.04% | 36.98% | 0.948x |
| `cyclo_phi64_x_phi105` | 85.03% | 86.13% | 0.987x |
| `xpow105_minus1` | 47.30% | 47.61% | 0.993x |
| `xpow120_minus1` | 12.33% | 12.39% | 0.995x |
| `xpow48_minus1` | 27.92% | 28.03% | 0.996x |

The only committed sampling profile is `c34ffbbb`'s, so this table spans #9136
as well: the movement on `cyclo_phi179`, `cyclo_phi385` and `wilkinson_56` is
that change's canonical Hensel lift, not this one, and the sweep table above
confirms those rows are flat against `7200f7d1`.  On the two rows this change
moves, Hensel lifting is 1.9% and 1.4% of total, so 0.735x and 0.738x are this
change to within a couple of points.

The sweep, the phase profiler and this ruler put `sd5` at 0.719x, 0.740x and
0.735x, and `sd5_x_phi11` at 0.734x, 0.752x and 0.738x.

### Traversal time

Rescaled by the ruler above, so both columns are fractions of the *same*
absolute time.  "Traversal outside the candidate test" is
`scanDirectCombinations` less `tryDirectCandidate` before and less
`Hex.directLeaf` after; both exclude the prefilters and the candidate work, so
the boundary is the same on each side.

| instance | before | after | |
|---|---:|---:|---:|
| `sd5` | 55.45% of total | 32.03% of the old total | **-42.2%** |
| `sd5_x_phi11` | 50.16% of total | 26.64% of the old total | **-46.9%** |
| `xpow48_minus1` | 0.53% | 0.14% | (already nothing) |
| every other profiled row | < 0.5% | < 0.5% | (already nothing) |

### Allocator time

Same rescaling, on the `allocation / free` leaf category of
`SPEC/profiling.md`, split by which allocator: glibc's, which is where GMP's
bignum limbs come from, and mimalloc, which is Lean's small-object path.

| | glibc / GMP | Lean small objects | all allocation |
|---|---:|---:|---:|
| `sd5` before | 57.24% | 10.81% | 69.10% |
| `sd5` after | 38.67% | 8.46% | 47.94% |
| | **-32.4%** | **-21.7%** | **-30.6%** |
| `sd5_x_phi11` before | 53.75% | 11.46% | 66.29% |
| `sd5_x_phi11` after | 36.99% | 8.22% | 45.91% |
| | **-31.2%** | **-28.2%** | **-30.7%** |

The split is the mechanism: `p ^ k` is bignum work and shows up in glibc's
allocator, the leaf list building is Lean constructor allocation and shows up
in mimalloc, and both fell.

**Caveat.**  Unlike the timing comparison, this one is not validated against
unchanged rows: the allocation share of `cyclo_phi64_x_phi105`, whose code path
this change does not touch at all, moves by -21% between the two records, and
`xpow120_minus1` by +6%.  Some of that is sampling variance and some is likely
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
| `Hex.scanDirectCombinations` | 83.95% |
| ... `Hex.directLeaf` | 40.39% |
| ... ... `Hex.directCandidatePrefilter` | 25.71% |
| ... ... ... `Hex.directTrailingPrefilter` | 16.57% |
| ... ... ... ... `Hex.centeredModNat` | 9.23% |
| ... ... ... `Hex.directDegreePrefilter` | 9.13% |
| ... ... `Hex.directCandidate` | 5.74% |
| ... ... `Hex.exactQuotient?` | 8.84% |
| traversal outside the leaf | 43.56% |

The traversal that remains is two cons cells and one modular multiply per
internal node: `x :: selectedRev`, `x :: rejectedRev`, and
`selectedTrail * trail x % modulusInt`.  The leaf that remains is dominated by
the prefilters' own arithmetic on 93-bit integers; `Hex.centeredModNat` alone
is 9.2% of total, and it reconverts the modulus from `Nat` to `Int` on every
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
| allocation attributable to support traversal falls at least 40% on `sd5` and `sd5_x_phi11` | met on the traversal: -42.2% and -46.9%. Whole-factorization allocator time falls 30.6% and 30.7%, with the sampling caveat above |
| material end-to-end improvement on the SD family, no unexplained regression above 5% on low-width controls | met; 0.684x to 0.850x across the SD family, and no other row moves more than 2.4% |
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
