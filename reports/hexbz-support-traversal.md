# HexBZ support traversal: filtering before materializing

The head-forced classical recombination search used to build, at every leaf,
the reversed selected support, its list of lifted polynomials, and the lift
modulus `p ^ k`, and only then run the degree and trailing-coefficient filters
that reject almost all of those leaves.  This page records what that cost and
what removing it bought, against the baseline in
[reports/hexbz-cactus-elbow.md](hexbz-cactus-elbow.md).

## Revision and protocol

- Source revision `9410326790518e1563174dce21345efc2c427105` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Baseline revision `c34ffbbbc16bd8c93274d96f555e22e1bb8868bc`, same host, same
  protocol, recorded by #9127.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
- Sweep: persistent warm service, ten-second per-call cutoff, median of five
  calls below one second and one call otherwise, early termination disabled.
  Measured protocol overhead 22.273 us per Hex call; reported times do not
  subtract it.

### Pinning, and why it is not CPU 0

The baseline pinned the measured service to CPU 0.  Three other agents were
running the same CPU-0-pinned protocol on this host throughout, so CPU 0 was
shared by up to three concurrent factorization services; sweeps taken there had
a median of 1.10x and outliers to 6.8x on rows that cannot have changed.  The
records below are pinned to CPU 70 instead, which was idle.

That substitution is validated rather than assumed.  Across the 354 corpus rows
outside the Swinnerton-Dyer families -- none of which this change can affect --
the new sweep divided by the baseline has median **0.9977** and p90 **1.0234**,
with no row above 100 us moving more than 10%.  CPU 70 is therefore
interchangeable with the baseline's CPU 0 for timing.  Allocation *shares* from
the sampling profiler are less robust to the substitution; see the caveat under
"Allocator time" below.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-factor-sweep-94103267-hex-chungus2.json` | `50155349e1c3c897386cbdfa14cd0110224fc68ae21b1c378a7fa57d69aaefde` |
| `reports/bench-results/hexbz-phase-profile-94103267-chungus2.json` | `7878245a14a2984f4001c28a9c44ed0860b243288c4cd8d67c12d488f8276eaa` |
| `reports/bench-results/hexbz-factor-sampling-profiles-94103267-chungus2.json` | `e1d7828ccf092b5bd282086d9f00592169f829e26869eb1d3db80ab0b7ac3274` |

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
| `sd5_shift1` | 96.670 ms | 68.329 ms | **0.707x** |
| `sd5_shift2` | 99.713 ms | 71.717 ms | **0.719x** |
| `sd5_x_phi11` | 222.540 ms | 163.370 ms | **0.734x** |
| `sd5` | 106.911 ms | 78.963 ms | **0.739x** |
| `sd5_x_phi45` | 514.710 ms | 402.377 ms | **0.782x** |
| `sd4_x_sd4shift1` | 25.091 ms | 21.429 ms | **0.854x** |
| `xpow105_minus1` | 84.464 ms | 82.932 ms | 0.982x |
| `xpow120_minus1` | 523.812 ms | 516.723 ms | 0.986x |
| `wilkinson_48` | 29.732 ms | 29.356 ms | 0.987x |
| `xpow48_minus1` | 21.635 ms | 21.460 ms | 0.992x |
| `wilkinson_56` | 40.396 ms | 40.167 ms | 0.994x |
| `cyclo_phi179` | 80.025 ms | 80.764 ms | 1.009x |
| `cyclo_phi385` | 455.841 ms | 460.879 ms | 1.011x |
| `sd6` | 8.115 s | 8.251 s | 1.017x |
| `chebyshev_T24` (control) | 570.606 us | 570.396 us | 1.000x |
| `cyclo_phi41` (control) | 2.981 ms | 2.981 ms | 1.000x |
| `legendre_P30` (control) | 8.333 ms | 8.352 ms | 1.002x |
| `xpow24_minus1` (control) | 3.714 ms | 3.603 ms | 0.970x |
| `randprod_21` (control) | 1.771 ms | 1.750 ms | 0.988x |

`sd6` is the row that reaches the subset budget: its head-forced search over 32
lifted factors declines on `defaultSubsetBudget` and the answer comes from a
later tier, so there is nothing here for this change to remove, and 1.017x is
inside single-call noise on an eight-second row.

The phase profiler agrees on the rows that moved -- 0.772x on `sd5`, 0.748x and
0.760x on its shifts, 0.780x on `sd5_x_phi11`, 0.892x on `sd4_x_sd4shift1` --
and puts every non-SD row between 0.961x and 1.008x.

### Total factor time, independently, from the sampling profiles

The bounded prime walk (`Hex.classicalInput`) is untouched by this change, so
its absolute cost is the same in both records and the ratio of its sampled
shares recovers the change in total time without depending on either run's
absolute speed.

| instance | prime-walk share, before | after | implied total-time factor |
|---|---:|---:|---:|
| `sd5` | 8.94% | 11.98% | **0.746x** |
| `sd5_x_phi11` | 9.93% | 13.26% | **0.749x** |
| `cyclo_phi385` | 44.83% | 45.36% | 0.988x |
| `wilkinson_56` | 35.04% | 35.55% | 0.986x |
| `cyclo_phi179` | 18.61% | 18.69% | 0.996x |
| `cyclo_phi64_x_phi105` | 85.03% | 85.13% | 0.999x |
| `xpow105_minus1` | 47.30% | 46.79% | 1.011x |
| `xpow120_minus1` | 12.33% | 12.18% | 1.012x |
| `xpow48_minus1` | 27.92% | 27.56% | 1.013x |

Three independent measurements -- the sweep, the phase profiler, and this
ruler -- put `sd5` at 0.739x, 0.772x and 0.746x, and `sd5_x_phi11` at 0.734x,
0.780x and 0.749x.

### Traversal time

Rescaled by the ruler above, so both columns are fractions of the *same*
absolute time.  "Traversal outside the candidate test" is
`scanDirectCombinations` less `tryDirectCandidate` before and less
`Hex.directLeaf` after; both exclude the prefilters and the candidate work, so
the boundary is the same on each side.

| instance | before | after | |
|---|---:|---:|---:|
| `sd5` | 55.45% of total | 33.25% of the old total | **-40.0%** |
| `sd5_x_phi11` | 50.16% of total | 26.26% of the old total | **-47.6%** |
| `xpow48_minus1` | 0.53% | 0.18% | (already nothing) |
| every other profiled row | < 0.5% | < 0.5% | (already nothing) |

### Allocator time

Same rescaling, on the `allocation / free` leaf category of
`SPEC/profiling.md`, split by which allocator: glibc's, which is where GMP's
bignum limbs come from, and mimalloc, which is Lean's small-object path.

| | glibc / GMP | Lean small objects | all allocation |
|---|---:|---:|---:|
| `sd5` before | 57.24% | 10.81% | 69.10% |
| `sd5` after | 39.85% | 8.48% | 49.13% |
| | **-30.4%** | **-21.5%** | **-28.9%** |
| `sd5_x_phi11` before | 53.75% | 11.46% | 66.29% |
| `sd5_x_phi11` after | 37.95% | 8.66% | 47.33% |
| | **-29.4%** | **-24.5%** | **-28.6%** |

The split is the mechanism: `p ^ k` is bignum work and shows up in glibc's
allocator, the leaf list building is Lean constructor allocation and shows up
in mimalloc, and both fell.

**Caveat.**  Unlike the timing comparison, this one is not validated against
unchanged rows: the allocation share of `cyclo_phi64_x_phi105`, whose code path
this change does not touch at all, moves by -20% between the two records, and
`xpow120_minus1` by +8%.  Some of that is sampling variance and some is likely
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
| `Hex.scanDirectCombinations` | 84.16% |
| ... `Hex.directLeaf` | 39.61% |
| ... ... `Hex.directCandidatePrefilter` | 24.24% |
| ... ... ... `Hex.directTrailingPrefilter` | 15.54% |
| ... ... ... ... `Hex.centeredModNat` | 8.77% |
| ... ... ... `Hex.directDegreePrefilter` | 8.62% |
| ... ... `Hex.directCandidate` | 6.16% |
| ... ... `Hex.exactQuotient?` | 8.94% |
| traversal outside the leaf | 44.55% |

The traversal that remains is two cons cells and one modular multiply per
internal node: `x :: selectedRev`, `x :: rejectedRev`, and
`selectedTrail * trail x % modulusInt`.  The leaf that remains is dominated by
the prefilters' own arithmetic on 93-bit integers; `Hex.centeredModNat` alone
is 8.8% of total, and it reconverts the modulus from `Nat` to `Int` on every
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
pinning each recorded value to the factor it describes.

## Acceptance criteria

| criterion | outcome |
|---|---|
| candidate products not constructed before metadata-only filters finish | met; `Hex.directLeaf` guards on `directCandidatePrefilter`, confirmed in the generated C |
| allocation attributable to support traversal falls at least 40% on `sd5` and `sd5_x_phi11` | met on the traversal: -40.0% and -47.6%. Whole-factorization allocator time falls 28.9% and 28.6%, with the sampling caveat above |
| material end-to-end improvement on the SD family, no unexplained regression above 5% on low-width controls | met; 0.707x to 0.854x across the SD family, every control within 3% and every profiled non-SD row within 1.3% |
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
