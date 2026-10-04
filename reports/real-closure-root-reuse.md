# Cached selected-root search

An immutable inclusion cache retains each original predecessor and its checked
map. It also retains the mapped selected generators once per insertion, maps
them once on extension, and removes structurally duplicate images on insertion
and append. Searches do not recompute the original generators or their images.
Each candidate or its negative is accepted only if it satisfies the converted defining equation,
derivative signs, and strict finite bounds. Linear heads first provide their
coefficient-field root. This is a finite candidate search; arbitrary expressions
in several generators are not enumerated.

## Constraint order experiment

The [complete samples](bench-results/real-closure-root-reuse-order-corrected-valid/results.json)
compare head/derivative/lower/upper with lower/upper/head/derivative on identical
actual cached generators. Owners select positive roots of `X^d-2` and, for two
owners, `X^d-3`. Every query also requires the first derivative to be positive.
The positive candidates lie below, inside or above the queried open interval:

| Case | Quadratic query | Quartic query |
| --- | --- | --- |
| below | `X²-11`, `(3,4)` | `X⁴-17`, `(2,3)` |
| inside | `X²-6`, `(1,3)` | `X⁴-6`, `(1,3)` |
| above | `X²-1`, `(0,9/8)` | `X⁴-1`, `(0,9/8)` |

Each arm checks the same complete constraints on each cached generator and its
negative, and returns no match. Descriptor validation and gathering are outside
timing. This isolates constraint order; it does not compare full gathering
implementations.

Two trials alternate adjacent head/bounds and bounds/head arms. Each sample
performs three searches on one automatically leased CPU. All 48 successful
samples are retained with host context, exact source captures and executable
SHA-256 in the [metadata](bench-results/real-closure-root-reuse-order-corrected-valid/metadata.json).
Means below are microseconds per search on this host.

| Degree | Owners | Positive candidate location | Head first | Bounds first | Bounds/head |
| --- | --- | --- | --- | --- | --- |
| 2 | 1 | below | 25.0 | 23.7 | 0.95 |
| 2 | 1 | inside | 23.9 | 34.9 | 1.46 |
| 2 | 1 | above | 26.1 | 41.4 | 1.59 |
| 2 | 2 | below | 66.6 | 51.0 | 0.77 |
| 2 | 2 | inside | 67.1 | 86.7 | 1.29 |
| 2 | 2 | above | 68.3 | 132.0 | 1.93 |
| 4 | 1 | below | 240.4 | 54.7 | 0.23 |
| 4 | 1 | inside | 242.8 | 137.6 | 0.57 |
| 4 | 1 | above | 234.7 | 59.5 | 0.25 |
| 4 | 2 | below | 863.4 | 183.4 | 0.21 |
| 4 | 2 | inside | 854.0 | 486.9 | 0.57 |
| 4 | 2 | above | 881.7 | 187.7 | 0.21 |

Bounds first reduces the measured quartic cost in all three cases. Quadratic
inside/above queries favor head first; the quadratic below case favors bounds
first, with a near tie for one owner. These mixed results do not support a
universal reorder. Production remains head first.

Reproduce a compiled sample with
`lake exe hexrealclosure_bench reuse-order 4 2 inside bounds 3`.
The [runner](bench-results/real-closure-root-reuse-order-corrected-valid/measure.py.txt)
records the fixed trial-major schedule. Adapt checkout paths when reproducing.

## Full gathering comparison

The [32 bounded samples](bench-results/real-closure-gather-bounded/results.json)
compare the actual gathering implementation before and after caching generator
images and introducing checked selected-generator reuse. The baseline reuses
exact original contexts; it does not search other presentations' generators.
This measures the complete added search/cache feature, rather than isolating
image storage alone. Both arms use identical `GatherTiming` source, native descriptors and input
construction; the baseline executable omits the unrelated reuse-order mode.
Setup is outside the measured interval. Gathering is timed; a
second gathering checks every returned owner equation and positive
selected embedding after timing. Owners select positive roots of `X^d-p` for
successive primes `p = 2, 3, 5, 7, …`. Two fixed trials use
adjacent baseline/cached and cached/baseline order on one automatically leased
CPU. Each sample performs one gathering.

The compositum dimension column is the product of defining degrees; it is an
upper bound on the actual field degree because some selected roots can belong
to the field already constructed. Means are milliseconds on the recorded host.

| Degree | Owners | Product of degrees | Baseline | Cached | Cached/baseline |
| --- | --- | --- | --- | --- | --- |
| 2 | 2 | 4 | 0.9684 | 0.9390 | 0.97 |
| 2 | 4 | 16 | 10.4558 | 13.1537 | 1.26 |
| 2 | 6 | 64 | 474.8063 | 526.1958 | 1.11 |
| 2 | 8 | 256 | 17575.3189 | 21543.7189 | 1.23 |
| 4 | 1 | 4 | 0.2984 | 0.4329 | 1.45 |
| 4 | 2 | 16 | 0.8976 | 1.0834 | 1.21 |
| 4 | 3 | 64 | 1.6904 | 4.0420 | 2.39 |
| 4 | 4 | 256 | 6.5707 | 12.0316 | 1.83 |

The complete added search/cache feature is slower in seven of the eight family
means. The quadratic two- and six-owner pairs disagree in direction between
trials; in those families the first arm wins both times. Their means do not
establish the direction independently of order effects. These samples do not
establish a full-gathering speedup. Failed checked searches and image upkeep both
add work; the comparison does not attribute the regression to either component.
The benchmark checks every owner defining equation and positive selected
embedding in both arms; timing is not an acceptance criterion for these checks.

The [metadata](bench-results/real-closure-gather-bounded/metadata.json) and retained
source captures identify both exact executables, their source heads and modified
driver. The [runner](bench-results/real-closure-gather-bounded/measure.py.txt) fixes
the trial-major schedule. Reproduce an individual arm with
`hexrealclosure_bench gather-timing 2 8 1` in the corresponding checkout.

### Removing redundant deduplication on extension

The revised cache maps its retained candidates once on extension, without
deduplicating the mapped list again. Insertion and append still deduplicate;
the search already tracks visited candidates. This removes a redundant equality
pass while preserving the search result. The
[32 revised samples](bench-results/real-closure-gather-single-map/results.json)
repeat the identical bounded input families with this changed implementation,
the same baseline, and a fixed adjacent AB/BA schedule. Every semantic check
passed. Means are milliseconds on the recorded host.

| Degree | Owners | Product of degrees | Baseline | Revised cache | Cache/baseline |
| --- | --- | --- | --- | --- | --- |
| 2 | 2 | 4 | 0.4986 | 0.6046 | 1.21 |
| 2 | 4 | 16 | 5.2756 | 6.6930 | 1.27 |
| 2 | 6 | 64 | 266.2230 | 333.9573 | 1.25 |
| 2 | 8 | 256 | 16917.5481 | 21129.8460 | 1.25 |
| 4 | 1 | 4 | 0.2724 | 0.3310 | 1.21 |
| 4 | 2 | 16 | 0.6561 | 1.0128 | 1.54 |
| 4 | 3 | 64 | 1.5954 | 2.9715 | 1.86 |
| 4 | 4 | 256 | 6.2489 | 11.4546 | 1.83 |

All eight revised family means remain slower than the baseline, with the same
direction in every adjacent pair. The complete added feature has not demonstrated a benefit on these independent-root families;
removing this equality pass does not change that conclusion. This experiment
changes the implementation, so it is distinct from an unchanged rerun.
Its [metadata](bench-results/real-closure-gather-single-map/metadata.json),
source captures and [runner](bench-results/real-closure-gather-single-map/measure.py.txt)
identify the exact compared programs. Absolute timings from separate schedules
do not establish a before/after improvement.

An earlier [full-gathering schedule](bench-results/real-closure-gather-before-after/results.json)
completed the quadratic four- and eight-owner baseline/cached pairs, then its
quadratic twelve-owner baseline ran for 7,399 seconds of wall time without completing.
That unfinished sample was terminated, recorded with return code `-15`, and
retained alongside all completed samples. The sixteen-owner and larger quartic
cases were not run. The bounded schedule retains the quadratic eight-owner
endpoint and adds smaller owner families and quartic families whose product of
defining degrees does not exceed 256. No sample was discarded based on host
activity.

## Different presentations of the same selected root

The [32 reuse samples](bench-results/real-closure-gather-reused-owners-valid/results.json)
use the positive root of `X^d-2` in every owner, with distinct upper bounds
`3+i` and lower bound zero. This avoids exact-context equality hits and exercises
the added selected-generator search. Both arms check each returned owner's
defining equation and positive embedding after timing. Target presentation depth
may differ: the baseline can append another representation of the same root;
the revised search can retain one level. For these even-degree polynomials the
positive root is unique, so the checked equations and signs identify the same
mathematical values in both arms. Two trial-major adjacent AB/BA trials each
perform one gathering on an automatically leased CPU. Means are milliseconds.

| Degree | Owners | Baseline | Revised search/cache | Cache/baseline |
| --- | --- | --- | --- | --- |
| 2 | 2 | 0.4843 | 0.4841 | 1.000 |
| 2 | 4 | 5.3478 | 0.9190 | 0.172 |
| 2 | 6 | 274.0503 | 1.3249 | 0.0048 |
| 2 | 8 | 17473.6502 | 1.7578 | 0.00010 |
| 4 | 1 | 0.2603 | 0.3363 | 1.292 |
| 4 | 2 | 0.6543 | 0.7509 | 1.148 |
| 4 | 3 | 1.6076 | 1.1574 | 0.720 |
| 4 | 4 | 6.3636 | 1.5289 | 0.240 |

Reuse greatly reduces the measured larger quadratic cases and the three- and
four-owner quartic cases. One-owner quartic gathering cannot reuse a predecessor
root and pays the added feature's overhead; two-owner quartic gathering is also
slower. These observations support retaining checked generator reuse, with the
independent-root regressions above as a documented cost. They do not isolate
the effect of retaining images from the effect of avoiding repeated extensions.
The [metadata](bench-results/real-closure-gather-reused-owners-valid/metadata.json)
and [runner](bench-results/real-closure-gather-reused-owners-valid/measure.py.txt)
retain exact sources and binaries. Reproduce an arm with
`hexrealclosure_bench gather-reuse-timing 2 8 1` in its recorded checkout.

The [16 untimed depth checks](bench-results/real-closure-gather-reuse-depth-checks/results.json)
use those same input families and the same gathering algorithms, retaining their
own source and binary hashes. Each cached case returns depth one; each baseline
case returns depth equal to the owner count. Every owner-value check passes.
These checks verify that reuse happened without collecting another timing
schedule. The current driver prints `target_depth` after its semantic checks and
calls the number of verified owners `checked_owners`; the older archives retain
their original `semantic_hash` field name, which was a count rather than a hash.

The [initial setup rejection](bench-results/real-closure-gather-reused-owners/results.json)
required both implementations to return one presentation level, a condition
the baseline does not promise. It failed before producing a timing and is
retained separately. The corrected acceptance condition checks mathematical
owner values while allowing either valid presentation depth.

## Attribution

A representative cached quadratic eight-owner run was profiled at 99 Hz on one
leased CPU. The retained profile records roughly 4,000 samples and no lost events.
Allocation and reference-count release account for about 40% of exclusive samples;
GMP addition and rational multiplication also appear among the leading costs.
The captured call chains do not support a quantitative inclusive attribution to
BKR or lower-level selected-sign queries. This profile explains substantial
representation-management cost without completing the required Phase 4 cost
breakdown.

This is a profile of one cached-arm run, so it cannot attribute the difference
between the two arms. The invocation did not record a source head or binary
hash; its exact implementation cannot be identified. The raw profile is retained
outside the worktree at the durable host path, with its byte count and SHA-256 in
the [artifact manifest](bench-results/real-closure-gather-before-after/cached-eight-profile-artifact.json).
These provenance limits preclude using it as an exact-head Phase 4 attribution.

## Other retained runs and limits


The [earlier 16 samples](bench-results/real-closure-root-reuse-order/results.json)
used a reversed constraint list, which visited the upper bound before the lower,
and only candidates below the query interval. They describe that specific
schedule and cannot establish the behavior of lower-first checks across candidate
locations. Their exact source and runner remain alongside the samples.

The [invalid-input run](bench-results/real-closure-root-reuse-order-corrected/results.json)
used derivative index zero, rejected before timing. It is retained with its
source, executable hash and failure output; it supplies no search timing.

The required tower8 isolation, nested evidence, MetiTarski and clean-versus-eager
workloads remain outstanding. These focused measurements do not satisfy the
full tower Phase 4 evaluation.
The cost of retaining generator images during shared-context enlargement has
also not been measured by these gathering cases.
