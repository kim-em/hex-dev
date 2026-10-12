# Coefficient-height normalization evidence

The head is `P=X³−1` and the queries are `[cX²,cX,c]`, with
`c=2^H−1`. Degree, support and matrix dimensions remain fixed while
coefficient height grows. The unique real root is 1: the remaining factor
`X²+X+1` is positive. All three queries are positive there, so the exact
complete table contains `[1,1,1]` with count one.

The small inventory at 64,…,4096 bits checks the reduced and unreduced
producers and the full 27-column reference against that independent table.
It checks graph and byte replay tables, rather than merely successful decoding.
Literal inputs, stored witness bits, dimensions, graph edges and certificate
bytes are recorded. Stored maxima do not measure temporary arithmetic or
aggregate live memory. These graphs have no shared nodes.

Scientific registrations measure `QueryReduction.build` and
`QueryReduction.check` separately. The construction registration also computes
a checksum of the literal reduction output; the checking registration returns
a Boolean. Construction times therefore include that checksum work. The digest uses
three large-integer doublings through the standard integer hash. Integer
hashing and explicit `Int.natAbs` conversions also copy H-bit magnitudes.
Replay copies one magnitude to obtain its input height. These fingerprint
operations add linear bit work; the GMP bit-length primitive itself takes
constant time. Coefficient bit lengths make its fingerprint sensitive to
the measured height; replay returns its input height together with its Boolean
result. These finite hashes do not establish literal output equality.
`phaseValid` checks every input and reduction field independently before timing. The phase
ladder is fixed before measurement at
8192,16384,32768,65536,131072,262144,524288 bits, with six trials per
height and a one-second target per batch. It avoids making the bounded BKR
systems dominate a small-height timing range. Preparation constructs only the
reduced preprocessing evidence; it does not expand unreduced powers of c or
build the full reference. Input preparation and independent correctness
validation occur outside the timed operation. No completed sample is removed because of host activity,
and no retry is automatic.

The mode-1 claim is `Θ(H)` for these two phases on this positive-monomial
family. Preprocessing normalizes the monomials to unit coefficients.
Lean 4.34.1 and 4.35.0-rc3 have identical `Rat.mul` definitions: they cancel
cross-factors with gcd and exact division before multiplying. Here its large operands are degenerate: `gcd(c,c)`, `gcd(0,c)`,
`gcd(c,1)`, and division `c/c` or `c/1`. Equality or a one-limb quotient
makes those particular operations linear; this is not a general gcd or
long-division bound. Other operations are multiplication by one limb and
proportional sums, differences and comparisons. The fixed number of slots
therefore gives linear bit work. General GMP gcd uses different algorithms
and thresholds; see the primary [Lehmer algorithm documentation](https://gmplib.org/manual/Lehmer_0027s-Algorithm.html)
and [subquadratic gcd documentation](https://gmplib.org/manual/Subquadratic-GCD).

The phase input guard checks every original polynomial and reduction field
against the symbolic formula, including all indices, unit remainders,
quotients and scales. Large phase records describe c symbolically instead of
using enormous decimal JSON tokens. The largest input integer occupies
64 KiB before allocator overhead. CPU cache sizes are recorded as host context;
cache or allocator effects can still make a finite-range result inconclusive.
The declared model is not changed to fit those observations.

The library SPEC bounds count arithmetic operations in terms of polynomial
degrees and query counts. Those parameters are fixed here, so their operation
counts are bounded independently of H. This experiment supplies a bit-cost
model for coefficient normalization, including its output fingerprint. It
does not exercise polynomial-division work: each query degree is below the
head degree. The equal-operand termination path is described in GMP's
[gcd source](https://github.com/gmp-mirror/gmp/blob/master/mpn/generic/gcd.c) and
[equality branch](https://github.com/gmp-mirror/gmp/blob/master/mpn/generic/gcd_subdiv_step.c).
The native backend audit records the actual gcd and bit-length call targets.
Bit length uses GMP's [base-two size calculation](https://github.com/gmp-mirror/gmp/blob/master/mpz/sizeinbase.c).
Earlier archived collections did not record this backend audit explicitly.
The precise GMP version is unrecorded. The linked call routes are verified; the source links
explain the relevant operations without identifying the exact linked release.

This family removes coefficient height at preprocessing. It covers that phase,
not height growth through general Sturm chains, full production, shared-graph
replay or nested coefficients. The
[consolidated report](sign-det-performance.md) links the other measured
families and records general chain-height propagation as a coverage limit.
An end-to-end linear timing claim
is not made from the 64-to-4096-bit inventory.

Collect with `python3 scripts/bench/collect_sign_det_height.py --output <new-directory>`
after committing sources and building `hexsigndet_bench`. The output must be
outside the source worktree. The driver leases one CPU, verifies build
freshness, archives reconstructible sources, records executable hashes and
host context, and retains every log and export. Validation checks the exact
schedule, settings, output fingerprints, compiler pin and clean source revision.
Complete measurements and model verdicts are recorded separately; the
collector returns nonzero if either verdict is inconclusive.

The harness's peak RSS is a process lifetime high-water mark, including
untimed preparation and runtime startup. It is not isolated replay memory.
The pinned harness has no allocation-byte counter; a missing value is not
zero. These registrations alone cannot discharge allocation, nested-field,
maximal-support, joint-query, unreduced comparison or complete Phase-4 gates.

The [archived Lean 4.34.1 collection](data/sign-det-height/640bf10bd/metadata.json)
uses Lean 4.34.1 and pre-rebase source revision
`640bf10bd72d2ad25e6ce5d9f1c409e5dfc13eaa` on shared host `chungus2`, automatically leased CPU 82. All 84 scientific samples
completed with the expected outputs and exact trial-major schedules. Sources
and executable hashes were unchanged. Both mode-1 verdicts are **consistent
with declared complexity**; no sample was removed and no rerun was used.
The normalized slopes are −0.081272 for construction and −0.074066 for
replay. The harness omits the first rung from its fitted verdict, while the
raw exports retain it.

The host's recorded data L1 is 48 KiB, L2 is 1 MiB and L3 is 32 MiB. These
are context, not a claim of cache isolation. Medians below include every
completed sample at each height; they are observations on this host.

| Coefficient bits | Normalization median µs | Replay median µs |
| ---: | ---: | ---: |
| 8,192 | 8.261 | 18.054 |
| 16,384 | 14.018 | 33.216 |
| 32,768 | 22.650 | 57.533 |
| 65,536 | 41.920 | 107.791 |
| 131,072 | 77.885 | 206.123 |
| 262,144 | 164.919 | 404.705 |
| 524,288 | 324.728 | 808.804 |

The source-derived reduced byte-size difference is 16 times the difference
in the decimal digit count of c. The five unshared nodes have eight original
query occurrences; each stores c once in the query and once as a preprocessing
scale. Every other reduced graph literal is height-independent. The small
inventory passes this additional relative-size check at all seven heights.
The absolute size remains an observed value: at 4096 bits the reduced graph
has 25,297 bytes and the unreduced graph 46,760 bytes. This is not a proof
of a general byte-parser roundtrip or an independent reconstruction of every
encoded byte.

Both earlier archives use the original checksum, whose integer hashes
truncate high bits and whose replay result is only a Boolean. Those hashes
are constant across this height ladder and cannot detect a run at the wrong
height. Literal input/reduction checks in `phaseValid`, rather than the hashes,
provide their value validation. New collections include coefficient bit lengths
in construction fingerprints and input height in replay results, and reject
fingerprint collisions between the seven declared phase heights. Small
inventory table/result hashes remain height-independent and are only
auxiliary observations; their literal inputs and tables are checked directly.

The archive preserves the exact premeasurement sources, including the
original validator. The additional model-formula and relative-size validation passes the
same retained data; it does not replace or remove measurements. Later report
and validator edits do not change the measured normalization or checking
functions. Reproduction uses the base and patch recorded in each metadata file.
None of the three measurement revisions is in the published branch history.
Each is reconstructed from the base and patch recorded in its metadata, with
file hashes preserving the measured sources. The recorded bases `18eb65686`
and `f08b8e9e8` are ancestors of main. The `640bf10bd` build directory was shared
with another worktree, as recorded by the resolved binary path. Hash and
freshness checks passed at collection time. New collections require the
executable to resolve inside their own source worktree.

The [Lean 4.35.0-rc3 collection](data/sign-det-height/ad5e59e5a/metadata.json)
uses recorded source `ad5e59e5aee5f8a0ae3003f86658f6de2dfa42a5` on the same
shared host, automatically leased CPU 89. All 84 scientific samples passed
output and schedule validation, with sources and executable unchanged. Both
mode-1 verdicts are **consistent with declared complexity**, with normalized
slopes −0.079653 for construction and −0.074067 for checking. No sample was
removed and no rerun was used. Recorded cache sizes match the earlier host
context. Medians include all six completed samples at each height. Host load averages
were 9.35, 22.84, 18.77 at collection start and
5.88, 18.81, 17.67 at collection end. They are recorded context;
no activity threshold rejected a completed sample.

| Coefficient bits | Normalization median µs | Replay median µs |
| ---: | ---: | ---: |
| 8,192 | 8.281 | 18.118 |
| 16,384 | 14.024 | 33.355 |
| 32,768 | 22.719 | 57.861 |
| 65,536 | 41.923 | 108.350 |
| 131,072 | 78.099 | 207.005 |
| 262,144 | 165.872 | 406.697 |
| 524,288 | 326.715 | 812.709 |

The [height-sensitive collection](data/sign-det-height/e3e380d81/metadata.json)
uses source `e3e380d818bbd6e74937895e5ddb4207f24b6bdc` and Lean 4.35.0-rc3,
on leased CPU 53 of the same shared host. Its 84 samples passed the exact
schedule, compiler-pin and height-sensitive fingerprint checks. Source and
executable hashes remained unchanged. Both verdicts are **consistent with
declared complexity**, with normalized slopes −0.080808 for construction and
−0.074718 for replay. The retained runtime audit confirms the executable's GMP
gcd and base-two bit-length routes. There was no discarded sample or rerun.
Load averages were 7.00, 11.35, 13.31 before collection and 6.30, 10.28, 12.79
afterwards, recorded as context.

| Coefficient bits | Normalization median µs | Replay median µs |
| ---: | ---: | ---: |
| 8,192 | 8.425 | 18.174 |
| 16,384 | 14.399 | 33.504 |
| 32,768 | 23.257 | 58.102 |
| 65,536 | 42.690 | 108.412 |
| 131,072 | 79.945 | 207.418 |
| 262,144 | 169.303 | 407.744 |
| 524,288 | 333.816 | 814.296 |

All three collections are consistent with the declared linear model on
their recorded revisions. The finite-range verdict does not prove an
asymptotic bound: its ±0.15 slope tolerance cannot distinguish a small
additional logarithmic factor across this ladder. The three highest doublings in the `e3e380d81` collection have ratios
approximately 1.87, 2.12, 1.97 for construction and 1.91, 1.97, 2.00
for replay. These observations distinguish
linear from quadratic growth on this range, while the model itself comes
from the stated primitive-operation analysis. General coefficient-height propagation remains outside this fixed-family
model. The [consolidated report](sign-det-performance.md) states the attested
coverage and its limits. Separate reports cover the retained
[maximal-support evidence](sign-det-maximal-matrices.md),
[joint-query and allocation evidence](sign-det-joint-performance.md), and
[nested-field conformance](sign-det-nested-fields.md). None establishes performance for every coefficient field.

Operation-scoped allocation observations for these exact normalization and
checking phases are retained in [the allocation report](sign-det-height-allocations.md).
They supplement the timing records; they do not measure live or peak memory.
