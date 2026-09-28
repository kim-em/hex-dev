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
a Boolean. Construction times therefore include that checksum work. The phase
ladder is fixed before measurement
at 8192,16384,32768,65536,131072,262144,524288 bits, with six trials per
height and a one-second target per batch. It avoids making the bounded BKR
systems dominate a small-height timing range. Preparation constructs only the
reduced preprocessing evidence; it does not expand unreduced powers of c or
build the full reference. All setup and correctness checks occur outside the
timed operation. No completed sample is removed because of host activity,
and no retry is automatic.

The mode-1 claim is `Θ(H)` for these two phases on this positive-monomial
family. Preprocessing normalizes the monomials to unit coefficients.
Lean 4.34.1's `Rat.mul` cancels cross-factors with gcd and exact division before
multiplying. Here its large operands are degenerate: `gcd(c,c)`, `gcd(0,c)`,
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

This family removes coefficient height at preprocessing. It covers that phase,
not height growth through general Sturm chains, full production, shared-graph
replay or nested coefficients. A harder coefficient family and the other
Phase-4 tracks remain required. In particular, an end-to-end linear timing claim
is not made from the 64-to-4096-bit inventory.

Collect with `python3 scripts/bench/collect_sign_det_height.py --output <new-directory>`
after committing sources and building `hexsigndet_bench`. The output must be
outside the source worktree. The driver leases one CPU, verifies build
freshness, archives reconstructible sources, records executable hashes and
host context, and retains every log and export. Validation checks the exact
schedule, settings, oracle-bound output hashes and clean source revision.
Complete measurements and model verdicts are recorded separately; the
collector returns nonzero if either verdict is inconclusive.

The harness's peak RSS is a process lifetime high-water mark, including
untimed preparation and runtime startup. It is not isolated replay memory.
The pinned harness has no allocation-byte counter; a missing value is not
zero. These registrations alone cannot discharge allocation, nested-field,
maximal-support, joint-query, unreduced comparison or complete Phase-4 gates.

The [retained collection](data/sign-det-height/640bf10bd/metadata.json)
uses Lean 4.34.1 and committed source
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

The archive preserves the exact premeasurement sources, including the
original validator. The additional model-formula and relative-size validation passes the
same retained data; it does not replace or remove measurements. Later report
and validator edits do not change the measured normalization or checking
functions. Reproduction uses the base and patch recorded in the metadata.

These passing results establish the declared normalization-phase models for
the archived Lean 4.34.1 revision only. They do not establish performance on
the current Lean 4.35.0-rc3 toolchain. General coefficient-height propagation, allocation, nested fields,
maximal support, joint comparisons and the remaining Phase-4 requirements
remain open under #10377.
