# BKR tables over nested infinitesimal coefficient fields

The input fields iterate the existing canonical RationalFn field over the
rationals, with the existing positive-infinitesimal sign operation. The
registrations fix the extension depth at one or two. Within each
field, the query-count schedule is 128, 256, 512, 1024 and 2048.

The polynomial is P=X on the whole line, and every query is the constant
newest infinitesimal. There is exactly one root, zero, and its complete sign
pattern is all positive, with count one. The input validator checks the
actual recursively encoded polynomial and every query against this
elementary independent oracle. It does not reuse a Tarski query or matrix
algorithm. These cases complement the more complicated nested-field
conformance examples and the separate coefficient-sign measurements.

Production calls the actual buildPrepared operation. Tree replay checks its
supplied evidence using the ordinary coefficient arithmetic and signs.
Field construction, domain preparation, the input's retained reference tree,
graph construction and full input fingerprints happen outside timing.
The producer includes its own certificate checking. These timings are
overlapping operations and must not be summed as disjoint components.
Inspection also checks the actual graph; no graph timing model is claimed.

For each fixed depth, polynomial degrees, coefficient representations and
matrix dimensions are bounded independently of the query count s. Leaves
have three moment rows and every parent retains one row and one sign column.
The tree has 2s−1 nodes and 4s−1 moment slots. Its balanced arity volume is
s(log₂s+1); the actual construction and replay scan length-k query, sign and
exponent lists at a node. Inspection counts the query-reduction steps
actually stored at every node: s(log₂s+1). Replay checks 4s−1 moment certificates. The s leaves each
replay their domain once under the current domain-cache policy; parent
moments also replay their domains. Production adds s initial query
normalizations, 4s−1 bounded-size moment-chain constructions, 2s−1 rank
certificates, s leaf inversions and s−1 scaled solves. These linear terms
can have large constants. The asymptotic model is s(log₂s+1), but the
finite timing test does not distinguish the linear terms from the logarithmic factor.
The harness fits per-parameter medians after dropping the first parameter,
so the fitted range is 256..2048. The model has no free exponent or linear
coefficient; the harness fits only the slope of time divided by that model.
Depth-dependent arithmetic costs are fixed within each registration.
The measurements make no fitted exponential claim across depths.

Normalization changes the constant infinitesimal query to operand 1 and
stores the infinitesimal in its scale witness. The Tarski moments therefore
use 1 and X; infinitesimal arithmetic occurs in normalization and replay of
the query-reduction witnesses. At depth two, the lower-level coefficients
are only 0 and 1. These examples measure two layers of field arithmetic,
not interactions between infinitesimals from different levels. Field
operations use stored instance dictionaries, so absolute times need not
match a caller with specialized concrete coefficient types.

Run:

    lake build hexsigndet_bench
    .lake/build/bin/hexsigndet_bench inspect-nested-tables-small
    python3 scripts/bench/sign_det_nested_tables.py --output /path/to/new-captures

The collector uses one automatically leased CPU, six trial-major rounds
per registration, the shared 100 ms repeat target and a 300-second
operational child cap. It retains all scheduled outputs before judging
them, including inconclusive results or invalid points. Clean source,
binary, harness, input/result fingerprints and host context are recorded.
The timed producer mixes its table hash with the prepared input fingerprint;
successful replay returns that fingerprint. Both results distinguish the
field depth and supplied input. These fingerprints are reproducibility
checks, not independent mathematical proofs.
The collector's output must be outside the source checkout.
The regression fixture is a compiled inventory snapshot, rather than a
freshness test against the current binary. Scientific collection always
regenerates and validates its own live inventories.

These supplied same-level graphs do not represent coefficient-sign proof
DAGs across field levels. That logical interface has separate kernel
examples. The native fields in this family use ordinary coefficient
arithmetic, without tower implementations or additional field instances.
The registration defines these operations; the retained observations below
report their measured costs. They do not establish full Phase-4 completion.


The larger range retains the same source-derived s(log₂s+1) model, six
trial-major rounds, 100 ms target, 300-second operational cap and slope rule.
Only the fixed query-count ladder changes to 128, 256, 512, 1024 and 2048.
On the fitted range 256..2048, pure linear cost has expected residual slope
about −0.138, s(log₂s+1) has slope zero, and s(log₂s+1)² has slope about +0.138.
All three fall within the unchanged acceptance interval |β| ≤ 0.15.
A consistent verdict therefore shows finite-range consistency with the
model; it neither confirms nor separates its logarithmic factor. The
source-derived operation count supplies the reason for that factor.
Neither an exponent nor a linear coefficient is fitted.

The earlier ladder was 8, 16, 32, 64 and 128, fitted at 16..128. Both complete
120-point collections used revision
39066b34e16620946959796b86d60c4af5b29e29. Their retained archives are supplied
by [PR #10785](https://github.com/kim-em/hex-dev/pull/10785) under
reports/data/sign-det-nested-tables/39066b34e1/first and unchanged-rerun.
The first/rerun residual slopes were −0.179223/−0.176575 for depth-one
production, −0.147045/−0.145991 for depth-one tree replay,
−0.178336/−0.181258 for depth-two production, and
−0.161606/−0.156667 for depth-two tree replay. Only depth-one tree replay
was consistent; the other three were inconclusive. All slopes were negative,
indicating growth slower than the model on that range. No observation is
discarded or relabeled. Historical validators accept that exact earlier
ladder only when it is explicitly requested.

The 300-second cap includes setup inside each child, as well as the timed
callback. Setup produces the reference certificate, checks tree and graph,
and computes their hashes. For planning only, the earlier depth-two
production unchanged-rerun median of 2597.92124 ms at 128 queries scales to about 62 seconds
at 2048 under the declared model. A production child also pays for setup:
approximately two productions plus two replays in total, rather than one
62-second operation. Once a callback takes at least 50 ms the harness uses
one timed call. Inspection records the elapsed setup-plus-callback work for
every depth and query count on stderr before scientific timing starts;
those records establish the actual operational margin under the cap.
The complete depth-two inspection at 2048 queries took 154.461 seconds
on the shared host: setup, production, tree replay and graph replay together.
This is an operational preflight observation, not a scientific timing point;
its [stderr record](data/sign-det-nested-cap-preflight/inputs.stderr) and
[literal inventory](data/sign-det-nested-cap-preflight/inputs.stdout.gz) are
retained with source and binary bindings. Each capped child performs a subset
of that inspection’s operations. The observed margin is about 1.94, subject
to changing shared-host activity; it is not a future wall-clock bound.
A cap hit is retained and reported as an invalid observation, not a
consistent or inconclusive scaling result. No quiet-host preflight or
retry-until-clean loop is used. Finite-range consistency cannot prove an
asymptotic bound.


## Retained timing and allocation observations

[The source-bound archive](data/sign-det-nested-tables/39066b34e1/archive.json)
retains both complete timing collections from source `39066b34e1`, all 240
correct observations, and the complete source reconstruction patch. The archived ladder is 8,16,32,64,128. The second
collection is the single permitted unchanged rerun. Original metadata and raw
exports are retained byte for byte, with separate hashes for compressed storage.
Every completed sample is included; shared-host activity does not exclude points.

| Operation | First slope of time/model | Rerun slope | Rerun median at 8 queries | Rerun median at 128 queries |
| --- | ---: | ---: | ---: | ---: |
| Production, depth 1 | -0.179223 | -0.176575 | 6.750 ms | 126.878 ms |
| Tree replay, depth 1 | -0.147045 | -0.145991 | 3.888 ms | 78.301 ms |
| Production, depth 2 | -0.178336 | -0.181258 | 139.538 ms | 2597.921 ms |
| Tree replay, depth 2 | -0.161606 | -0.156667 | 79.050 ms | 1579.240 ms |

Tree replay at depth one is consistent with the declared model in both
collections, by margins of only 0.003 and 0.004 inside the slope tolerance.
All four slopes are negative: time grows more slowly than the model here.
Rerun doubling ratios are 2.03–2.16, compared with 2.29–2.5 for the model.
The four families show similar growth; this pass does not establish a distinct
scaling regime for depth-one replay. The other three families are inconclusive in both collections.
The source-derived model remains s(log₂s+1); the large linear terms described
above are not fitted away. The larger-range collection below supplies the separate follow-up to test
those costs; the original inconclusive verdicts remain unchanged. No further unchanged rerun is authorized for this range.

[The allocation archive](data/sign-det-nested-tables/39066b34e1/allocation/archive.json)
retains all 36 operation captures: three trial-major rounds, four registrations,
and 8, 32 and 128 queries. It uses the existing allocator profiler and stock
Valgrind; no arithmetic or profiler C implementation is changed. Each wrapper
calls the actual non-inlined `produce` or `checkTree` helper, whose generated
one-object-argument, pointer-result ABI is checked. Symbol lines are retained
from the unchanged binary with the measured hash; the binary itself is not
archived. The in-capture evidence of each symbol’s actual invocation is its
single wrapped callback. These
helpers run once per captured operation and are not called during preparation.
The independent literal oracle checks the field depth, queries and root/sign
table. Agreement with the same binary’s live inventory checks reproducibility.
Production fingerprints combine the input’s reference evidence with the
produced table; they do not fingerprint its newly produced certificate.
Successful replay returns the input fingerprint by definition.
The shared driver's three ABI self-checks, overflow guards and complete raw
profiles are retained.

| Operation at 128 queries | Lean requested bytes | mimalloc requested bytes | GMP requested bytes |
| --- | ---: | ---: | ---: |
| Production, depth 1 | 114,224,512 | 8,966,400 | 76,100,496 |
| Tree replay, depth 1 | 71,833,960 | 5,472,560 | 46,485,424 |
| Production, depth 2 | 2,347,789,080 | 192,098,528 | 1,572,709,056 |
| Tree replay, depth 2 | 1,442,321,896 | 117,350,032 | 959,558,896 |

All three rounds gave identical counters. The three buckets are disjoint:
[the stock method](sign-det-allocation-method.md) charges only the outermost
of the seven wrapped entry points. Their sum is cumulative requested bytes,
including repeated allocation; it neither measures live objects nor covers
every allocation path. These captures are not scientific timing samples. Instrumented RSS belongs
to the profiling process, including Valgrind and preparation. The broader
native/Massif memory study records process RSS and mapped pages separately.

Depths one and two supply the fixed routine coverage. An untimed deeper-field
prototype preflight is retained externally at
~/.local/state/hex/issue-10377-session-progress/nested-tables-depth-four-preflight/;
it yielded no scientific timing samples. Deeper-field correctness is covered
by the separate conformance examples.

Recheck the archived medians, raw allocation counts, native results, DHAT
provenance, ABI self-checks and callback bindings with:

    python3 -m scripts.bench.sign_det_nested_archive reports/data/sign-det-nested-tables/39066b34e1 --reconstruct-source

Source reconstruction applies the retained patch to its recorded base in a
private Git index and temporary object store, verifies the complete tree and
every recorded source hash,
and leaves the checkout unchanged. Historical exports use the explicitly fixed
8..128 ladder, never the current default. The allocation supplement retains
unchanged stock collector sources and generated helper declarations and symbol
lines from the original measured binary; original collection metadata and raw
capture bytes remain unchanged.

## Larger-range timing observations

The larger-range collection contains all 120 scheduled observations at revision
219e2232cf2a2e2f768ed058119a011e4e1ad13a. All input and result checks passed,
with no truncated, invalid or discarded sample. The four verdicts are
consistent with the declared model; no unchanged rerun was needed.

| Operation | Residual slope | Median at 128 queries (ms) | Median at 2048 queries (ms) |
|---|---:|---:|---:|
| Depth-one production | −0.095825 | 126.281 | 2276.226 |
| Depth-one tree replay | −0.074557 | 77.784 | 1483.962 |
| Depth-two production | −0.093002 | 2566.310 | 46544.805 |
| Depth-two tree replay | −0.085363 | 1573.124 | 29594.698 |

The [archive](data/sign-det-nested-wide/219e2232cf/archive.json) retains the
original metadata and losslessly compressed outputs, including the independent
literal input inventory, host load and CPU affinity, result fingerprints,
source and executable hashes and harness revision. The full source patch
reconstructs the measured Git tree; all 303 recorded source hashes are checked.
The archived collector and literal coefficient helper, bound to their recorded
hashes, supply the validation declarations without importing current collection
helpers. The validator also recomputes slopes and verdicts from the raw timings.
The retained Git commit object binds the reconstructed tree to the measured revision;
the collector’s original partial patch reproduces all 303 recorded source hashes. Validate the points, derived
medians and source reconstruction with:

    python3 -m scripts.bench.sign_det_nested_wide_archive \
      reports/data/sign-det-nested-wide/219e2232cf --reconstruct-source

The shared host was chungus2, pinned to CPU 21. Load averages (1/5/15 minutes)
were 5.85/4.70/6.62 before and 6.23/10.83/16.52 after collection. These are
recorded context; no sample is excluded because of host activity. The collection’s
own depth-two/2048 inspection took 155.801 seconds for setup, production, tree
replay and graph replay together, a 1.93 margin against the 300-second cap.
This operational observation is retained in inputs.stderr and is not a timing
point or future wall-clock bound. At 2048 queries the median
whole-child peak RSS values were 107290, 88130, 139466 and 104228 KiB in the
operation order shown above. These include setup and runtime state; they are
neither operation allocation traffic nor peak live-object sizes. The separate
36 operation-allocation captures on the earlier ladder remain unchanged in
[PR #10785](https://github.com/kim-em/hex-dev/pull/10785). Production and replay are overlapping regions and their times are
not added. The negative slopes indicate slower growth than the normalization
on the fitted finite range. As explained above, this range does not separate
linear growth from the logarithmic factor. These results satisfy this family's
declared finite consistency check, without establishing the library's remaining
joint/maximal-support findings or complete Phase-4 readiness.
