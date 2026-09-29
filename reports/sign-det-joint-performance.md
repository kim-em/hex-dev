# Joint Thom-query performance

This family compares the roots 1 and −1 of Xⁿ−1 and Xⁿ+1 for odd n. The
actual common head is −(X²ⁿ−1)/2. Each re-encoding has 3n+1 queries: the
2n target derivatives followed by the source equation and its n derivatives.
The [input inventory](sign-det-joint-inputs.md) describes the exact polynomial
and sign bindings and their independent rational-root oracle.

The timed bodies in `bench/HexSignDet/Joint.lean` exercise:

- completion of both original partial descriptors;
- cross-polynomial comparison of the completed sources, including the common
  product and both checked re-encodings;
- construction of both joint tables, separately with reduced and direct
  moment products;
- checking both supplied evidence trees in each production mode.

The table-production bodies each build two tables and replay both. They use
prepared domains. Completion builds two source tables and runs four tree
replays: `buildPrepared` checks each constructed tree, then
`Descriptor.ofReplay?` checks it again. Comparison builds four tables and runs
six tree replays: each re-encoding builds and checks a joint table, builds and
checks a target-descriptor table, then checks the joint tree again.
Completion and comparison construct the domains required by their actual APIs. Result
hashes include both returned derivative words or both table counts; the
comparison hash also includes its common head and ordering.

Preparation constructs and validates the source descriptors, completes them,
computes a comparison and both direct tables, and retains the supplied trees
and graphs. It is outside the timed loops. Untimed callback checks compare
answers with exact evaluation at the known roots before any measurement.
This family has realized support two, candidate matrices of width at most
four, infinite endpoints and no shared source roots. It does not cover maximal
support, finite endpoint constraints, common roots or nested coefficient fields.

## Cost model

The declared model is Θ(n³) polynomial coefficient operations for each timed
body on this family. It is not a unit-bit cost model or a bound for arbitrary
defining polynomials.

The target derivative degrees are 0,…,2n−1, the source derivative degrees are
0,…,n−1, and the source equation has degree n. Every leaf includes exponent
two. `DensePoly.mulImpl` visits every pair of stored coefficients, including
zeros. Consequently the sum of leaf square sizes is

```
(2n)(2n+1)(4n+1)/6 + n(n+1)(2n+1)/6 + (n+1)² = Θ(n³).
```

Positive preprocessing changes the scale of these monomials without changing
their degrees. The leaf products therefore give a cubic lower bound in both
production modes. Checking also reconstructs these products in the direct
moment identities or the supplied reduction identities. Every nonconstant
query also multiplies its moment polynomial by the head derivative and runs
pseudo-division. Those operations contribute O(n²) per row over O(n) rows.
Many visited coefficients are zero: this bound includes dense storage overhead
for sparse monomials, rather than work intrinsic to these particular roots.

The direct path uses `DensePoly.natPow`. In the measured implementation,
`natPow q 1` evaluates `q*q` before recursing to exponent zero, and discards
that square. Exponent two consequently also computes and discards a fourth
power. These additional dense products retain the cubic bound and contribute
to the direct timings. Reduced/direct ratios compare the complete current
implementations, including this work and their replay costs; they do not
isolate the mathematical benefit of reducing products modulo the head.

The complete child restrictions have at most two sign conditions. The retained
row basis starts with the constant row and, when two conditions occur, one
separating query row. Their tensor products have exponent sum at most two.
There are O(n) nodes and at most four moment rows per node. The inventory
requires maximum exponent sum two across both production modes and candidate
width at most four.

All moment operands have degree O(n). The head is a binomial, and the queries
are monomials apart from the one source equation. Reducing the source equation
or its square modulo the common head leaves a multiple of Xⁿ±1. After a
monomial shift, division of X²ⁿ−1 leaves that same binomial, which divides the
next remainder. Thus the remainder chains have bounded length rather than
the degree-dependent length possible for general heads. The inventory records
both modes' maximum chain lengths and rejects a length above eight. This check
describes the sparse family; it is not a claim that longer chains necessarily
violate the cubic coefficient-operation bound. Dense
query-kernel products and certificate identity products cost O(n²) per row,
giving O(n³) over all rows. Balanced query/exponent/sign slot work contributes
O(n² log n); the matrices have bounded dimensions and scalar sizes. Completion
uses source degree n instead of target degree 2n; comparison invokes a fixed
number of these tables and a binomial common-product calculation.

Raw rational coefficients grow with derivative factorials. Reduced witnesses
retain the scale (2n)!/2; the direct witness maximum includes n((2n)!/2)².
The inventories record these exact bit sizes. Actual timings include rational
arithmetic at those sizes, allocation and result hashing. Agreement with the
coefficient-operation model does not establish a bit-complexity bound, and
this family cannot separately identify degree and coefficient-height effects.
The coefficient-height family has its own measurements. A model mismatch is
retained and investigated rather than hidden by changing the model afterward.

## Collection protocol

The explicit degree schedule is 3, 7, 15, 31 and 63, with six trial-major
rounds. Reduced/direct production and replay use adjacent alternating AB/BA
arms. Completion and comparison each use the ordinary shared LeanBench
schedule. The target inner duration is 100 ms; a 180-second child-process cap is an
operational safeguard that includes preparation and calibration, although the
reported per-call timing excludes them. Every completed observation is retained. One CPU is
automatically leased, and host activity is recorded without an idleness test
or sample filtering.

The independent input validator checks literal polynomials, both exact sign
tables and dimensions. Callback result hashes bind the measured answers to
those checked inputs. The collector retains source reconstruction, executable
identity, command output, exact schedules and the shared harness verdicts.
Inconclusive verdicts remain observations, not successful performance gates.
At most one unchanged rerun is allowed after an inconclusive result. A changed
implementation requires a separate collection with its own source identity.
The collector runs all scientific arms before validation, so a timeout or bad
point in one arm does not suppress later measurements; the raw records and
validation failures are retained. The harness checkout must be clean and match
the manifest pin before and after collection.

LeanBench records each child's peak resident set, including preparation,
calibration and repeated timed calls. It does not isolate one operation's live
memory. Its allocated-byte field is unavailable, so resident-set observations
do not complete the separate allocated-byte requirement. Stored witness bits
and serialized certificate sizes likewise do not measure temporary peak bits
or allocation. This family alone does not complete Phase 4 or #10377.

## Retained collection at 1f55c4de9

The [raw records](data/sign-det-joint-timing/1f55c4de9/metadata.json) bind the
measurement to source `1f55c4de910bcc9715031d8ff03d081491020726`, CPU 20 on
`chungus2`, and the pinned shared harness. This collection used a 60-second
child-process cap. It retained 30 successful completion observations and 24
successful comparison observations, plus six `killed_at_cap` comparison records
at degree 63. Production and replay were not scheduled because this version of
the collector stopped when validating the capped comparison. No records are
removed or counted as successful timings when they lack an answer.

Median per-call times, excluding preparation and calibration, in milliseconds:

| Source degree | Complete both sources | Compare completed sources |
| --- | ---: | ---: |
| 3 | 1.040 | 12.675 |
| 7 | 5.357 | 78.753 |
| 15 | 28.720 | 517.718 |
| 31 | 169.252 | 3713.573 |
| 63 | 1110.296 | 6 capped trials |

Both harness verdicts are **inconclusive**. Completion's residual slope
−0.57246 uses degrees 7–63 after the harness drops degree 3. Comparison's
−0.56848 uses degrees 3–31 and carries the `truncated_at_cap` advisory. These
slopes describe `log(T/n³)` against `log n`, not negative growth of elapsed time,
and they cover different ranges.

The consecutive-interval exponents computed from the retained medians are
1.93, 2.20, 2.44 and 2.65 for completion, and 2.16, 2.47 and 2.71 for comparison.
They increase with degree but remain below three. This finite range does not
show the cubic leaf-square lower-bound term dominating elapsed time. It does
not identify the relative costs of coefficient arithmetic, dense zero slots,
query bookkeeping and replay. The captures below supply partial attribution.

The cap includes startup, preparation and hashing the prepared input as well
as the timed body. The parent supplies environment metadata to the child.
For a body taking at least 50 ms, the autotuner returns its first call, so
there is no additional calibration batch. A killed child does not establish
a 60-second lower bound for one comparison call.

The original metadata records the harness revision but does not establish a
clean package checkout at the beginning of collection. A separate
[harness inspection](data/sign-det-joint-timing/1f55c4de9/harness-inspection.json)
records a clean checkout matching the manifest during collection. A
[post-collection inspection](data/sign-det-joint-timing/1f55c4de9/post-collection-verification.json)
checks that source, clean git revision and executable still match the original
metadata after failure. These observations retain their actual scope; they are
not rewritten as start-of-run checks. The corrected collector checks harness
provenance before and after collection and runs all arms before validation.

This partial collection does not establish the joint-query performance gate.
The recorded untimed `callbacks` command took 143.5 seconds on the same leased
CPU for preparation and all six callbacks at all five degrees. This observation
motivates a 180-second child-process cap; it is not a guarantee about future
host activity. Raising the cap leaves the 100 ms inner target unchanged and
does not change how a completed point is timed.

The corrected collection can supply the previously missing degree-63
comparison and production/replay arms. Completion's timed implementation is
unchanged and was not capped: collecting it again consumes its one allowed
unchanged rerun, and there is no evidence that its verdict will change.
All original observations remain available. No further unchanged rerun is
permitted for this family after that collection.

The measured commit need not remain reachable after rebasing the PR. Its
[committed source patch](data/sign-det-joint-timing/1f55c4de9/committed-source.patch)
reconstructs the recorded source from `d279b9ffa`; the metadata records its
hash and the reconstruction check. The corrected revision changes the cap,
inventory guard and collection/reporting code, while preserving every timed
operation body. The old inventory's exponent bound covers reduced nodes only;
the corrected guard checks both production modes.

Replay returns a Boolean, whose successful digest is 11 for every degree.
That digest certifies successful acceptance, rather than identifying the input
size. Parameter and arm identity also rely on the registration, schedule and
retained source. Both table-production modes deliberately share an expected
answer hash because their tables must agree.

## Complete retained collection at 394c3c548

The [complete records](data/sign-det-joint-timing/394c3c548/metadata.json) contain
180 successful scientific points: thirty each for completion and comparison,
and sixty each for paired production and replay. They bind source
`394c3c54802ee1fe8e251098323b02c603536454`, the unchanged executable and clean
pinned harness before and after collection, on automatically leased CPU 28.
All input, callback, schedule and result validators pass. The separate archive
manifest hashes files after collection; it does not add retrospective metadata
to the original records.

Median per-call times in milliseconds, excluding preparation and calibration:

| Source degree | Completion | Comparison | Reduced production | Direct production | Reduced replay | Direct replay |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 1.049 | 12.729 | 5.886 | 6.538 | 3.151 | 3.299 |
| 7 | 5.718 | 79.456 | 36.668 | 44.356 | 19.155 | 22.505 |
| 15 | 29.234 | 522.338 | 238.360 | 318.613 | 118.679 | 156.176 |
| 31 | 170.706 | 3725.910 | 1695.884 | 2436.691 | 828.731 | 1145.641 |
| 63 | 1134.454 | 28283.769 | 12849.552 | 19097.066 | 6132.309 | 8985.939 |

All six scaling verdicts remain **inconclusive**, with residual slopes against
the declared cubic model of −0.592, −0.324, −0.331, −0.237, −0.371 and −0.273,
respectively. The harness's warmup exclusion leaves degrees 7–63 for these fits.
The completed collection removes the cap truncation; it still does not establish
that the cubic term dominates elapsed time over this range. Its exit status one
reports inconclusive verdicts, with no failed scientific points or validation
errors. This collection uses the permitted unchanged rerun; no further
unchanged rerun is planned.

Adjacent paired direct/reduced production ratios have medians 1.108, 1.223,
1.329, 1.441 and 1.478 over increasing degrees. Replay ratios are 1.047, 1.174,
1.313, 1.371 and 1.463. These are medians of six adjacent ratios at each degree,
not ratios of separately aggregated medians. They show a finite-range benefit
for the complete reduced implementation on these exact inputs, including the
extra direct powers described above. They do not isolate modulo-head reduction
or establish a general speedup.

Both the original capped collection and this complete collection are retained.
The CPU and allocation captures below supply partial attribution, rather than
turning the inconclusive scaling verdicts into successful performance gates.

## Representative operation attribution

The [profile manifest](data/sign-det-joint-timing/profile-394c3c548/metadata.json)
records one cold degree-31 comparison at source `394c3c548`, automatically
leased CPU 52, with the same executable hash before and after capture. Perf
sampled user-space cycles at 199 Hz. The shared harness emitted one operation
region using `CLOCK_MONOTONIC`; its result had the expected comparison digest.
This is profiling evidence, not a scientific timing observation or a scaling
verdict.

There are 716 samples within that region and 1,232 outside it. All retained
operation samples belong to the recorded benchmark process. The
[direct-IP summary](data/sign-det-joint-timing/profile-394c3c548/ip-summary.json)
attributes the operation's sampled instruction pointers as follows:

| Sampled function | Samples | Share |
| --- | ---: | ---: |
| `cfree@GLIBC_2.2.5` | 111 | 15.5% |
| `malloc` | 104 | 14.5% |
| `__gmpz_add` | 74 | 10.3% |
| `__gmpz_init_set_ui` | 54 | 7.5% |
| `realloc` | 39 | 5.4% |
| `__gmpz_mul_2exp` | 36 | 5.0% |
| `l_Rat_mul` | 35 | 4.9% |
| `lean_nat_gcd` | 28 | 3.9% |
| `__gmpz_gcd` | 27 | 3.8% |
| `__gmpz_realloc` | 27 | 3.8% |

Allocation/freeing functions, GMP integer operations, rational multiplication
and gcd work occupy most sampled leaves. Matrix dimensions in this family are
at most four; this profile supplies no useful estimate of general matrix-solve
scaling. Coefficient-sign checks are similarly too small here to attribute
reliably. The wider support and nested-field families remain necessary.

The first call-stack extraction had 461 samples with no unwound frame. Perf's
recorded instruction pointers recover their leaf symbols without another
capture. Both derived summaries and the raw capture are retained; the direct-IP
summary is the basis for this table. Caller-stack attribution is limited by
incomplete unwinding. Allocation-function sample shares are CPU costs, not
allocation counts, allocated bytes or peak live memory.

## Intercepted allocation observations

A separate heaptrack capture runs one cold degree-31 comparison at source
`394c3c54802ee1fe8e251098323b02c603536454`, on automatically leased CPU 34.
The executable hash is unchanged before and after the capture. The manifest,
commands, summaries and original analysis outputs are in
[data/sign-det-joint-timing/allocation-394c3c548](data/sign-det-joint-timing/allocation-394c3c548).
Raw compressed events and folded stacks remain in the manifest's local directory.

Across the whole child process, including preparation, heaptrack reports
1,039,653,778 intercepted allocation calls. Its allocation-size histogram has
exactly the same count, with 10,237,421,113 cumulative requested bytes.
These count requests to the intercepted allocation functions, including
reallocations. They are neither peak live bytes nor a count of every Lean object
allocation. The reported peak tracked heap is approximately 196.34 KB;
instrumented RSS is approximately 1.37 GB and includes profiler overhead.
Instrumentation took about 564 seconds, so its elapsed time is excluded from
the scientific timing observations.

Exact matching of the comparison callback frame in the folded stacks attributes
385,922,080 calls to that callback. This is an attributable lower bound:
incomplete unwinding can omit the frame. A broader substring filter also matches
specialized helpers used during preparation, and would incorrectly include
another 386,197,862 calls. The original shorter symbol filter matched no reported
allocators; its unchanged output is retained. Importantly, heaptrack's summary
and size-histogram totals remain whole-process totals even with a backtrace
filter. Consequently the cumulative requested-byte figure cannot be assigned to
the comparison alone. The supplied postprocessor distinguishes exact callback
frames from helper names; it does not rerun the capture.

This supplies an allocation observation for the representative comparison.
Allocation scaling, complete operation-specific byte counters, wider matrices
and nested coefficient evidence remain separate requirements.
