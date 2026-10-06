# Joint Thom-query performance

This family compares the roots 1 and −1 of Xⁿ−1 and Xⁿ+1 for odd n. The actual common
head is −(X²ⁿ−1)/2. Each re-encoding has 3n+1 queries: the 2n target derivatives
followed by the source equation and its n derivatives. The [input inventory](sign-det-joint-inputs.md) describes the exact polynomial and sign bindings and their independent
rational-root oracle.

The timed bodies in `bench/HexSignDet/Joint.lean` exercise:

- completion of both original partial descriptors;
- cross-polynomial comparison of the completed sources, including the common
  product and both checked re-encodings;
- construction of both joint tables, separately with reduced and direct
  moment products;
- checking both supplied evidence trees in each production mode.

The table-production bodies each build two tables and replay both. They use prepared
domains. Completion builds two source tables and runs four tree replays: `buildPrepared`
checks each constructed tree, then `Descriptor.ofReplay?` checks it again. Comparison
builds four tables and runs six tree replays: each re-encoding builds and checks a joint
table, builds and checks a target-descriptor table, then checks the joint tree again.
Completion and comparison construct the domains required by their actual APIs. Result
hashes include both returned derivative words or both table counts; the comparison hash
also includes its common head and ordering.

Each registration prepares its source descriptors, domains or supplied trees.
Completion receives only
the two validated partial descriptors. Comparison receives the two completed source
identities. Table production receives the actual common polynomial, checked prepared
domain and ordered queries, without producing either table first. Replay receives the
two supplied trees for its selected reduced or direct mode, checked against exact
evaluation at the known roots. Reduced replay trees are constructed by
`buildPrepared` in reduced mode and compared by complete serialized-graph
equality with the comparison producer’s re-encoding evidence. Preparation
remains outside the timed loops.

The combined case constructor is retained for independent input inspection. Callback
inspection checks separate preparations against the combined case’s literal source
descriptors and complete serialized evidence, as well as the common head and both ordered
query lists, then compares the six callbacks with the same exact root answers. Type
indices prevent completion/comparison or reduced/direct replay preparations from being
swapped in a registration. The retained collections below used the combined
constructor; their input inventories, callback result hashes and observations
remain unchanged. Separating preparation supplies no new scientific timing
verdict and changes no cubic operation bound. It does not authorize another
unchanged rerun. The source and attribution evidence below distinguish that
operation bound from an unsupported wall-time prediction; see the final scope
section for the applicable disposition.

The new reduced/direct replay arms retain only their respective supplied trees,
whereas both historical arms retained the same complete combined case. Heap
contents, allocator locality and process resident peaks can therefore differ.
Future replay ratios and resident measurements are not directly comparable
with the retained combined-preparation ratios and memory observations. Both
production arms still use the same prepared input.

This family has realized support two,
candidate matrices of width at most four, infinite endpoints and no shared source roots.
It does not cover maximal support, finite endpoint constraints, common roots or nested
coefficient fields.

## Cost model

The declared model is Θ(n³) polynomial coefficient operations for each timed body on
this family. It is not a unit-bit cost model or a bound for arbitrary defining
polynomials.

The target derivative degrees are 0,…,2n−1, the source derivative degrees are 0,…,n−1,
and the source equation has degree n. Every leaf includes exponent two.
`DensePoly.mulImpl` visits every pair of stored coefficients, including zeros.
Consequently the sum of leaf square sizes is

```
(2n)(2n+1)(4n+1)/6 + n(n+1)(2n+1)/6 + (n+1)² = Θ(n³).
```

Positive preprocessing changes the scale of these monomials without changing their
degrees. The leaf products therefore give a cubic lower bound in both production modes.
Checking also reconstructs these products in the direct moment identities or the
supplied reduction identities. Every nonconstant query also multiplies its moment
polynomial by the head derivative and runs pseudo-division. Those operations contribute
O(n²) per row over O(n) rows. Many visited coefficients are zero: this bound includes
dense storage overhead for sparse monomials, rather than work intrinsic to these
particular roots.

The direct path uses `DensePoly.natPow`. In the measured implementation, `natPow q 1`
evaluates `q*q` before recursing to exponent zero, and discards that square. Exponent
two consequently also computes and discards a fourth power. These additional dense
products retain the cubic bound and contribute to the direct timings. Reduced/direct
ratios compare the complete measured implementations, including this work and their
replay costs; they do not isolate the mathematical benefit of reducing products modulo
the head. The [polynomial-power correction](sign-det-poly-power.md) removes this
unused work; the historical measurements are unchanged.

The complete child restrictions have at most two sign conditions. The retained row basis
starts with the constant row and, when two conditions occur, one separating query row.
Their tensor products have exponent sum at most two. There are O(n) nodes and at most
four moment rows per node. The inventory requires maximum exponent sum two across both
production modes and candidate width at most four.

All moment operands have degree O(n). The head is a binomial, and the queries are
monomials apart from the one source equation. Reducing the source equation or its square
modulo the common head leaves a multiple of Xⁿ±1. After a monomial shift, division of
X²ⁿ−1 leaves that same binomial, which divides the next remainder. Thus the remainder
chains have bounded length rather than the degree-dependent length possible for general
heads. The inventory records both modes' maximum chain lengths and rejects a length
above eight. This check describes the sparse family; it is not a claim that longer
chains necessarily violate the cubic coefficient-operation bound. Dense query-kernel
products and certificate identity products cost O(n²) per row, giving O(n³) over all
rows. Balanced query/exponent/sign slot work contributes O(n² log n); the matrices have
bounded dimensions and scalar sizes. Completion uses source degree n instead of target
degree 2n; comparison invokes a fixed number of these tables and a binomial common-
product calculation.

Raw rational coefficients grow with derivative factorials. Reduced witnesses retain the
scale (2n)!/2; the direct witness maximum includes n((2n)!/2)². The inventories record
these exact bit sizes. Actual timings include rational arithmetic at those sizes,
allocation and result hashing. Agreement with the coefficient-operation model does not
establish a bit-complexity bound, and this family cannot separately identify degree and
coefficient-height effects. The coefficient-height family has its own measurements. A
model mismatch is retained and investigated rather than hidden by changing the model
afterward.

## Collection protocol

The current explicit degree schedule is 15, 31, 63, 127 and 255, with six
trial-major rounds. It extends the geometric degree ladder to exercise the
dense coefficient operations at larger degrees. Historical collections keep
their original 3, 7, 15, 31 and 63 schedule and settings.
Reduced/direct production and replay use adjacent alternating AB/BA arms. Completion and
comparison each use the ordinary shared LeanBench schedule. The target inner duration is
100 ms; a 3600-second child-process cap is an operational safeguard that includes
preparation and calibration, although the reported per-call timing excludes them. Every
completed observation is retained. One CPU is automatically leased, and host activity is
recorded without an idleness test or sample filtering.

The cap is a planning safeguard. The earlier size-63 comparison child took
about 29 seconds including preparation; cubic extrapolation to 255 gives
roughly 1900 seconds. A full collection may take around 18 hours. These are
estimates, not measured size-255 guarantees: the larger coefficient operands
and host activity can increase the duration. The collector checks all five
sizes and all actual callbacks before beginning the scientific arms, retaining
their elapsed wall times. A cap hit is a failed observation, retained with the
later scheduled samples, rather than a passed or inconclusive verdict.

After the fixed warmup exclusion, the wider fit uses degrees 31 through 255.
At 255 the stored reduced and direct witnesses have about 3900 and 7700 bits.
A consistent cubic verdict is finite-range wall-time evidence; it does not
separate coefficient-operation counts from growing bit costs. A slope outside
the fixed tolerance remains an investigated finding. The model, exponent,
tolerance and completed samples are not changed to obtain a desired verdict.
The explicit commands with suffix `-wide` select this ladder; the commands
`inspect-joint` and `inspect-joint-timings` retain their historical defaults.

The independent input validator checks literal polynomials, both exact sign tables and
dimensions. Production, completion and comparison result hashes bind the measured answers
to those checked inputs. Replay returns a Boolean, so its successful hash is
the same at every degree; the exact parameter schedule binds replay samples
to their degrees.
The collector retains source reconstruction, executable identity, command output, exact
schedules and the shared harness verdicts. Inconclusive verdicts remain observations,
not successful performance gates. At most one unchanged rerun is allowed after an
inconclusive result. A changed implementation requires a separate collection with its
own source identity. The collector runs all scientific arms before validation, so a
timeout or bad point in one arm does not suppress later measurements; the raw records
and validation failures are retained. The harness checkout must be clean and match the
manifest pin before and after collection.

LeanBench records each child's peak resident set, including preparation, calibration and
repeated timed calls. It does not isolate one operation's live memory. Its allocated-
byte field is unavailable, so resident-set observations do not complete the separate
allocated-byte requirement. Stored witness bits and serialized certificate sizes
likewise do not measure temporary peak bits or allocation. This family alone does not
complete Phase 4 or #10377.

## Retained collection at 1f55c4de9

The [raw records](data/sign-det-joint-timing/1f55c4de9/metadata.json) bind the
measurement to source `1f55c4de910bcc9715031d8ff03d081491020726`, CPU 20 on `chungus2`,
and the pinned shared harness. This collection used a 60-second child-process cap. It
retained 30 successful completion observations and 24 successful comparison
observations, plus six `killed_at_cap` comparison records at degree 63. Production and
replay were not scheduled because this version of the collector stopped when validating
the capped comparison. No records are removed or counted as successful timings when they
lack an answer.

Median per-call times, excluding preparation and calibration, in milliseconds:

| Source degree | Complete both sources | Compare completed sources |
| --- | ---: | ---: |
| 3 | 1.040 | 12.675 |
| 7 | 5.357 | 78.753 |
| 15 | 28.720 | 517.718 |
| 31 | 169.252 | 3713.573 |
| 63 | 1110.296 | 6 capped trials |

Both harness verdicts are **inconclusive**. Completion's residual slope −0.57246 uses
degrees 7–63 after the harness drops degree 3. Comparison's −0.56848 uses degrees 3–31
and carries the `truncated_at_cap` advisory. These slopes describe `log(T/n³)` against
`log n`, not negative growth of elapsed time, and they cover different ranges.

The consecutive-interval exponents computed from the retained medians are 1.93, 2.20,
2.44 and 2.65 for completion, and 2.16, 2.47 and 2.71 for comparison. They increase with
degree but remain below three. This finite range does not show the cubic leaf-square
lower-bound term dominating elapsed time. It does not identify the relative costs of
coefficient arithmetic, dense zero slots, query bookkeeping and replay. The captures
below supply partial attribution.

The cap includes startup, preparation and hashing the prepared input as well as the
timed body. The parent supplies environment metadata to the child. For a body taking at
least 50 ms, the autotuner returns its first call, so there is no additional calibration
batch. A killed child does not establish a 60-second lower bound for one comparison
call.

The original metadata records the harness revision but does not establish a clean
package checkout at the beginning of collection. A separate [harness inspection](data/sign-det-joint-timing/1f55c4de9/harness-inspection.json) records a
clean checkout matching the manifest during collection. A [post-collection inspection](data/sign-det-joint-timing/1f55c4de9/post-collection-verification.json)
checks that source, clean git revision and executable still match the original metadata
after failure. These observations retain their actual scope; they are not rewritten as
start-of-run checks. The corrected collector checks harness provenance before and after
collection and runs all arms before validation.

This partial collection does not establish the joint-query performance gate. The
recorded untimed `callbacks` command took 143.5 seconds on the same leased CPU for
preparation and all six callbacks at all five degrees. This observation motivates a
180-second child-process cap; it is not a guarantee about future host activity. Raising
the cap leaves the 100 ms inner target unchanged and does not change how a completed
point is timed.

The corrected collection can supply the previously missing degree-63 comparison and
production/replay arms. Completion's timed implementation is unchanged and was not
capped: collecting it again consumes its one allowed unchanged rerun, and there is no
evidence that its verdict will change. All original observations remain available. No
further unchanged rerun is permitted for this family after that collection.

The measured commit need not remain reachable after rebasing the PR. Its [committed source patch](data/sign-det-joint-timing/1f55c4de9/committed-source.patch) reconstructs
the recorded source from `d279b9ffa`; the metadata records its hash and the
reconstruction check. The corrected revision changes the cap, inventory guard and
collection/reporting code, while preserving every timed operation body. The old
inventory's exponent bound covers reduced nodes only; the corrected guard checks both
production modes.

Replay returns a Boolean, whose successful digest is 11 for every degree. That digest
certifies successful acceptance, rather than identifying the input size. Parameter and
arm identity also rely on the registration, schedule and retained source. Both table-
production modes deliberately share an expected answer hash because their tables must
agree.

## Complete retained collection at 394c3c548

The [complete records](data/sign-det-joint-timing/394c3c548/metadata.json) contain 180
successful scientific points: thirty each for completion and comparison, and sixty each
for paired production and replay. They bind source
`394c3c54802ee1fe8e251098323b02c603536454`, the unchanged executable and clean pinned
harness before and after collection, on automatically leased CPU 28. All input,
callback, schedule and result validators pass. The separate archive manifest hashes
files after collection; it does not add retrospective metadata to the original records.
Both worktree paths use the same physical build cache. The scientific children, like the
profiles, resolve through that cache; before/after binary hashes identify the measured
executable, but the original collection does not establish build-cache isolation.

Median per-call times in milliseconds, excluding preparation and calibration:

| Source degree | Completion | Comparison | Reduced production | Direct production | Reduced replay | Direct replay |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 1.049 | 12.729 | 5.886 | 6.538 | 3.151 | 3.299 |
| 7 | 5.718 | 79.456 | 36.668 | 44.356 | 19.155 | 22.505 |
| 15 | 29.234 | 522.338 | 238.360 | 318.613 | 118.679 | 156.176 |
| 31 | 170.706 | 3725.910 | 1695.884 | 2436.691 | 828.731 | 1145.641 |
| 63 | 1134.454 | 28283.769 | 12849.552 | 19097.066 | 6132.309 | 8985.939 |

All six scaling verdicts remain **inconclusive**, with residual slopes against the
declared cubic model of −0.592, −0.324, −0.331, −0.237, −0.371 and −0.273, respectively.
The harness's warmup exclusion leaves degrees 7–63 for these fits. The completed
collection removes the cap truncation; it still does not establish that the cubic term
dominates elapsed time over this range. The retained summaries report inconclusive
verdicts, with no failed scientific points or validation errors. The outer log contains
Lake freshness output, not an independently recorded collector exit status. This
collection uses the permitted unchanged rerun; no further unchanged rerun is permitted.
This is family-level accounting: the production and replay arms also use up that rerun,
even though the original collector stopped before scheduling them. The [benchmark finding on #10377](https://github.com/kim-em/hex-dev/issues/10377#issuecomment-5882834592) records the investigation requirement. The retained inclusive attribution,
source operand inventory and wider observations supply that investigation.
The final scope section states the operation-count interpretation; no
declaration is fitted to the observed slopes.

Adjacent paired direct/reduced production ratios have medians 1.108, 1.223, 1.329, 1.441
and 1.478 over increasing degrees. Replay ratios are 1.047, 1.174, 1.313, 1.371 and
1.463. These are medians of six adjacent ratios at each degree, not ratios of separately
aggregated medians. They show a finite-range benefit for the complete reduced
implementation on these exact inputs, including the extra direct powers described above.
They do not isolate modulo-head reduction or establish a general speedup.

Both the original capped collection and this complete collection are retained. The CPU
and allocation captures below supply partial attribution, rather than turning the
inconclusive scaling verdicts into successful performance gates.

## Representative operation attribution

The [profile manifest](data/sign-det-joint-timing/profile-394c3c548/metadata.json)
records one cold degree-31 comparison at source `394c3c548`, automatically leased CPU
52, with the same executable hash before and after capture. That hash equals the
scientific collection’s binary hash. Both worktree paths use the same physical `.lake`
cache; the [analysis addendum](data/sign-det-joint-timing/profile-394c3c548/analysis-addendum.json) records their post-capture realpaths and inode identity. Original
metadata did not record those identities. Future measurements require an isolated build
cache. Perf sampled user-space cycles at 199 Hz. The shared harness emitted one
operation region using `CLOCK_MONOTONIC`; its result had the expected comparison digest.
This is profiling evidence, not a scientific timing observation or a scaling verdict.

There are 716 samples within that region and 1,232 outside it. All retained operation
samples belong to the recorded benchmark process. The [direct-IP summary](data/sign-det-joint-timing/profile-394c3c548/ip-summary.json) attributes the operation's sampled
instruction pointers as follows:

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

The [leaf categorisation](data/sign-det-joint-timing/profile-394c3c548/leaf-categories.json) classifies 715 of 716 samples: allocation/free 47.6%, GMP arithmetic
28.8%, Lean runtime 11.9%, Hex code 3.2%, and other Lean library code (Rat/List) 8.4%.
`cfree` is glibc’s alias for `free`. GMP allocation wrappers are counted in
allocation/free, rather than arithmetic. Initialization and mpz constructor routines
retain their named GMP/runtime categories; this split describes sampled functions rather
than inclusive allocation-related work. These are user-mode samples; `cycles:u` excludes
kernel work such as page faults. Specialisation names containing `input_spec` can belong
to helpers reused by the timed body; they do not establish that preparation leaked into
the operation region. Allocation/freeing functions, GMP integer operations, rational
multiplication and gcd work occupy most sampled leaves. Matrix dimensions in this family
are at most four; this profile supplies no useful estimate of general matrix-solve
scaling. Coefficient-sign checks are similarly too small here to attribute reliably. The
wider support and nested-field families remain necessary.

The call-stack extraction had 461 binary samples with no unwound frame; the other
samples recovered only a leaf. No operation sample has a caller stack. Perf's recorded
instruction pointers recover their leaf symbols without another capture. Both derived
summaries and the raw capture are retained; the direct-IP summary is the basis for this
table. Samply’s framehop unwinder recovers caller stacks from the same unchanged
capture. The [inclusive summary](data/sign-det-joint-timing/profile-394c3c548/inclusive-summary.json) and [diagnostics](data/sign-det-joint-timing/profile-394c3c548/diagnostics.json) use the existing pinned
filtering/symbolication tools. All 1,948 imported samples match the raw monotonic
timestamps with one common offset and zero residual. The analysis-time clock anchor
supplies only a common coordinate conversion; it was not recorded at spawn, and no wall-
clock claim relies on it. The postprocessing commands and raw hashes are in the [Samply analysis manifest](data/sign-det-joint-timing/profile-394c3c548/samply-analysis.json).

The filtered profile classifies 91.48% of leaves: allocation/free 38.13%, GMP 36.31%,
Lean runtime 16.62%, Hex own code 0.42%, and other 8.52%. This uses the shared
summarizer’s category rules; the manually classified instruction-pointer table above
uses a different explicit grouping.

| Inclusive function | Share of operation samples |
| --- | ---: |
| `lean_nat_gcd` | 83.24% |
| `SignDet.buildPrepared` | 77.93% |
| `DensePoly.mulImpl` | 66.62% |
| `SignDet.Replay.check` | 60.34% |
| `SignDet.checkMoment` | 54.61% |
| `SignedRemainderChain.check` | 49.02% |
| `Sturm.certifyPrepared` | 34.92% |
| `DensePoly.positivePseudoDiv` | 23.88% |

The [call-path check](data/sign-det-joint-timing/profile-394c3c548/stack-plausibility.json)
checks every recovered frame beneath `lean_nat_gcd` against the runtime
call-path allowlist and finds no unexpected name. All 182 samples with GMP
addition or shifting beneath it have the unsigned 64-bit `mpz` constructor as the immediate caller of
the addition/shift frame. Those calls are valid: [Lean’s pinned runtime source](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/runtime/mpz.cpp#L39)
constructs the value by shifting and adding its two halves. The captured
binary’s gcd and constructor disassemblies retain the corresponding calls.
The 83.24% inclusive gcd share therefore includes integer promotion and
normalization, not only the GMP gcd algorithm. This plausibility check addresses
those specific call paths; timestamp/window confidence alone does not validate
caller stacks, and the check does not prove every unwind edge.

These shares overlap. Dense multiplication includes rational normalization and gcd work
under its coefficient operations. Replay validates polynomial identities in the signed
remainder chains as well as building their evidence; it therefore contributes to the
same arithmetic hot path. The degree-31 comparison registers the complete
production/checking composition, so those costs are attributable to the measured
callback. This narrow-support case still supplies no general matrix or nested
coefficient-sign attribution.

Window diagnostics (these do not validate caller stacks):

```text
calibration residual: 4.254 ms (effective limit 20.1005 ms)
total timed duration: 3603.8 ms
retained operation samples: 716
samples from other threads within the window: 0
sensitivity under ±5 ms window shifts: passed
confidence: passed
```

Allocation-function sample shares are CPU costs, not
allocation counts, allocated bytes or peak live memory.

## Intercepted allocation observations

A separate heaptrack capture runs one cold degree-31 comparison at source
`394c3c54802ee1fe8e251098323b02c603536454`, on automatically leased CPU 34. The
executable hash is unchanged before and after the capture. The manifest, commands,
summaries and original analysis outputs are in [data/sign-det-joint-timing/allocation-394c3c548](data/sign-det-joint-timing/allocation-394c3c548). Raw
compressed events and folded stacks are retained under
`/home/kim/.local/state/hex/issue-10377-profiles/issue-10377-joint-allocation-394c3c548`. The original `/tmp` path is a symlink to this durable directory.
The [analysis addendum](data/sign-det-joint-timing/allocation-394c3c548/analysis-addendum.json) records corrected analysis commands and binary-path bindings; original
records are unchanged. The CPU capture is retained in the corresponding durable
`issue-10377-joint-profile-394c3c548` directory.

Across the whole child process, including preparation, heaptrack reports 1,039,653,778
intercepted allocation calls. Its allocation-size histogram has exactly the same count,
with 10,237,421,113 cumulative requested bytes. These count requests to the intercepted
allocation functions, including reallocations. They measure GMP/glibc allocation
traffic: 810,295,561 calls are from `__gmp_default_allocate` and 229,341,127 from
`__gmp_default_reallocate`, 99.998% of the total. Lean object allocation and live heap
are unmeasured. They are neither peak live bytes nor Lean allocation counts. The
reported peak tracked GMP/glibc heap is approximately 196.34 KB; instrumented RSS is
approximately 1.37 GB and includes profiler overhead. Instrumentation took about 564
seconds, so its elapsed time is excluded from the scientific timing observations.

Exact matching of the comparison callback frame in the folded stacks attributes
385,922,080 calls to that callback. This is an attributable lower bound: incomplete
unwinding can omit the frame. A broader substring filter also matches specialized
helpers used during preparation, and would incorrectly include another 386,197,862
calls. Of these, 386,040,114 have an explicit preparation frame, while 157,748 have
neither the preparation nor exact callback frame. The [callback-only aggregate](data/sign-det-joint-timing/allocation-394c3c548/callback-frame-allocation-counts.json) separates these scopes. The lower bound does not count stacks whose
callback frame failed to unwind, including any outside the substring filter. The
original shorter symbol filter matched no reported allocators; its unchanged output is
retained. Importantly, heaptrack's summary and size-histogram totals remain whole-
process totals even with a backtrace filter. Consequently the cumulative requested-byte
figure cannot be assigned to the comparison alone. The supplied postprocessor
distinguishes exact callback frames from helper names; it does not rerun the capture.

The [streaming reanalysis](data/sign-det-joint-timing/allocation-394c3c548/reanalyse.py)
parses the whole-process total from the retained output and commits per-frame
aggregates. The original postprocessor is preserved as part of the capture record.
`comparison-histogram.tsv` contains whole-process data despite its name. Its one- and
two-limb requests, together with gcd/Rat multiplication stacks, show substantial small-
operand rational-normalisation traffic. `lean_nat_gcd` appears in 99.1% of the
substring-filtered allocation stacks; the inclusive CPU profile separately attributes
83.24% of its samples to that function.

This supplies a GMP allocation observation. The operation-scoped collection
below adds intercepted Lean, direct mimalloc and GMP request counts for joint
table production, completion, comparison and replay across three degrees.
Coverage of additional allocation paths, live heap,
wider allocation families, representative profiles for those families,
wider matrices and nested coefficient evidence remain separate coverage
requirements. The six fitted verdicts retain their original values under the
operation-count interpretation in the final scope section.

## Operation-scoped allocation

The [joint allocation collection](sign-det-joint-allocations.md) retains 54
single-callback observations over table production, completion, comparison and
both replay modes at degrees 3, 7 and 15, plus one degree-31 comparison check. It separates intercepted Lean, direct mimalloc and GMP
entry-point requests and checks native result agreement. These cumulative
requested-byte observations have their own coverage limits; they do not supply
peak live memory or resolve the running-time verdicts above.


## Completed wider observations and interrupted comparison

The [retained archive](data/sign-det-joint-timing/432958c4fc-interrupted/archive.json)
binds source `432958c4fc14dbff1ea8110e47c5d1b073bd5ac8`, its compiled binary,
pinned harness, source patch and all original outputs. The source is reconstructed
from merged base `98cab2feb5` plus `committed-source.patch`; the archived metadata
records that reconstruction check. The measurements describe that snapshot,
whose commit need not remain reachable after rebasing. Equality with current
main’s executable is not claimed. The input inventory and
callback checks completed at degrees 15, 31, 63, 127 and 255. Completion and
cross-polynomial comparison each completed all 30 scheduled timing points,
with exact result hashes checked against the callback inventory.

| Source degree | Completion median (s) | Comparison median (s) |
| ---: | ---: | ---: |
| 15 | 0.028601 | 0.521794 |
| 31 | 0.166799 | 3.771672 |
| 63 | 1.098908 | 28.216194 |
| 127 | 7.815629 | 220.943285 |
| 255 | 58.274983 | 1750.337582 |

The unchanged cubic declaration gives **inconclusive** for completion
(residual slope −0.219255) and **consistent with declared complexity** for
comparison (−0.084199). The fits exclude the leading degree-15 warmup rung,
while retaining all its observations. These are the original harness verdicts. The cubic
coefficient-operation count is not a bit-cost bound. The varying factorial
coefficients, dense zero entries and rational normalization have different
costs; passing this fit does not establish the running time of arbitrary
comparison inputs. Completion has appreciable trial variation, including a
92.1-second degree-255 observation; all completed samples and recorded host
load remain included. Host activity is context, not a reason to remove points.

The collection was interrupted during the subsequent adjacent production
comparison. It retains nine completed points, in the original scheduled
order, plus the header. No production summary was emitted and replay timing
did not begin. These partial points are not a complete comparison or a scaling
verdict. The original collector metadata records `failed` with
`KeyboardInterrupt`; its last operation record remains `running` because the
collector was interrupted inside that operation. A separate
[final binding](data/sign-det-joint-timing/432958c4fc-interrupted/final-binding.json)
records unchanged source, binary, revision and harness revision after interruption.
A separate [later harness inspection](data/sign-det-joint-timing/432958c4fc-interrupted/harness-inspection.json)
records its clean status and manifest-pin agreement, with its actual observation
time and commands; this is not an original collector after-check.
The remaining measurement processes were stopped; none continued separately.
No original record is rewritten as a completed collection.

The input inspection took 5,883 seconds, callback inspection 11,621 seconds,
completion collection 440 seconds and comparison collection 12,708 seconds.
Those durations include preparation and child startup. They are not per-call
timings. Extending the campaign adds substantial cost and is
not required merely to obtain another fitted verdict. The retained smaller
adjacent production/replay comparisons remain separate evidence. This archive
supplies completed wider observations and explicit limits, not final Phase-4
attestation. Under the changed schedule, comparison is consistent; completion
remains inconclusive. This collection does not resolve the four earlier
production/replay findings. Their disposition remains separate, using the
applicable evidence policy rather than continuing this interrupted campaign.

The existing CI test `scripts.bench.test_sign_det_joint_timing` checks archive
hashes, unchanged bindings, input and callback answers, both complete timing
schedules, the recomputed medians and the partial schedule prefix. It also
checks that the incomplete production file is rejected by the ordinary full
comparison validator.

## Whole-child resident memory and practical range

The following values are median native process high-water marks in MiB across
six trials at each size. They include preparation, startup and harness tuning,
not just the timed callback; they are neither peak live heap nor isolated
callback working sets. The original preparation built a combined case for all
arms. The wider collection used the later separated preparations. Their
resident values must not be treated as adjacent before/after measurements.

| Callback, original collection | 3 | 7 | 15 | 31 | 63 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Completion | 66.2 | 67.8 | 72.1 | 87.8 | 152.1 |
| Comparison | 66.2 | 68.1 | 74.1 | 96.1 | 182.6 |
| Reduced production | 66.1 | 67.6 | 71.8 | 90.0 | 160.3 |
| Direct production | 66.1 | 68.0 | 72.1 | 90.3 | 160.7 |
| Reduced replay | 65.6 | 68.2 | 72.0 | 87.6 | 152.1 |
| Direct replay | 66.0 | 68.1 | 71.9 | 87.2 | 152.4 |

These values come from every successful sample's `peak_rss_kb` in
`reports/data/sign-det-joint-timing/394c3c548/`: `runCompletion.json`,
`runComparison.json`, `production.jsonl` and `replay.jsonl`.

| Callback, wider collection | 15 | 31 | 63 | 127 | 255 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Completion | 66.3 | 66.4 | 70.2 | 81.8 | 127.9 |
| Comparison | 70.2 | 80.4 | 122.1 | 284.6 | 863.8 |

The wider collection's complete completion/comparison JSON records supply these
values. Its interrupted production/replay output does not provide a complete
resident-memory comparison.

The intended representative joint examples have source degrees 3–15; degree
31 is a stress case. In the original collection comparison medians are about
13 ms, 80 ms, 522 ms and 3.73 s at degrees 3, 7, 15 and 31. At degree 63 the
same operation takes 28.28 s. In the wider collection comparison reaches
220.94 s at 127 and 1750.34 s at 255, with completion reaching 58.28 s at 255.
The low-degree cases are usable library examples. These large comparison
cases are slow and are not presented as practical interactive workloads.
The 864 MiB median process peak at 255 reinforces that limitation. No new
measurement or retrospective acceptance threshold is inferred from this table.

## Scope of the coefficient-operation declaration

The six `Joint.*` formulas count coefficient operations. They do not provide
an independently justified wall-time model for these rational computations.
The literal input inventory identifies growing factorial coefficients, but
that growth does not explain the observed *subcubic* residuals. Lower-order
per-row work and unequal costs of zero and nonzero operations can affect the
finite range. The comparison profile shows substantial dense multiplication
and rational normalization. The wider comparison's local exponents approach
three (2.97 and 2.99), and its original verdict is consistent; wider completion
retains its inconclusive −0.219 residual. These observations support no claim
of unexpectedly supercubic timing growth.

An operand-size correction was considered. Stored witness maxima are not
peak intermediate operands, and pricing all dense coefficient visits by the
largest factorial coefficient would ignore the predominance of zeros. No
proved bit-complexity bound for the combined rational/GMP implementation is
available here. Consequently this report asserts the derived cubic
coefficient-operation bound, not a substitute bit-aware timing law. It does
not claim that timings establish the operation count or certify a bit bound.

Under the representative-observation rule in
[SPEC/benchmarking.md](../SPEC/benchmarking.md#choosing-the-complexity-claim),
the original formulas, measurements and fitted verdicts remain intact and the
fits are descriptive. Exact answers and all scheduled original points are
checked. The tables above supply time and process-memory context on the
representative range. No exponent or constant is fitted to repair a declaration.
The wider complete observations are additional evidence, not a requirement to
repeat expensive large cases.

This replaces the obligation to obtain a passing cubic timing fit; it does not
relabel historical verdicts as passing. A source-bound violation, excessive
cost on intended inputs, or a failed explicit comparison target still requires
a fix. Peak intermediate bits and polynomial gcd counts remain evidence gaps.
The bound concerns this two-root, bounded-candidate family, not arbitrary
real-root problems. This disposition requires the evidence policy to be
merged; it is not itself a Phase-4 attestation.

## Practical improvements

The measured direct reference computes unused polynomial powers. PR #10810 removes the exponent-one square and preserves the power and
coefficient-interpretation proofs; the historical timings retain that work.
Its [small adjacent comparison](sign-det-poly-power.md) retains all 72 cold
production/replay observations at degrees 3, 7 and 15. It shows no uniform
winner and makes no before/after timing claim. This report depends on that
change merging before treating those observations as current.

Skipping zero coefficients in dense multiplication could save substantial
work on these sparse inputs. The generic executable interface currently
assumes operations but no zero-annihilation laws, so that change needs a
lawful optimized interface and a proof of agreement; it is not silently
applied to arbitrary coefficient operations. Denominator-one normalization
and small-integer gcd fast paths are further candidates indicated by the
profile. The latter belongs to Lean's runtime, and no C runtime change is
made here. These are potential improvements, not demonstrated speedups or
reasons to collect longer ladders. The immediate avoidable power computation
is addressed before any additional optimization campaign.
