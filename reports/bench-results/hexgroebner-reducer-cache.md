# Reusing exact multiplied reducers in F4

Explicit checkpoint caches avoid repeating symbolic reducer multiplication.
On the fixed diagnostic suite, candidate B/A has geometric mean **0.9227**,
median **0.9401** and range **0.7736–1.0220**. Eco-10 improves by about 16% and
Reimer-5 by about 22%; small cyclic cases can be slightly slower. All complete
bases and non-resource counters agree. These are Hex before/after observations,
with no fresh external-comparator sweep for the cache and no performance
leadership claim.

## Representation and correctness

`ReducerCache` retains at most 16384 entries in the F4 checkpoint, associated
with its append-only monomial arena. The constructor and entries are private.
A 64-bit key packs the stable leading and multiplier IDs. A hit also compares
the entire base polynomial, so a changed reducer with the same leading monomial
cannot reuse a different row. Exponent-width changes preserve IDs and cached
supports. Sugar and certificate derivations use the current basis; no cached
receipt or derivation promotes a candidate to a checked result.

Base/product payloads share already charged immutable polynomial buffers.
Lookup and full comparison work consumes the parent allowance; each inserted
key reserves eight logical bytes. The cache skips an insertion when its cap or
remaining key allowance would be exceeded. Ordinary uncached multiplication
still consumes its usual allowance; there is no unbounded recovery path.
Allocator headers and map capacity have the same exclusion as other computation
metadata. Raw internal callers must retain the associated monomial arena.

The native byte comparator borrows both buffers, validates the complete slice
and processes at most 4096 bytes per call. Invalid ranges or larger quanta return
false before access, including arbitrary-size Nat offsets. It mutates no data,
retains no pointers and assumes neither alignment nor byte order. A kernel-
reducible Lean implementation supplies the portable behavior. Whole-polynomial
validation splits longer comparisons into bounded calls.

The candidate and traced-certificate producers both retain the cache across
rounds and shared final interreduction. A successful stage commits its cache;
failed stages retain the previous checkpoint and charged work/allocation.
Every reused row still gets a derivation from the current basis root, followed
by independent complete-basis certification.

## Validation

The full library/theory/conformance build passes (14187 jobs). All 175 matrix,
567 SymPy/Singular basis and 1288 division/normal-form/membership oracle cases
pass, as do all 29 benchmark verification cases and project audits at the
measured snapshot. Regenerated F4 fixtures change exactly three work fields in
325 cases: `work`, `serialWork` and `referenceWork`. Every basis, input, field,
order and non-work counter is unchanged; the explicit comparison is retained.

Tests cover low-work/low-byte budgets, repeated hits with no new polynomial
allocation, a changed reducer with the same leading ID, and reuse after exponent
storage widens to 32 bits. Existing candidate/certificate resume and parent-
budget cases pass. All 567 traced outputs match the reference and their complete
certificates independently check. Ordinary-kernel byte-comparison examples and
existing basis replay examples pass; no new axiom or admission is introduced.

The compiled matrix harness instruments the byte binding, verifies its C type
and requires its call counter to be nonzero. All four SIMD/scalar and
Barrett/remainder variants pass with Clang and GCC, ordinarily and with
ASan/UBSan. Each variant executes all 3920 explicit byte-comparison calls.
Standalone C tests cover slice endpoints, 4096-byte limits, mismatches, aliasing
and overflow-sized offsets. Sanitizers instrument C rather than Lean-generated
code, and Lean buffers lack ASan heap redzones; bounded range comparisons and
the portable equality checks remain independent obligations.

## Measurement contract

The host is chungus2, AMD EPYC 9455, Lean 4.35.0-rc3. Generated C uses bundled
Clang 23.1.0; FFI uses system Clang 23.1.3. Both arms use one computation thread
pinned to an automatically leased CPU, frozen executables and adjacent AB then
BA comparisons. Source fingerprint B is `f4edebd7a46e`; the algorithm is at
`41976a14b5`, with subsequent harness tests in `ee19e19fef`. Baseline A is the
narrow-SIMD production engine, measured fingerprint `04e1c0a5f392`, corresponding
to the computational sources in PR #10998's `98ee31c93e` snapshot. Exact source
blobs and executable hashes identify each arm independently of rebased ancestry.

Every completed sample, regression and outlier is retained. There are no
failures, timeouts or discarded samples. One unchanged rerun of the fixed
benchmark experiment follows an inconclusive cyclic-6 observation. The full
16-case diagnostic experiment has no unchanged rerun. Earlier cache prototypes
are separate implementations and are not pooled with production data.
Candidate time covers canonicalization, F4 and final interreduction. Process
time also includes startup, parsing and complete output. Certificate generation,
independent certification and kernel checking are excluded from these timings.

## Full-system diagnostic suite

The suite is cyclic-5/6, Katsura-6, Eco-10, Noon-4, Reimer-5, MinRank and fixed
quadratics over 32003/2147483647 in grevlex. It weights cyclic twice and is
neither balanced nor held out. Suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
The leased CPU is 30; each process has a ten-second timeout and a 16-GiB address-
space allowance. All 64 processes complete, with all 32 full basis comparisons
and non-resource counters equal.

Candidate B/A geometric mean/median are 0.9227/0.9401, range 0.7736–1.0220.
Process B/A geometric mean/median are 0.9440/0.9854, range 0.8113–1.0286.
Means weight paired ratios equally, without family balancing. Tiny cases have
substantial process-startup cost; their process ratios do not isolate F4.

| Input | Candidate AB | Candidate BA | Work B/A | Cumulative allocation B/A |
| --- | ---: | ---: | ---: | ---: |
| cyclic5-15 | 0.9974 | 1.0058 | 0.9849 | 0.9951 |
| cyclic5-31 | 1.0008 | 1.0180 | 0.9885 | 0.9957 |
| cyclic6-15 | 0.9683 | 0.9759 | 0.9643 | 0.9714 |
| cyclic6-31 | 0.9758 | 0.9750 | 0.9704 | 0.9751 |
| kat6-15 | 0.9437 | 0.9346 | 0.9182 | 0.9464 |
| kat6-31 | 0.9345 | 0.9383 | 0.9324 | 0.9529 |
| eco10-15 | 0.8435 | 0.8435 | 0.8947 | 0.8870 |
| eco10-31 | 0.8465 | 0.8423 | 0.9035 | 0.9010 |
| noon4-15 | 0.9745 | 0.9805 | 0.9697 | 0.9697 |
| noon4-31 | 0.9748 | 0.9801 | 0.9806 | 0.9735 |
| reimer5-15 | 0.7771 | 0.7736 | 0.8700 | 0.8726 |
| reimer5-31 | 0.7762 | 0.7749 | 0.8992 | 0.8897 |
| minrank_d_2_p_2_q_3_r_2-15 | 0.9419 | 1.0015 | 1.0008 | 0.9920 |
| minrank_d_2_p_2_q_3_r_2-31 | 1.0220 | 0.9273 | 1.0070 | 0.9931 |
| quadratic5-32003 | 0.9254 | 0.9075 | 0.9303 | 0.9468 |
| quadratic5-2147483647 | 0.9241 | 0.9232 | 0.9462 | 0.9534 |

## Registered fixed lean-bench cases

Each arm uses the declared five fixed repetitions, prepared IO-backed inputs
and complete structural basis hashing. Per case, arms run adjacent AB then BA.
The first experiment uses leased CPU 16; its single unchanged rerun uses CPU 57.
All 240 points complete and full result hashes agree. Per-call ratios normalize
totals by actual inner-repeat counts.

| Case | First geometric mean | Rerun geometric mean | All-point geometric mean | All-point median | All-point range |
| --- | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 1.0097 | 1.0179 | 1.0138 | 1.0150 | 0.9884–1.0333 |
| cyclic5 | 1.0053 | 1.0062 | 1.0058 | 1.0062 | 0.9872–1.0333 |
| cyclic6 | 0.9392 | 0.9580 | 0.9485 | 0.9687 | 0.7055–0.9853 |
| katsura3 | 0.9910 | 0.9887 | 0.9898 | 0.9867 | 0.9614–1.0313 |
| reimer5 | 0.8219 | 0.7841 | 0.8028 | 0.7836 | 0.6699–0.9542 |
| cyclic6Small | 1.0049 | 0.9889 | 0.9968 | 0.9694 | 0.9464–1.4371 |

Cyclic-4/5 show a small repeatable cost. Cyclic-6's original baseline-arm
variation pulls its geometric mean below the median. `cyclic6Small` includes a
large original B-arm observation (ratio 1.4371); the rerun is retained alongside
it, and the pooled geometric mean does not establish a consistent gain for that
case. Reimer's gain is larger, with all variation and both experiments retained.
No outlier is removed to improve the result.

## Reuse counts and prototypes

Read-only instrumentation preserves every basis and operation counter. Excluding
multiplication by 1, about 81% of Eco-10's symbolic reducer terms, 71% of Reimer-5's
and 59% of Katsura-6's are repeated. The probe uses one process per input and
its timings are not performance evidence. The earlier public-cache prototype
has diagnostic candidate geometric mean 0.9268 and median 0.9455; final production
adds private cache state and bounded comparison calls. Both source snapshots and
all prototype observations are retained separately.

## Reproduction and remaining work

Overlay an archive's exact `root-sources` onto its baseline. Use the pinned
toolchain and archived `compiled-driver` with its Hex requirement/package path
pointed to that checkout; build `production_compare`. Both arms use its default
production route. Build `hexgroebner_bench` for fixed-case exports. Metadata
retains the complete scripts, limits, arm order, executable identities, memory,
failures and raw outputs. Source fingerprinting uses staged source blobs.

Caching advances symbolic preprocessing rather than completing the SPEC. Compact
monomial/index operations, parallel and delayed-reduction kernels, finite
extensions, packed characteristic two, deterministic F4 proofs and balanced
matched comparator acceptance remain open. The preceding narrow-field report
records a substantial gap to current msolve; these cache measurements do not
establish that it has closed.

Retained evidence (SHA-256):

- [cache-production-bench-f4edebd7a46e-repeat.tar.gz](raw/cache-production-bench-f4edebd7a46e-repeat.tar.gz): `8c48627535a87de4fa34a9a3117ff717544667b30af9e3edcc663b120f88f110`
- [cache-production-bench-f4edebd7a46e.tar.gz](raw/cache-production-bench-f4edebd7a46e.tar.gz): `30b191fc435da64c88b25d7063a163ba456e7c446cdd06f2318deee24da87311`
- [cache-production-records-f4edebd7a46e.tar.gz](raw/cache-production-records-f4edebd7a46e.tar.gz): `bbc92b1bd8aa219f5c73d16acfaf7489910e1ed96eb8afa69283467ed3159ca7`
- [cache-production-validation.tar.gz](raw/cache-production-validation.tar.gz): `791c29885bddfabaf8cfbeacbf66d2213b1a0fb72ba87841696f54df1ff387c9`
- [cache-prototype-evidence.tar.gz](raw/cache-prototype-evidence.tar.gz): `2f26a14d81aa8102780d4cd3b5e561ab8b77a8073258474c44e636e8e65d77a2`

The combined tree with the calibrated narrow-field SIMD registrations also
passes the full 14187-job build, all 175/567/1288 oracle cases, all 30 benchmark
verifications and the four compiled native variants. The expanded native test
counts are 116054 scans, 198139 gathers and 3920 byte comparisons per variant.
These checks cover the integration; the earlier frozen timings are unchanged.

A separate post-cache Eco-10 profile uses the frozen `f4edebd7a46e` executable
and one leased CPU with 1999-Hz DWARF cycle sampling. No samples are lost.
The native narrow scan accounts for about 13.5% of sampled cycles; the two
reducer-lookup loops account for about 7.1%, and monomial preparation, allocation
and reference counting remain visible. Kernel symbols are restricted and some
sampled kernel work does not resolve. This is cost attribution from one retained
profile, rather than a speed comparison or an external-comparator observation.

- [cache-rebased-validation.tar.gz](raw/cache-rebased-validation.tar.gz): `791abf3b35a8e5fba809a244d8dd6f9be1fb868ce70b43dd3966f259c0c127c6`
- [cache-production-profile.tar.gz](raw/cache-production-profile.tar.gz): `29475a1daeb3467e03e2406a06d16ea307d5b29a5a20a4100bf1f5d90c5ac364`
