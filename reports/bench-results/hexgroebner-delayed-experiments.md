# Delayed reduction and native metadata-load experiments

The tested exact u64 delayed-reduction and native metadata-load prototypes do
not improve the existing multiplied-row engine consistently. They are not
selected for production. Delayed reduction remains a required optimization
objective; these finite observations do not establish a language limitation.
All completed samples, regressions, failed checks and exact source snapshots
remain available below.

## Contract and validation

The baseline is the frozen multiplied-row engine `c9fcd659ff93` (computational
commit `68086d6576`). Scalar delayed accumulation is `bca52b174b5d`, commit
`48ce93f451`; AVX2 accumulation is `89a5bdc1fd9b`, commit `ef86e98ba4`.
Two-byte fields use eight-byte dense slots and minimal-width sparse residues.
Each update adds an exact nonnegative multiple modulo p, reducing before a
u64 overflow. Pivot tests and sparse extraction reduce exactly. Four-lane
AVX2 handles contiguous and scattered updates, with a scalar fallback that
preserves the precise malformed/overflow prefix. Calls remain bounded by
4096 transitions; state, work, trace and parent-budget distinctions remain.

Portable bodies use exact Nat arithmetic. Native/portable states, projection
against immediate reduction, malformed and aliased buffers, large Nat fields,
near-u64-max accumulators and 5000-column resumed scans agree. Both scalar and
SIMD prototypes pass library/theory/conformance builds and the independent
175 matrix, 567 SymPy/Singular basis and 1288 division/membership oracles.
The SIMD snapshot passes a 14204-job build. Clang/GCC ASan+UBSan variants pass,
with 12475 delayed scan and 12848 delayed gather calls per variant, plus 4973
contiguous and 5121 scattered successful delayed vector calls in vector
variants. Protected-page tests cover both buffer ends, invalid coefficients,
index rejection, exact u64 boundary sums and overflow fallback. Classic paths
and all existing width/vector combinations remain exercised. Failed initial
prototype builds are retained and the recorded final builds pass.

The metadata-load prototype `58b8615b2967`, commit `e3f4e80cd1`, adds a checked
borrowed eight-byte little-endian native read, without alignment assumptions.
Its compiler rewrite is proved in Lean; truncated and arbitrary-precision
indices retain the old fallback. The native implementation itself is checked
against its portable definition. Both compilers' four sanitizer variants pass;
a dynamic F4 counter window ends at 86530 native word loads. A 2065-job
library/theory/bench/emitter build and the same external oracles pass. This
prototype changes no complete basis or operational counter.

## Full-system measurements

Host chungus2, shared AMD EPYC9455, Lean4.35.0-rc3, generated C Clang23.1.0,
FFI Clang23.1.3. One thread uses an automatically leased CPU. Every experiment
runs adjacent AB then BA. The unchanged 16-system diagnostic suite uses p32003
and 2147483647, ten-second per-process and 16-GiB address-space limits, complete
reduced grevlex output and equality of every full basis. Candidate time includes
canonicalization, F4 and final interreduction; process time additionally includes
startup, parsing and output. Certification and kernel checking are excluded.
The suite is diagnostic, neither balanced nor held out.

| Prototype | CPUs | Processes | Candidate B/A geometric mean | Median | Range | Process geometric mean |
| --- | --- | ---: | ---: | ---: | --- | ---: |
| Scalar delayed | 24/41 | 128 | 1.0071 | 1.0092 | 0.5420–2.1026 | 1.0186 |
| AVX2 delayed | 63 | 64 | 1.0110 | 1.0011 | 0.9241–1.5500 | 0.9595 |
| Native metadata load | 78 | 64 | 0.9961 | 0.9978 | 0.9538–1.0107 | 0.9508 |

Only the scalar experiment uses one unchanged diagnostic rerun after mixed
observations. The other prototypes use no unchanged rerun. Delayed workspace
work/byte counters change; all other counters and complete bases agree.

Registered fixed cases retain five declared repetitions, structural basis hashes
and actual inner-repeat normalization. All points complete and hashes agree.
Only cyclic6Small uses two-byte coefficients; the other fields do not select
this delayed path. Scalar has one unchanged rerun; AVX2 and metadata have none.

| Case | Scalar delayed B/A | AVX2 delayed B/A | Metadata B/A |
| --- | ---: | ---: | ---: |
| cyclic4 | 0.8606 | 0.9925 | 0.9885 |
| cyclic5 | 0.8880 | 1.0601 | 1.0284 |
| cyclic6 | 0.9884 | 1.0044 | 1.0271 |
| katsura3 | 0.9368 | 1.0539 | 1.0204 |
| reimer5 | 1.0522 | 1.0010 | 1.0221 |
| cyclic6Small | 1.0343 | 1.0028 | 1.0288 |

Scalar retains 240 points on its original and repeat CPUs; AVX2 retains 120 on
CPU62 and metadata 120 on CPU18. Medians, every individual ratio, CPU affinity,
load observations, failures and ranges remain in the raw analyses. Large
outliers in unaffected cases are retained, not filtered or used as evidence of
an algorithm change. No later rerun is used to select favorable samples.

## Matrix kernels and profile

Both campaigns compare the frozen immediate-reduction baseline with delayed
accumulation at p32003 on Cauchy matrices, contiguous or even-column scattered.
The registered custom ladder is 64/128/256/512 with three trial-major outer
trials, a four-second inner target and 32-second per-call cap. All 96 completed
points per campaign have equal full decoded result hashes. Every export reports
an inconclusive complexity verdict; none is budget-truncated. These are finite
size timing observations, not a complexity claim.

The scalar campaign originally supplied floor/ceiling flags that do not apply
to a custom ladder. The CLI ran the complete declared ladder for both arms.
The original command/metadata and an explicit protocol correction are retained;
no points were discarded. The SIMD campaign requests the actual full ladder.

| Layout/size | Scalar delayed B/A | AVX2 delayed B/A |
| --- | ---: | ---: |
| cauchy16/64 | 1.3533 | 1.1665 |
| cauchy16/128 | 1.5439 | 1.2256 |
| cauchy16/256 | 1.8365 | 1.2168 |
| cauchy16/512 | 2.1037 | 1.2102 |
| cauchy16Strided/64 | 1.2866 | 1.1408 |
| cauchy16Strided/128 | 1.3567 | 1.1464 |
| cauchy16Strided/256 | 1.3795 | 1.1012 |
| cauchy16Strided/512 | 1.4218 | 1.0748 |

Scalar uses CPU7; SIMD uses CPU21. Both remain slower than the existing exact
minimal-width AVX2 kernels on these sizes, despite the SIMD improvement over
scalar delayed arithmetic. Wider dense storage and four rather than eight
vector lanes are implementation tradeoffs; the timings alone do not isolate
their causal costs.

To explain the lack of a full-system benefit, two sequential two-second,
one-repetition perf captures profile cyclic6Small, CPU44, 1999Hz with DWARF
stacks. Neither loses samples. Baseline/native scan self samples are 3.41% and
3.60%; monomial combine is 6.93% and 6.74%, reference-count decrement 8.47% and
8.25%, allocation 5.68% and 5.18%, free 5.44% and 5.35%. Baseline and delayed
observe 16.886ms and 17.189ms per inner operation under perf; this sequential
profile is not an adjacent timing comparison. Restricted kernel symbols stay
unresolved. The samples point toward monomial/storage overhead as further work;
no costs are attributed to hypothetical compiler limitations.

## Retained evidence

Source manifests/blobs, frozen binary hashes, exact commands, complete raw
outputs, analyzers and validation logs are archived. Reconstruct `root-sources`
over the declared baseline and rebuild the archived driver; fixed cases use
`hexgroebner_bench`. Source identities are independent of invoking-checkout
commit/dirty fields in benchmark exports. SHA-256:

- [delayed-kernels-bca52b174b5d.tar.gz](raw/delayed-kernels-bca52b174b5d.tar.gz): `f302b49b3830336376d607629fa5d4b2bb14971dbf2a9542893bab29d3761803`
- [delayed-production-bench-bca52b174b5d.tar.gz](raw/delayed-production-bench-bca52b174b5d.tar.gz): `281a61530982796b27ec783fbd213c341278fa803cf4e0e43b00c6d9b33f80e8`
- [delayed-production-bench-bca52b174b5d-repeat.tar.gz](raw/delayed-production-bench-bca52b174b5d-repeat.tar.gz): `b6e2a5c54a10e03e5847a38d13b71b0b5bda5f39b00fe8f812256ce7631cbe81`
- [delayed-production-records-bca52b174b5d.tar.gz](raw/delayed-production-records-bca52b174b5d.tar.gz): `5fe693a34d6179913dc8d262d5989e9ad94534ef12159bb28f36e699d8fe2dd1`
- [delayed-production-records-bca52b174b5d-repeat.tar.gz](raw/delayed-production-records-bca52b174b5d-repeat.tar.gz): `09e9f00e613f4adddc000bd5da1e567d378b945d47ed6bf6b6e87e3b5d83382b`
- [delayed-scalar-validation.tar.gz](raw/delayed-scalar-validation.tar.gz): `0d984751b55ee3dd1daef83757515f21280e3ba67a30b9b91480e9ed6e9ba5f3`
- [delayed-simd-kernels-89a5bdc1fd9b.tar.gz](raw/delayed-simd-kernels-89a5bdc1fd9b.tar.gz): `27d90f1c929b35a596d1b8376fa3d28755e533d9281a39b0fed02914e5540a91`
- [delayed-simd-production-bench-89a5bdc1fd9b.tar.gz](raw/delayed-simd-production-bench-89a5bdc1fd9b.tar.gz): `ff1069f9f85577a3cb08ae6fdec7c0c3030284687e6283e419dd92a2e7692767`
- [delayed-simd-production-records-89a5bdc1fd9b.tar.gz](raw/delayed-simd-production-records-89a5bdc1fd9b.tar.gz): `f631f773c51f87ba7a790b181c57c3bf87b584fa5defb5814e22188a9096e8b3`
- [delayed-simd-validation.tar.gz](raw/delayed-simd-validation.tar.gz): `e388ac5b5601d018541512d5906f1da40c68ac42e971870d088ba81afcdc6273`
- [delayed-simd-profile.tar.gz](raw/delayed-simd-profile.tar.gz): `ad9c7eb91b3b27a43148d572dce415ef740e302f1f01a49ece901c805e79a959`
- [word-production-bench-58b8615b2967.tar.gz](raw/word-production-bench-58b8615b2967.tar.gz): `57673569b4e975716c191f22265222d5b635ca5b8725e42e0b0399fdd96ddceb`
- [word-production-records-58b8615b2967.tar.gz](raw/word-production-records-58b8615b2967.tar.gz): `95d3c21bb49801f8ebb9deadbd8e929985e8befbc017de5cbc89fdc27da8d92e`
- [word-production-validation.tar.gz](raw/word-production-validation.tar.gz): `52454f1fc469d7f02eb93f186707832d608ffecdd84ff9239d2fe9cefe9f97b8`
