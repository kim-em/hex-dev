# Exact Mersenne-prime SIMD experiments

The production implementation selects a dedicated transition for p = 2^31−1.
It folds contiguous products exactly and retains Montgomery reduction for
scattered updates. Generic field loops are unchanged. The current measurements
and validation are in “Separate dispatch”; earlier snapshots remain separate.

The prime is p=2147483647. For canonical factors and coefficients, x=ab<p².
The fold (x AND p)+(x>>31) is congruent to x modulo p and below 2p, so one
conditional subtraction is exact. The existing u32 row ABI supplies2a mod p;
modular halving recovers a as (m>>1)+(m AND 1)*1073741824. No buffer format,
field bound, output convention or work accounting changes. Other primes retain
the exact Montgomery or narrow Barrett implementation.

## Contiguous and scattered specialization

Snapshot `b3dd413988ad`, commit `a48d7dffa3`, specializes both layouts. The
matched kernel baseline is `7fa53b016617`, commit `ce08647c11`: production
code equals `70aacca874da`, with identical new benchmark registrations in both
arms. Diagnostic and existing fixed cases use the original frozen `70aacca874da`
executable. Kernel preparation is excluded; validation, allocation, elimination,
full decoded output and structural hashing are included. Benchmarks use full-rank
Cauchy matrices with exactly (n³−n)/3 entry updates plus quadratic overhead.
All retained measurements use a leased CPU, one thread and adjacent AB/BA order
on the shared host. Raw metadata records toolchain, ISA, load and binary hashes.
No CI timing is used for scientific claims.

The 96 kernel points on CPU 30 cover64/128/256/512 with three fixed outer
trials, 4 sec inner target and 32 sec call cap. Every complete output hash agrees.
All eight complexity fits are inconclusive; none is budget-truncated. These are
finite-size observations, not a complexity or overall-fastest claim.

| Matrix size | Contiguous geometric mean B/A | Even-column strided geometric mean B/A |
| ---: | ---: | ---: |
| 64 | 0.9238 | 1.4768 |
| 128 | 0.9503 | 1.3332 |
| 256 | 0.9888 | 1.2989 |
| 512 | 0.9268 | 1.1794 |

The scattered regression prevents selecting this variant for production.
Whole-system timings are variable and do not establish a broad F4 speedup.
Every full basis and every non-timing counter agrees. Exactly one unchanged
repeat is retained; every outlier remains in both runs.

| Diagnostic run | CPU | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | --- | ---: |
| Original | 12 | 0.8923 | 0.9774 | 0.3624–1.4818 | 0.9859 |
| Repeat | 54 | 0.9974 | 1.0053 | 0.5677–1.7608 | 1.0359 |

Pooled 128-process candidate geometric mean is 0.9434, median 0.9877, range 0.3624–1.7608; process geometric mean 1.0106. Existing fixed cases use other primes and retain 240 points, including the5.9096 cyclic6Small ratio. Per-case means, medians, ranges and all points remain in the analyses.

The 2065-job library/theory/emitter build passes. Its emitters pass175 matrix, 567 SymPy/Singular basis
and 1288 division oracle cases; fixture bytes are unchanged. Four Clang/GCC
ASan/UBSan variants pass native/portable equality, aliases, malformed prefixes
and budgets. The AVX2 F4 counter window includes 10111 actual Mersenne vectors;
scalar variants include zero. The two new registered benchmarks pass the32-case
bench verification gate in 5 sec. These are correctness checks, not performance
measurements. Full global conformance completion is recorded separately.

Archives contain source blobs for both kernel arms, compiled-driver source,
frozen executable hashes, exact commands, all completed samples and analyses.
SHA-256:

- [mersenne-kernels-b3dd413988ad.tar.gz](raw/mersenne-kernels-b3dd413988ad.tar.gz): `84bed5d83d0aecbee8a0fe8715c7a7ea50e07cb41d4e6e64c858e51e403bcc75`
- [mersenne-production-bench-b3dd413988ad-repeat.tar.gz](raw/mersenne-production-bench-b3dd413988ad-repeat.tar.gz): `6d9f0ee6ec37d3b0da2928db07e80cc6cfe7dd0583e526fc50c50163dd945eb5`
- [mersenne-production-bench-b3dd413988ad.tar.gz](raw/mersenne-production-bench-b3dd413988ad.tar.gz): `dc8cbe5acf3e69fd30ada640e546dd0e16116ee666ed1412f0e2ad2f1936fe5b`
- [mersenne-production-records-b3dd413988ad-repeat.tar.gz](raw/mersenne-production-records-b3dd413988ad-repeat.tar.gz): `325b801656a2d08028ec8a448160e2ca0e963dad3612ab6fa82f284af9558fc7`
- [mersenne-production-records-b3dd413988ad.tar.gz](raw/mersenne-production-records-b3dd413988ad.tar.gz): `21b712e517a6bfdcb66d9aa5672c75dddcf3b3f6d1d2eb3a559a2b581f1684ab`

## Contiguous-only specialization

`3b7fe1f161ed`, measured commit `30f48e8a77`, uses the exact fold only for
contiguous eight-entry updates. Scattered updates retain Montgomery reduction.
It uses the same matched benchmark baseline `7fa53b016617` and frozen diagnostic
baseline `70aacca874da`. All 96 kernel points on CPU 61 have matching complete
output hashes. All eight fits are inconclusive and none is budget-truncated.

| Matrix size | Contiguous geometric mean B/A | Even-column strided geometric mean B/A |
| ---: | ---: | ---: |
| 64 | 0.9878 | 0.9332 |
| 128 | 1.0058 | 1.0177 |
| 256 | 0.8394 | 1.0043 |
| 512 | 0.9081 | 1.0047 |

The contiguous ratios vary across the two implementation snapshots, especially
at 256 columns. These finite-size observations do not establish a reproducible
size-specific or full-system benefit. Scattered ratios in this snapshot remain
close to baseline. Complete-system results retain substantial variability and
do not establish general F4 leadership. All complete bases
and every non-timing counter agree. One unchanged repeat is retained.

| Diagnostic run | CPU | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | --- | ---: |
| Original | 70 | 0.9608 | 0.9560 | 0.6239–2.4448 | 0.9638 |
| Repeat | 70 | 0.9977 | 0.9866 | 0.7566–1.4749 | 0.9715 |

Pooled 128-process candidate geometric mean is 0.9790, median 0.9815,
range 0.6239–2.4448; process geometric mean 0.9676, median 0.9356,
range 0.5563–2.4741. Fixed cases retain 240 points on CPUs 71/22. Pooled
means are 0.9637 cyclic4, 1.0449 cyclic5, 1.0783 cyclic6, 1.0548 katsura3,
1.1094 reimer5 and 1.3535 cyclic6Small. The fixed regressions, including a
5.5145 ratio, remain in the evidence. No further unchanged repeat is used.

The u8/u16 scan disassemblies contain1894/1892 instructions respectively in
both frozen executables. After normalizing call target addresses and RIP
displacements, those instruction strings agree. Raw and normalized disassembly
are retained. This comparison is not a semantic proof, does not explain the
fixed timing differences and does not invalidate any completed sample.

The 2077-job library/theory/emitter rebuild, all 175/567/1288 oracle cases,
32-case bench verification and project DAG/phase/manifest/header/line/admission
audits pass. Four Clang and four GCC ASan/UBSan variants pass with 8351 actual
Mersenne vectors inside the AVX2 F4 window and zero for scalar variants. Full
all-project conformance completion is recorded separately. The validation
archive retains the failed concurrent build and successful sequential rebuild.

SHA-256:

- [mersenne-contiguous-kernels-3b7fe1f161ed.tar.gz](raw/mersenne-contiguous-kernels-3b7fe1f161ed.tar.gz): `8ee28ebc9bc0cfc68999fb9e3778db7863b92a6ddc4fd406c04ed9e9365b33bc`
- [mersenne-contiguous-production-bench-3b7fe1f161ed.tar.gz](raw/mersenne-contiguous-production-bench-3b7fe1f161ed.tar.gz): `8be923872dfdb7bfe9dad2f647cc61c98be0c1f7e969870ec937f559f298ccb5`
- [mersenne-contiguous-production-bench-3b7fe1f161ed-repeat.tar.gz](raw/mersenne-contiguous-production-bench-3b7fe1f161ed-repeat.tar.gz): `37ca3c4b71ba2400afc178b90a1e85bf1a43e80f7ed658e9e7a36e8296a2a9df`
- [mersenne-contiguous-production-records-3b7fe1f161ed.tar.gz](raw/mersenne-contiguous-production-records-3b7fe1f161ed.tar.gz): `78075f84209c7202a59df3adfa2b99a6b20d240711b86cdec126e062ea04dc08`
- [mersenne-contiguous-production-records-3b7fe1f161ed-repeat.tar.gz](raw/mersenne-contiguous-production-records-3b7fe1f161ed-repeat.tar.gz): `438bbeb46bdceb47a07b50e98f8f463db78822732eddc93ee291ee6131db922b`
- [mersenne-contiguous-validation.tar.gz](raw/mersenne-contiguous-validation.tar.gz): `79e6ea3ec4602a49ed47210997fae13fa8491cae1b875fbc5f56ac196a9b7e61`

## Diagnostic results by field

The existing diagnostic observations split by field as follows. Different
implementation snapshots remain separate; no extra timing run is introduced.

| Snapshot | Prime | Paired observations | Candidate geometric mean B/A | Candidate median | Process geometric mean |
| --- | ---: | ---: | ---: | ---: | ---: |
| Two-layout | 32003 | 32 | 0.9562 | 0.9745 | 1.0547 |
| Two-layout | 2147483647 | 32 | 0.9307 | 0.9972 | 0.9683 |
| Contiguous-only | 32003 | 32 | 0.9471 | 0.9490 | 0.9161 |
| Contiguous-only | 2147483647 | 32 | 1.0121 | 1.0023 | 1.0221 |

The original two-layout snapshot also completes the 14036-job full project
conformance build. Its sanitizer counters and completed validation logs are
retained in [mersenne-two-layout-validation.tar.gz](raw/mersenne-two-layout-validation.tar.gz), SHA-256 `2d83d6b3ff2238227f014f6230f1a9ae74214aef45fcf24ad6fa34d21e02bb92`.

## Separate dispatch

The selected implementation `d1278bde9bd5`, commit `76dfa8e649`, selects a
separate Mersenne transition once per bounded call. The generic u8, u16 and
u32 loops contain no Mersenne branch. Their normalized disassembly matches the
matched baseline: 1894, 1892 and 1912 instructions respectively. Address and
RIP-displacement normalization is retained with the raw disassembly and script;
this is supporting evidence, not a semantic proof.

The baseline is `a93136c7f112`, commit `aeed8d3bdf`. Production code equals
merged `f8c21c8235`. Both arms compile identical shared Cauchy helpers, benchmark
registrations and configuration; their drivers have identical source hashes.
The benchmark fingerprint includes the complete `bench/HexGroebner/` prefix.
All source blobs and both compiled-driver source trees are retained.

The 96-point kernel sweep on CPU 70 has matching complete output hashes. All
eight complexity fits are inconclusive and none is budget-truncated. Ratios
are finite-size observations for this implementation, without pooling earlier
compiled variants or claiming a full-system speedup.

| Size | Contiguous mean B/A | Median | Range | Strided mean B/A | Median | Range |
| ---: | ---: | ---: | --- | ---: | ---: | --- |
| 64 | 0.9750 | 0.9722 | 0.9606–1.0021 | 0.9909 | 0.9904 | 0.9521–1.0295 |
| 128 | 0.9187 | 0.9194 | 0.9149–0.9207 | 0.9791 | 0.9831 | 0.9428–1.0032 |
| 256 | 0.8687 | 0.8689 | 0.8618–0.8766 | 0.9689 | 0.9653 | 0.9419–1.0003 |
| 512 | 0.8163 | 0.8150 | 0.8102–0.8252 | 0.9685 | 0.9692 | 0.9344–0.9999 |

All 64 diagnostic processes have identical full bases and non-timing counters.
On CPU 33, candidate geometric mean B/A is 0.9981, median 0.9964, range
0.9713–1.0877; process geometric mean is 0.9951, median 0.9970, range
0.9497–1.0183. The field split follows. These samples do not establish a
full-system improvement. No unchanged repeat is used for this snapshot.

| Prime | Pairs | Candidate mean B/A | Median | Range | Process mean B/A |
| ---: | ---: | ---: | ---: | --- | ---: |
| 32003 | 16 | 1.0009 | 0.9974 | 0.9713–1.0877 | 0.9937 |
| 2147483647 | 16 | 0.9953 | 0.9932 | 0.9827–1.0200 | 0.9965 |

The matched fixed sweep retains all 120 points on CPU 71, with identical full
result hashes. Mean B/A is 0.9831 cyclic4, 0.9887 cyclic5, 0.9908 cyclic6,
0.9882 katsura3, 0.9920 reimer5 and 0.9900 cyclic6Small. Complete medians,
ranges and individual samples remain in the analyses.

The 2079-job library/theory/emitter build, all 30 Groebner conformance modules
in a 216-job build, all 175/567/1288 external oracle cases, 32-case benchmark
verification and project audits pass. Four Clang and four GCC ASan/UBSan
variants pass. Targeted contiguous products compare generic and specialized
paths at factors {0, 1, 2, 2^30−1, 2^30,p−1} and coefficients
{1, 2, 2^30, 2^30+1,p−1}, with an assertion that the fold executed. The F4
counter window includes 8351 actual Mersenne vectors; scalar variants use zero.
The two preceding snapshots also complete their 14036-job global conformance
builds; the validation archive retains those completed logs separately.

SHA-256:

- [mersenne-dispatch-kernels-d1278bde9bd5.tar.gz](raw/mersenne-dispatch-kernels-d1278bde9bd5.tar.gz): `724ee0937d1215b01640297b67643f19062023160896ef6e8140b3cb91ccfca8`
- [mersenne-dispatch-production-bench-d1278bde9bd5.tar.gz](raw/mersenne-dispatch-production-bench-d1278bde9bd5.tar.gz): `bb59a2aed5eff5e66e4fcb93b09ede5f620969abbf899ee5bdddeae36ace3538`
- [mersenne-dispatch-production-records-d1278bde9bd5.tar.gz](raw/mersenne-dispatch-production-records-d1278bde9bd5.tar.gz): `4e077b0ffa279a2dc7ff0e5626073aeeaefd1a32e732f1620bf77d826733403c`
- [mersenne-dispatch-validation.tar.gz](raw/mersenne-dispatch-validation.tar.gz): `7bb52de285ccef834fb3f2c92c1ec07bed6fb53e4a2109cf2526c7179fcf31a7`
