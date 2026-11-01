# Packed storage, reducer and SIMD experiments

These are separate development experiments, each identified by its source
fingerprint and immutable capsule. Candidate time includes canonicalization,
F4 and final interreduction. Process time also includes launch, parsing and
complete output; it uses the historical full-initialization comparison driver,
so its ratios do not predict the standalone driver's process gains. Certificate
generation, independent certification and kernel checking are excluded.

Each diagnostic campaign uses 16 inputs from seven families at primes 32003 and
2147483647, with adjacent AB then BA, one thread on an automatically leased CPU.
Every completed process, outlier and failed setup log is retained. Every diagnostic
campaign has 64 successful processes and 32 agreeing complete reduced-basis
pairs. Fixed benchmarks use the declared five repetitions and preserve complete
structural output hashes. Repeats below are the single permitted unchanged
repeat after an inconclusive observation, never retries until a desired result.
Distinct source snapshots are never pooled. No held-out or leadership claim is made.

The baseline for products, columns, current trie, AVX-512 and reducer-choice
experiments is packed comparison `802ae51122d7`. The earlier two trie snapshots
use zero-scan baseline `f3d5acec8365`. Their linked kernels, toolchains and
executable hashes remain in their own manifests. Reported ratios are B/A;
values below one favor the experiment. All rows are research variants, not
production selections.

| Variant | Fingerprint | Diagnostic processes | Candidate geometric mean | Process geometric mean | Fixed points |
| --- | --- | ---: | ---: | ---: | ---: |
| products | `af771c7004b3` | 128 | 0.9677 | 0.9968 | 240 |
| columns | `0c885cbab97e` | 64 | 1.0339 | 1.0322 | 120 |
| columns-native | `2044daa7e3ba` | 128 | 0.9858 | 0.9983 | 240 |
| trie | `c6bdd8600d7c` | 64 | 0.9404 | 1.0545 | 120 |
| trie-validator | `de40637c328a` | 128 | 0.9337 | 0.9592 | 240 |
| trie-compare | `3949a0dadd7a` | 128 | 0.9237 | 0.9622 | 240 |
| avx512 | `f116ae6fb07a` | 128 | 0.9968 | 0.9836 | 240 |
| reducer-order | `0b76971083b4` | 64 | 1.0371 | 1.0632 | 120 |
| reducer-low | `51e45b030283` | 64 | 1.0495 | 1.0809 | 120 |
| minimal-reducers | `eb0b7c2d6b5e` | 64 | 1.0743 | 1.0815 | 120 |
| json-runtime | `802ae51122d7` | 64 | 0.9771 | 1.0150 | 0 |
| text | `802ae51122d7` | 64 | 1.1301 | 0.3854 | 0 |
| minimal-init | `802ae51122d7` | 128 | 1.4120 | 0.4654 | 0 |

A separate corrected sparse-first joint-target experiment (`668abb190c63`)
retains 128 diagnostic processes and 240 fixed points. Every one of its 64
complete basis pairs agrees; pooled candidate/process ratios are 0.9080/0.9129.
Fixed Reimer ratio is 0.5361 (median 0.5582), with matrix entries reduced from
960252 to 435489 at the large prime. Eco entries fall 3268590→2939286.
Sugar scheduling remains unchanged. The capsule also retains the original
`29215102b484` failure: two completed processes exposed a complete-basis mismatch
because independent final normal-form rows had been reordered. The correction
restricts ordering to joint elimination. The failed snapshot has its own source
manifest and is never pooled with the corrected one. These timing observations
precede traced-producer integration and its further conformance checks.

Batched support products preserve termwise failure prefixes and all computation
counters. They show a modest candidate gain without an overall process gain.
Pure packed column maps add preparation cost; native support translation
recovers some candidate time but remains flat overall. Their pooled fixed
`cyclic6Small` ratio is 1.0446, so this is not a uniform improvement.

The current packed reducer trie avoids boxed node temporaries and preserves
portable traversal choice, order and exact work exhaustion. It has the strongest
candidate evidence here (0.9237), but individual fixed cases remain mixed. The
new preparation cost changes only work/allocated counters, with all basis and
matrix statistics preserved. Separate later checks cover the maximum tree/stack
with read-only guard pages and Clang/GCC sanitizers; the 175/567/1288 independent
oracles pass after refreshing only charged work counters. These later tests do
not change the measured kernel implementation or retroactively change its source
fingerprint. Earlier trie variants remain separate observations.

The exact AVX-512 prototype handles sixteen entries with AVX2/scalar fallbacks,
coefficient-width specialization, contiguous Mersenne folding and u32 native
scatter. Both complete diagnostic campaigns agree in every non-timing counter;
pooled candidate ratio 0.9968 does not establish an F4 gain. Fixed Reimer's pooled
geometric mean is 1.0538, with median 0.9948; every outlier remains included.
The 96 Cauchy kernel points agree in full decoded output hashes, but all eight
exports have inconclusive complexity verdicts. These are finite-size kernel
observations, not complexity proofs:

| Matrix size | Contiguous AVX-512/AVX2 | Even-column strided AVX-512/AVX2 |
| --- | ---: | ---: |
| 64 | 0.9583 | 0.9924 |
| 128 | 0.9161 | 0.9829 |
| 256 | 0.7985 | 0.9337 |
| 512 | 0.7517 | 0.9315 |

AVX-512 validation comprises six Clang and six GCC ASan/UBSan variants and
1950 relevant conformance/theory targets. A later unchanged-kernel oracle rerun passes all 175 matrix, 567 reduced-basis
and 1288 division cases; the separate validation capsule retains its log. Its protocol's later eight-lane phrase is corrected in the
capsule scope file; the A/B definition identifies sixteen-lane experimental code.

Both higher-degree-first and lower-degree-first reducer preferences increase
candidate and fixed-system work. Restricting symbolic lookup to basis leading
monomials with no proper divisor also regresses: candidate 1.0743 and process
1.0815. It retains every basis polynomial and pair obligation, but Reimer31
matrix entries increase 960252→1064156, with work 15341887→18672374. Its
fixed Reimer ratio is 1.2213. None of these policies is selected. Their target
builds and complete-basis comparisons are evidence; no full conformance or
producer proof is claimed for these algorithmic research variants.

Frontend experiments keep the library source index `802ae51122d7` but change
external prototype files and hashes. Narrow JSON imports alone do not remove
broad initialization; the text frontend and minimal-initialization prototype
reduce process startup while regressing internal candidate time. Their old
msolve observations use a libtool wrapper and requested native flags stripped
by Nix. They are historical, biased in favor of Hex, and superseded by
[effective-native standalone comparisons](hexgroebner-driver.md). Source-family
fingerprints alone do not identify external driver code; each capsule retains
that code and its separate hashes. Generic older GCC labels do not override the
actual Clang toolchain recorded in scope corrections.

Each capsule contains raw outputs, schedules, host context, exact candidate and
baseline source blobs, executable hashes and the analysis scripts. Native checks
use Clang 23.1.3 and GCC 16.2.0 where explicitly stated; generated Lean C uses
the pinned SDK compiler. Native/portable comparisons and mathematical kernel
checking remain distinct from scientific timing. Whole-process memory is valid
only where the protocol explicitly records matched GNU-time wrappers; older
`wait4` parent-floor readings are not child-memory evidence.

- [prototype-products-af771c7004b3.tar.gz](raw/prototype-products-af771c7004b3.tar.gz): `648174baf4c7571d24e30f2d07d2911227dd8badee80217760aa09261bbf4aa6`.
- [prototype-columns-0c885cbab97e.tar.gz](raw/prototype-columns-0c885cbab97e.tar.gz): `485b6ebd532de6a0baa40431a9604e29a98bf6761ad9bd51580f701b70b02334`.
- [prototype-columns-native-2044daa7e3ba.tar.gz](raw/prototype-columns-native-2044daa7e3ba.tar.gz): `5171d6279b85f7c65de544f19cdac1e6a23b1b394d29a441f15d61243b099ccf`.
- [prototype-trie-c6bdd8600d7c.tar.gz](raw/prototype-trie-c6bdd8600d7c.tar.gz): `ef9565d304cf80d84a69e0f6e4995d37b7a9f303caf424a1e6a3b7f64aa48a3b`.
- [prototype-trie-validator-de40637c328a.tar.gz](raw/prototype-trie-validator-de40637c328a.tar.gz): `5e86a9003921346d9efa11adec8907625108621ebc75e683e5320268a882c088`.
- [prototype-trie-compare-3949a0dadd7a.tar.gz](raw/prototype-trie-compare-3949a0dadd7a.tar.gz): `da343f8e76d17f8688b02b9942c46b43e27d91b40da19aef923f54870df6fcdf`.
- [prototype-avx512-f116ae6fb07a.tar.gz](raw/prototype-avx512-f116ae6fb07a.tar.gz): `109db3422133a25aebc86d31f66176754037298998112bdfdc30556f2bf22d19`.
- [prototype-reducer-order-0b76971083b4.tar.gz](raw/prototype-reducer-order-0b76971083b4.tar.gz): `948b0cabc3c096283acc72cfe3bc5c332f0a64539a9d0b315ab14179706db42a`.
- [prototype-reducer-low-51e45b030283.tar.gz](raw/prototype-reducer-low-51e45b030283.tar.gz): `b55de7f8495eeecd4f5c8901aa08e7841264b66adca60dee6909ef6d7202a415`.
- [prototype-minimal-reducers-eb0b7c2d6b5e.tar.gz](raw/prototype-minimal-reducers-eb0b7c2d6b5e.tar.gz): `91ba76ee769c93cc2ffef15fe1d19c7a0e3857fc36120fbef436eef519f41d54`.
- [prototype-json-runtime-802ae51122d7.tar.gz](raw/prototype-json-runtime-802ae51122d7.tar.gz): `4ebf93af9cc4e9e6c3351dafb86289432609e17996a183ba15e65d8fb1224466`.
- [prototype-text-802ae51122d7.tar.gz](raw/prototype-text-802ae51122d7.tar.gz): `c65afdab001e550fb86b4ca0cdc0a06f8fc3ff1b54bd38d7639c11254113bda5`.
- [prototype-minimal-init-802ae51122d7.tar.gz](raw/prototype-minimal-init-802ae51122d7.tar.gz): `566e91fd3d040b89c7c5b0749c5ebf6cff3d5feabb60e62eaaef9049be3fe414`.

- [prototype-sparse-targets-668abb190c63.tar.gz](raw/prototype-sparse-targets-668abb190c63.tar.gz): `0d3f5b42634afd01227d9ad899b6d5b5f0d2a4b23b65186d6256d53f91a46abb`.
- [trie-validation-9e0ab9d9c2d6.tar.gz](raw/trie-validation-9e0ab9d9c2d6.tar.gz): `fd854c5b1b2a19d9564967430694bc41f7d58d3f5f9a59d7a895905c7a11db48`.

A larger-window trie prototype (`9fdfe4b5fab1`) admits 8192 nodes and 16383
charged visits. Its single CPU1 campaign has 64 successful processes and 32
agreeing complete bases, with candidate/process ratios 1.0010/0.9913 against
combined snapshot `a00d1a3e57a9`. All non-timing algorithm counters agree; these
inputs do not exercise the newly admitted interval. Maximum read-only guard
pages under Clang ASan/UBSan, the TrieConformance target, a 328-job core/bench
build and a fresh 188-job driver build pass. No full conformance or independent
oracle profile is claimed for this prototype. No unchanged repeat is used, and
it is not selected.

- [prototype-wide-trie-9fdfe4b5fab1.tar.gz](raw/prototype-wide-trie-9fdfe4b5fab1.tar.gz): `6f28f722540d475cb0a7b0fdee94ecefba16d36d95e15e8d5d435c5fa1a89449`.
