# F4 product-cache and owned-loop experiments

The production engine keeps symbolic reducer caching. The additional S-pair
row cache, general monomial-product map, stronger pair hash and owned support
loop below are excluded from production: these experiments do not establish
consistent gains sufficient to justify their cumulative complexity. No language
or runtime impossibility follows from these results.

## Contract and reproducibility

Every timed arm is a frozen production executable on chungus2 (AMD EPYC 9455),
Lean 4.35.0-rc3, bundled Clang 23.1.0 and FFI Clang 23.1.3. One computation
thread uses an automatically leased CPU. Inputs run adjacent AB then BA, with
all completed samples retained regardless of host activity. Each diagnostic
experiment has 16 grevlex inputs over 32003 and 2147483647: cyclic-5/6,
Katsura-6, Eco-10, Noon-4, Reimer-5, MinRank and fixed quadratics. This is neither
a balanced nor held-out acceptance suite. Suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
Each process has a ten-second timeout and 16-GiB address-space cap.

Candidate timing includes canonicalization, F4 and final interreduction.
Process timing additionally includes parsing, startup and complete output.
Certificate generation, independent certification and kernel checking are
separate and excluded. All processes finish successfully, with equal complete
bases. S-pair caching and general product memoization change resource charges;
all other non-time counters agree. Hash-only and owned-loop contrasts preserve
every non-time counter. Fixed lean-bench cases verify full structural basis
hashes and normalize total nanoseconds by actual inner repeats.

Archives retain exact staged source manifests, source blobs, executable hashes,
commands, CPU/thread context, peak process memory, raw outputs and analysis.
Source identities are content fingerprints, independent of later rebases.
Overlay `root-sources` on the declared baseline and use the archived driver and
pinned toolchain to reproduce the default `production_compare` route. The
computational library remains Mathlib-free throughout.

## Diagnostic contrasts

Ratios are B/A. Each line has its own baseline; ratios across different changes
are never pooled or multiplied. Original and one unchanged rerun are pooled
only within the same contrast. No additional unchanged reruns are performed.

| Contrast | B fingerprint | CPUs | Processes | Candidate geometric mean | Median | Range | Process geometric mean |
| --- | --- | --- | ---: | ---: | ---: | --- | ---: |
| S-pair row cache vs symbolic-only cache/read/lookup | a8a18555d30d | 48, 18 | 128 | 0.9829 | 0.9763 | 0.8009–1.4713 | 0.9648 |
| General product map vs S-pair row cache | d87ac129f886 | 14 | 64 | 0.9904 | 1.0289 | 0.5118–1.3387 | 0.9503 |
| Mixed pair hash plus product map vs S-pair row cache | 50329d969663 | 19 | 64 | 0.9955 | 0.9884 | 0.9462–1.0603 | 0.9805 |
| Mixed pair hash vs identity hash, both product maps | 50329d969663 | 85 | 64 | 0.9980 | 0.9947 | 0.9600–1.0535 | 0.9952 |
| Owned support loop vs per-term state updates, both mixed maps | 15b6fea84d14 | 88, 56 | 128 | 0.9863 | 0.9832 | 0.3603–2.3679 | 0.9942 |

The S-pair cache has 120 fixed benchmark points: case geometric means range
0.9678–1.0070. Its original Eco observations regress by roughly 2–10%; the
unchanged diagnostic rerun remains mixed. The general map has no fixed-case
campaign. The mixed-hash map has 120 fixed points: cyclic4 1.1058, cyclic5
1.0608, cyclic6 1.2112, Katsura3 1.0134, Reimer5 0.9724 and cyclic6Small
1.0592. Its poor fixed results are retained without an unchanged rerun.

Owned-loop fixed cases have one unchanged rerun after large AB/BA disagreement,
240 completed points in total. Pooled results retain substantial variation:

| Case | Geometric mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.8642 | 0.9944 | 0.5456–1.0211 |
| cyclic5 | 0.9813 | 0.9775 | 0.9378–1.0320 |
| cyclic6 | 0.8978 | 0.9711 | 0.2281–1.2760 |
| katsura3 | 0.9996 | 1.0023 | 0.9281–1.0345 |
| reimer5 | 0.9763 | 0.9582 | 0.7296–1.2618 |
| cyclic6Small | 0.9546 | 0.9568 | 0.6786–2.0895 |

The owned-loop first diagnostic mean is 1.0125 and its rerun 0.9607. Its
first fixed cyclic6 mean is 0.7867 and rerun 1.0247; pooled median 0.9711
is much nearer one than the geometric mean 0.8978. These disagreements and
outliers do not support attributing the geometric-mean improvement solely to
the loop rewrite. Its extra product map is therefore omitted along with the
other variants.

## Representation, tests and attribution

The S-pair variant caches multiplied basis faces but records fresh derivations.
The general map normalizes commutative pairs of stable u32 IDs into exact u64
keys, caps entries at 32768 and charges twelve logical bytes per entry. Exact
key equality handles hash collisions. Overflow-safe widening preserves IDs.
The mixed-hash variant uses a transparent SplitMix avalanche rather than the
identity UInt64 hash; the change introduces no new axiom and does not change
global UInt64 hashing. The owned loop holds the table and accumulated work
locally, committing the same exhaustion prefix as the per-term loop.

All variants pass complete basis/certificate fixtures and their applicable
library/theory builds, independent 175 matrix, 567 SymPy/Singular basis and
1288 division/normal-form/membership oracles. The general map covers capacity,
width changes and parent work/byte limits. The owned-loop fixtures match the
mixed-map fixture bytes, including all resource counters. Native/portable paths
agree. Validation logs include project audits and generated C where inspected.
These facts establish tested behavior, not a proof of the full deterministic
F4 specification or completion of the overall issue.

An untimed native probe finds repeated products in about 95.8% of Eco-10's,
94.6% of Reimer-5's and 82% of cyclic6's product calls. Every complete basis
and non-time counter matches the uninstrumented engine. The existing arena
already interns equal monomials, so this repetition count alone does not
predict a useful second map. Probe wall times are not timing evidence.

A separate owned-loop Eco-10 profile uses CPU 27 and 1999-Hz DWARF cycle
sampling, with no lost samples. Native scanning has about 13.89% of samples,
allocation 3.38%, reference-count decrement 3.26%, the owned support loop 2.27%
and symbolic preprocessing 2.12%. About 18.12% is unresolved kernel work;
these percentages are not rescaled or attributed to an algorithm. This is one
cost profile, not an AB timing experiment. It supplies no evidence requiring
language changes before further algorithmic improvements.

## Retained evidence

SHA-256 values cover every archive, including negative and inconclusive results:

- [spair-cache-production-bench-a8a18555d30d.tar.gz](raw/spair-cache-production-bench-a8a18555d30d.tar.gz): `361159fa2b85b3735f6409f269dc66d9f0de255cac23e62e395ccf8e5d8af7c0`
- [spair-cache-production-records-a8a18555d30d.tar.gz](raw/spair-cache-production-records-a8a18555d30d.tar.gz): `0297db03aed966f660a4bcf53115ec3952e2c2c37a882b761e1afe5319aee7cf`
- [spair-cache-production-records-a8a18555d30d-repeat.tar.gz](raw/spair-cache-production-records-a8a18555d30d-repeat.tar.gz): `2f7123bf6559aa20069bf57cd83c60a16d494f306c1d9d71565f0f955aff742d`
- [spair-cache-validation.tar.gz](raw/spair-cache-validation.tar.gz): `090e84281783fd565a19dffc3045d0bb526317c9f6e64b274e2f7dce6150fad4`
- [spair-monomial-reuse-probe.tar.gz](raw/spair-monomial-reuse-probe.tar.gz): `4f7050bbee6a7ff27f359ae3db0ee685a387ba92dbf29e51976d33241e83adad`
- [product-cache-production-records-d87ac129f886.tar.gz](raw/product-cache-production-records-d87ac129f886.tar.gz): `c2bb775931f43e09922ea7691114f90af46e68d558a19362866ec97e152f0d5b`
- [hex-groebner-product-cache-production-validation.tar.gz](raw/hex-groebner-product-cache-production-validation.tar.gz): `a8d4db1d9d4e60241f7ee2478d4b9ad0edfb83f1cbb5bd1e50e15f5e33e226aa`
- [hash-quality-records-50329d969663.tar.gz](raw/hash-quality-records-50329d969663.tar.gz): `145b9c881c9e8a393233267eb6aa7fadae90962d59ad79be967fefcb71828555`
- [product-hash-production-bench-50329d969663.tar.gz](raw/product-hash-production-bench-50329d969663.tar.gz): `28508d183db8f563b0c22b0f40226ef1bf73bad927c12d4c964ac42f1d64e01d`
- [product-hash-production-records-50329d969663.tar.gz](raw/product-hash-production-records-50329d969663.tar.gz): `cfc0dd377ef2615ccd46b62d830c7e06bcd2f2829462622af62a400f994adfb4`
- [hex-groebner-product-hash-production-validation.tar.gz](raw/hex-groebner-product-hash-production-validation.tar.gz): `c9c98bad60442653319190ed78011b60f533ac660f66ff30c4eb0d8a75685d4b`
- [product-batch-production-bench-15b6fea84d14.tar.gz](raw/product-batch-production-bench-15b6fea84d14.tar.gz): `871ded6d09cfcddb45f4f3db3844148422c1c5dbe7a854449c6dbef7d3486e7c`
- [product-batch-production-bench-15b6fea84d14-repeat.tar.gz](raw/product-batch-production-bench-15b6fea84d14-repeat.tar.gz): `95a3e3719cbb2c26c76264e341885f924b46a8aadfde261cc4e8aeade8f7770e`
- [product-batch-production-records-15b6fea84d14.tar.gz](raw/product-batch-production-records-15b6fea84d14.tar.gz): `4043da904a3895f3da0376704d6d54937cf4445fab5e2f30b396adbe919f4838`
- [product-batch-production-records-15b6fea84d14-repeat.tar.gz](raw/product-batch-production-records-15b6fea84d14-repeat.tar.gz): `bd384b0a5fd07db4ceb615eba21d7ed68105b39c9ca7e5aaf82f7d45d317e655`
- [hex-groebner-product-batch-production-validation.tar.gz](raw/hex-groebner-product-batch-production-validation.tar.gz): `a5eaef6644881461ae19261617c4575046babb37255424ea0db42222a6931df6`
