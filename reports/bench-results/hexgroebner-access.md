# Packed scalar reads and reducer lookup accounting

Two separate changes reduce F4 bookkeeping costs without changing basis choices
or operation counters. The packed-read diagnostic candidate B/A geometric mean
is **0.9745** (median 0.9757). The subsequent lookup change has geometric mean
**0.9606** (median 0.9502) across its original and single unchanged diagnostic
rerun. These are incremental before/after experiments with different baselines;
the ratios are not pooled across changes or multiplied into a claimed combined
speedup. Neither establishes the fastest-open-source milestone.

## Exact behavior

`Packed.read` remains the byte-based kernel definition. A proved `@[csimp]`
function equality selects `readFast` during compilation: it checks the complete
scalar range and an exact USize round trip once, then uses unboxed byte indices.
The fallback repeats the original byte reads, preserving partial-buffer and
arbitrary-precision-index behavior. The proof covers all widths, arrays and
indices and introduces only the existing `propext`/`Quot.sound` dependencies.
No extern or new axiom is used. The separate eight-byte metadata rewrite is
unchanged. Generated C retains the complete check and `lean_byte_array_uget`
accesses, rather than a per-byte Nat range check in the valid branch.

Reducer lookup previously rebuilt the workspace/statistics through the shared
computation monad at every visited node and edge list. Its read-only traversal
now accumulates work locally and commits its exact charged prefix once. The
same depth-first order, sparse-row preference, degree preference and tie
handling remain. A failed indivisible charge retains the counter before that
charge, just as before. Nothing updates the monomial arena during lookup.
Arbitrary-precision work accounting and parent exhaustion semantics remain.

## Validation

The packed-read build passes all 14187 jobs, the 175 matrix, 567 independent
SymPy/Singular basis and 1288 division/normal-form/membership cases, and all 30
benchmark verifications. Four compiled native variants also pass and execute
the extended packed-read checks. Tests compare every valid scalar index over
many byte patterns with the independent recursive little-endian decoder.
Ordinary-kernel examples cover normal, truncated and huge-index cases.

The combined lookup build passes all 14188 jobs, the same independent oracles
and all 30 benchmark verifications. A small explicit three-branch trie tests
every work cutoff, including the indivisible root edge-list charge, a nonzero
initial counter, all other statistics, unchanged arena data and equal-priority
tie selection. Full fixture work counters are unchanged, so no fixture update
is needed. DAG, phase, release-manifest, source/header and admission audits pass.
Neither change modifies native C, ownership or coefficient/monomial contracts.
The native byte comparator and sanitizer evidence belong to the preceding
[cache change](hexgroebner-reducer-cache.md).

## Measurement contract

All experiments use chungus2, AMD EPYC 9455, Lean 4.35.0-rc3, generated C with
bundled Clang 23.1.0 and FFI with system Clang 23.1.3. Each pins one computation
thread to an automatically leased CPU and runs adjacent AB then BA per case.
Executables are frozen before timing. Every completed sample, regression and
outlier is retained; there are no failures, timeouts or discarded samples.
One unchanged rerun is used only for the inconclusive experiments identified
below. Host activity never rejects a completed observation.

The diagnostic suite has 16 grevlex problems over 32003/2147483647: cyclic-5/6,
Katsura-6, Eco-10, Noon-4, Reimer-5, MinRank and fixed quadratics. It weights
cyclic twice and is neither balanced nor held out. Suite SHA-256 is
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
Each process has a ten-second timeout and 16-GiB address-space limit. Candidate
time includes canonicalization, F4 and final interreduction; process time adds
startup, parsing and complete output. Certificates, independent certification
and kernel checking are excluded. All full bases and every non-time counter
agree in all **192 processes**, giving 96 exact paired comparisons.

Packed-read B is fingerprint `096016b0e9fe` at `31b60e116c` (identical tree
to PR commit `972cc6fcc3`), against the frozen cache engine `f4edebd7a46e`. Lookup B is fingerprint `cfb2c79989e2`, with its
algorithm at `bf3916ff27` (PR equivalent `c42506d087`), against that frozen packed-
read engine. Later benchmark success guards and standalone selftest prints do
not change computational functions. Exact source blobs and executable hashes
identify the measured arms independently of rebased ancestry. Source manifests
identify build inputs, not later unpublished checkout work.

## Diagnostic observations

| Change / experiment | CPU | Candidate geometric mean | Median | Range | Process geometric mean | Median | Range |
| --- | ---: | ---: | ---: | --- | ---: | ---: | --- |
| Packed read | 63 | 0.9745 | 0.9757 | 0.9371–0.9976 | 0.9265 | 0.9267 | 0.8556–0.9931 |
| Lookup | 1 | 0.9698 | 0.9508 | 0.9213–1.6817 | 0.9782 | 0.9824 | 0.9100–1.0635 |
| Lookup rerun | 87 | 0.9514 | 0.9500 | 0.9232–1.0127 | 0.9785 | 0.9828 | 0.9313–1.0170 |

Packed reads have no unchanged diagnostic rerun. Their process observations
improve more than the candidate timer; startup/conversion costs are not
separately isolated, so this does not attribute that difference to a particular
stage. Lookup's first cyclic5-31 BA B candidate is 5.365 ms against A's
3.190 ms (ratio 1.6817); the process ratio is 1.0635. Its other block improves,
making the family inconclusive and motivating the one unchanged full-suite
rerun. Both datasets remain; the pooled lookup process mean/median are
0.9784/0.9826, range 0.9100–1.0635. This retains the large candidate observation
rather than treating the rerun as its replacement.

## Registered fixed lean-bench cases

The six fixed cases use declared five repetitions and complete structural
basis hashes. Preparation is excluded; canonicalization and final interreduction
are included. The default cases use modulus 65537; cyclic6Small uses 32003.
All **360 points** complete with matching full hashes. Ratios divide total time
by actual inner repeats before pairing. Packed-read's first cyclic6 observations
change direction between AB and BA, motivating its one unchanged rerun; lookup
has no unchanged fixed-case rerun. The two changes' points are never pooled.

| Change | Case | First geometric mean | Rerun geometric mean | Combined geometric mean | Combined median | Combined range |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| Packed read | cyclic4 | 0.9772 | 0.9784 | 0.9778 | 0.9619 | 0.8655–1.2856 |
| Packed read | cyclic5 | 0.9657 | 0.9860 | 0.9758 | 0.9658 | 0.8991–1.1240 |
| Packed read | cyclic6 | 1.0067 | 1.0034 | 1.0051 | 0.9847 | 0.6969–1.6191 |
| Packed read | katsura3 | 0.9724 | 0.9878 | 0.9801 | 0.9751 | 0.7651–1.2476 |
| Packed read | reimer5 | 0.9569 | 0.9825 | 0.9696 | 0.9576 | 0.8608–1.3037 |
| Packed read | cyclic6Small | 0.9872 | 0.9576 | 0.9723 | 0.9844 | 0.8338–1.0863 |
| Lookup | cyclic4 | 0.9637 | — | 0.9637 | 0.9626 | 0.9478–0.9791 |
| Lookup | cyclic5 | 0.9618 | — | 0.9618 | 0.9620 | 0.9354–1.0041 |
| Lookup | cyclic6 | 0.9630 | — | 0.9630 | 0.9610 | 0.9569–0.9757 |
| Lookup | katsura3 | 0.9693 | — | 0.9693 | 0.9686 | 0.9541–0.9856 |
| Lookup | reimer5 | 0.9458 | — | 0.9458 | 0.9464 | 0.9377–0.9533 |
| Lookup | cyclic6Small | 0.9666 | — | 0.9666 | 0.9662 | 0.9602–0.9730 |

Packed-read CPUs are 55 and 60; lookup uses CPU 60. The packed-read rerun has
large observations in both directions, including cyclic6 ratios 0.6969–1.6191.
Its pooled cyclic6 geometric mean is 1.0051, so no consistent improvement is
established for that case. Other fixed cases have pooled geometric means below
one, with every spread retained. The lookup fixed-case geometric means are
0.9458–0.9693; cyclic5 includes an individual 1.0041 ratio. These finite fixed-
input observations do not prove a general complexity law or universal gain.

## Prototype, reproduction and remaining work

The earlier indexed-read prototype clones the pre-cache algorithm and has
candidate geometric mean 0.9812, median 0.9799 over its 64 diagnostic processes.
It is a separate implementation and is not pooled with production. Its exact
Lean/Lake sources, inputs and every completed sample are retained.

Overlay each production archive's `root-sources` onto its recorded baseline,
use the pinned toolchain and archived `compiled-driver`, and build
`production_compare`. Its default path runs production without `--reference`.
Build `hexgroebner_bench` for registered cases. Archived scripts retain the
arm order, CPU lease, limits, exact commands, memory, raw outputs and executable
identities; analysis scripts verify complete outputs and non-time counters.
Validation includes source and generated-C snapshots. The lookup and read
experiments have independent baselines; use their respective manifests.

These changes reduce representation and accounting costs within Lean. They
supply no evidence that language changes are necessary to reach leadership.
The [narrow-field report](hexgroebner-small-fields.md) records the substantial
remaining msolve gap before caching and these changes; no fresh matched
external sweep is included here. Irregular monomial operations, sparse/dense
elimination, parallelism, extension/characteristic-two coverage, deterministic
F4 theory and the fixed balanced, held-out comparator campaigns remain open.

Retained evidence (SHA-256):

- [packed-read-production-bench-096016b0e9fe-repeat.tar.gz](raw/packed-read-production-bench-096016b0e9fe-repeat.tar.gz): `8cc31860f0b59f0360d04ec4529486e5d7c690bd0221a6c5bd609fd5e370fd72`
- [packed-read-production-bench-096016b0e9fe.tar.gz](raw/packed-read-production-bench-096016b0e9fe.tar.gz): `3257cafb52c40f7486d6e4e06341fbc5d1117c24db66ea0b9cf61b2c8021ca3d`
- [packed-read-production-records-096016b0e9fe.tar.gz](raw/packed-read-production-records-096016b0e9fe.tar.gz): `c33d2bf0425d2c23f8dd08c14e96bc21fbd2e624e920b2fdfdbc60cef945982a`
- [reducer-find-production-bench-cfb2c79989e2.tar.gz](raw/reducer-find-production-bench-cfb2c79989e2.tar.gz): `a36ac5749d39b585e0449b12a10ca689c34845f6d3e9b4d1cd6120d88da64b80`
- [reducer-find-production-records-cfb2c79989e2-repeat.tar.gz](raw/reducer-find-production-records-cfb2c79989e2-repeat.tar.gz): `abfe2ab2c021f5c03ffb840882f1f4bd6380e996ac2d2bd545bbdb6ade6b415c`
- [reducer-find-production-records-cfb2c79989e2.tar.gz](raw/reducer-find-production-records-cfb2c79989e2.tar.gz): `9a543ed425b7273da9e1209727dcccdc321158e0380c3a2c0cf547d0a0243dbb`
- [groebner-access-validation.tar.gz](raw/groebner-access-validation.tar.gz): `b1fd09cbe0e1c46e32d03959dd07d82efa28c8cdfb2be7ec65d0e1062cd5239c`
- [packed-read-indexed-prototype.tar.gz](raw/packed-read-indexed-prototype.tar.gz): `f73ec0584a2aee2f14f8defc9f5815cfbf1307bf966b1b608ce2609f9dcc04f5`
