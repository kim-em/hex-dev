# Combined context-bound reducer cache and scalar access

The measured combined snapshot reduces diagnostic candidate time with B/A
geometric mean **0.8811**, median **0.8981**, across the original experiment and
its single unchanged rerun. The fixed cyclic6 case regresses in both experiments:
pooled geometric mean **1.4134**, median **1.4216**. Other fixed cases have
geometric means below one, with substantial variation. These observations do not
establish a universal gain or the fastest-open-source milestone.

## Exact source and scope

B has source fingerprint `57149c9cc2f7`, computational commit `92a3625b64`:
context-bound checkpoint reducer caching, proved packed scalar reads and local
reducer-lookup accounting. A is the frozen narrow-field SIMD production engine
with fingerprint `04e1c0a5f392`. Both arms include canonicalization, F4 and final
interreduction. Process timing adds startup, parsing and complete output.
Certificate generation, independent certification and kernel checking are
excluded. Exact source blobs, build inputs and executable SHA-256 identities
are retained independently of rebased commits. Reports lie outside the measured
source family. Earlier incremental measurements in the [cache](hexgroebner-reducer-cache.md)
and [access](hexgroebner-access.md) reports retain their historical snapshots;
they are not multiplied to predict this combined result.

The measured cache binds the explicit field, variable count and monomial order,
clearing entries on context changes. A full base-support/coefficient comparison
identifies each cached basis polynomial. Sealed public resumable states retain
the associated append-only arena; public raw calls in this measured snapshot
require that same arena,
as do raw packed polynomial and reducer-index operations. Future identifiers
wider than u32 bypass the packed cache key. The SPEC is unchanged.

## Validation

`lake build` passes implemented HexGroebner, HexGroebnerTheory and all emitter/
benchmark targets (2073 jobs); all Groebner conformance modules also pass.
Independent oracles pass 175 matrix, 567 SymPy/Singular basis and 1288 division,
normal-form and membership cases. All 30 benchmark verifications, downstream
kernel replay, DAG, phase, release-manifest, header/line and admission audits
pass. No new axiom or admission is introduced.

Tests independently change coefficients under identical support, and exercise
4200-term cache hits plus support and coefficient mismatches beyond byte 4096.
Field/order changes compare with fresh uncached products. Real F4 and long-row
checks take dynamic IO seeds so the compiler cannot evaluate them before the
instrumentation windows. Each window must independently increase the byte-call
counter. All four SIMD/scalar and Barrett/remainder variants pass with Clang23
and GCC16, ordinarily and under ASan/UBSan: each records 4051 byte comparisons,
116274 scans and 198271 gathers. Earlier failed instrumentation-window attempts
are retained and labelled: closed Boolean checks ran during module initialization.
Sanitizers instrument native C; portable comparisons and exact range guards
remain separate obligations.

## Measurement contract and all observations

Host chungus2, AMD EPYC 9455; Lean 4.35.0-rc3; generated C Clang23.1.0 and FFI
Clang23.1.3. One computation thread pins to an automatically leased CPU. Arms
run adjacent AB then BA, retaining every completed point, regression and outlier.
The diagnostic suite uses the same 16 grevlex inputs over 32003/2147483647 as
the incremental reports (SHA-256
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`).
Each process has ten seconds and a 16-GiB address-space allowance. The suite is
neither balanced nor held out. All 128 processes finish and complete bases plus
every non-resource counter agree; work/allocation reflect the cache changes.

| Diagnostic experiment | CPU | Candidate geometric mean | Median | Range | Process geometric mean | Median | Range |
| --- | ---: | ---: | ---: | --- | ---: | ---: | --- |
| Original | 37 | 0.8826 | 0.9070 | 0.6354–1.1490 | 0.9571 | 1.0054 | 0.5497–1.3884 |
| Rerun | 8 | 0.8796 | 0.8849 | 0.5215–3.1654 | 0.9393 | 0.8725 | 0.3870–3.2312 |

Pooled process geometric mean/median are 0.9482/0.9649. The rerun's diagnostic
candidate range includes a 3.1654 observation; it is retained without another
unchanged rerun. The fixed suite has 240 completed points, full structural
basis hashes equal, five declared repetitions, and ratios normalized by actual
inner repeats. CPUs are 14 and 26. Every completed sample is retained.

| Fixed case | Original geometric mean | Rerun geometric mean | Pooled geometric mean | Median | Range |
| --- | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 1.1098 | 0.7870 | 0.9346 | 0.9846 | 0.4682–1.9567 |
| cyclic5 | 0.8706 | 0.9211 | 0.8955 | 0.9273 | 0.5755–1.6241 |
| cyclic6 | 1.3105 | 1.5243 | 1.4134 | 1.4216 | 0.5957–2.6989 |
| katsura3 | 0.6880 | 0.8964 | 0.7853 | 0.9098 | 0.2535–1.3560 |
| reimer5 | 0.7449 | 0.6354 | 0.6880 | 0.6696 | 0.4221–1.2864 |
| cyclic6Small | 1.0125 | 0.9089 | 0.9593 | 1.0218 | 0.3611–2.6313 |

The fixed cyclic6 regression remains unresolved by these timing observations;
fixed modulus 65537 and diagnostic modulus 2147483647 both use four-byte
coefficients and the wide SIMD path. The latter does not reproduce the fixed
regression. Each experiment contributes ten paired ratios per fixed case;
17 of the 20 pooled cyclic6 ratios exceed one. This conflicts with the
incremental observations and remains unexplained by these timing data. No
completed sample is removed or attributed to host activity.
This combined snapshot has exactly one unchanged diagnostic rerun and one
unchanged fixed-suite rerun, both prompted by inconsistent adjacent-arm results.
These finite inputs do not establish a general complexity law. Wider matched
comparator campaigns and the SPEC's balanced, held-out acceptance remain open.
No language or runtime impossibility has been established.

## Retained evidence

- [hotloop-production-bench-57149c9cc2f7.tar.gz](raw/hotloop-production-bench-57149c9cc2f7.tar.gz): `5a33fe158e26a5bbbf6d78c9d3d2cd77d57f62bb36e7b9829b1eccff4687eaea`
- [hotloop-production-bench-57149c9cc2f7-repeat.tar.gz](raw/hotloop-production-bench-57149c9cc2f7-repeat.tar.gz): `2e8896a76f917997cfd7d3d4d8244fa279d7e0471e9a5b298de1cbfa084017c2`
- [hotloop-production-records-57149c9cc2f7.tar.gz](raw/hotloop-production-records-57149c9cc2f7.tar.gz): `c60cfdc968ad633a85ec7dc41abafb52016891500d0ad4a4ba85b918010e1cf0`
- [hotloop-production-records-57149c9cc2f7-repeat.tar.gz](raw/hotloop-production-records-57149c9cc2f7-repeat.tar.gz): `b86dae05d239eac86b03dbbc8de431c9f4d861f32f4165a931e7d7218db6efc5`
- [hotloop-final-validation.tar.gz](raw/hotloop-final-validation.tar.gz): `3e373cfc6c1c5d18ef8ab03e0bb843a96122bbde5ac76104b698227d5c27bfb9`


- [hotloop-context-profile.tar.gz](raw/hotloop-context-profile.tar.gz): `da4b3fb6328e8df8f16187f371d7911d8aee23fddb71479ec8b4ba62809ed0fe`
- [hotloop-context-profile-amortized.tar.gz](raw/hotloop-context-profile-amortized.tar.gz): `54d5ef57ee83c567c695c9e8347c145e980d45ad3327f3e4d1529af65d591788`

A separate cyclic6 profile compares this guarded engine with the pre-guard
lookup engine `cfb2c79989e2`. Initial whole-process profiles include initialization
and lose samples; they remain archived without algorithm attribution. A second
sampling protocol uses a two-second inner calibration and one repetition to
amortize initialization, retaining raw profiles, full-output hashes and exact
commands. Both captures lose zero samples and show similar cost distributions:
reference-count decrement about 7.6%, packed monomial combination 6.7–6.8%,
allocation 5.1–5.5% and freeing 4.9–5.2%. The context comparison has no separate
sample group above the 0.3% display threshold. These profiles do not identify
the cause of the short fixed-run regression or replace its completed timings.

The retained amortized profile rows report 21.816 ms per call for the guarded
engine and 22.807 ms for the pre-guard lookup engine, each at 128 inner repeats.
These are single sequential captures under perf, rather than adjacent AB/BA
scientific comparisons, and their baseline is `cfb2c79989e2` (PR-equivalent
computational commit `c42506d087`), not A. Metadata records host load averages
29.3/26.6/19.1. They do not reproduce the direction of the short fixed campaign
and do not establish its cause. `ReducerCache.multiply` self samples account for
0.34% and 0.31%, respectively. Exported `env.git_commit` is the invoking checkout
`a5b40ea5b7`, not either frozen binary's source; fingerprints and executable
SHA-256 identities identify the actual build inputs.

The baseline A cyclic6-31 candidate observations in the original diagnostic
campaign are about 22–25ms; the rerun is about 44ms. These absolute observations
show the changed execution context without rejecting or adjusting any sample.
All gains and losses have the reported dispersion, including Reimer/Katsura.

This source snapshot precedes exact cached-product validation against the current
arena. Its public raw cache entry points require the associated arena; the
subsequent implementation validates the exponent identities before reuse.
