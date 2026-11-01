# Compact monomial indexing and joint target ordering

The implementation combines packed monomial hash buckets and links with stable
joint target ordering by decreasing leading-column index, then increasing
support size. Columns follow decreasing monomial order, so smaller leading
monomials enter first. Independent normal forms retain input positions; traced
production moves each derivation root with its polynomial. Hashes only filter
candidates, and exact exponent equality determines identity. Known reducer
pivots and both degree/sugar scheduling contracts are preserved.

Native owned lookup/insertion has a transparent portable model. It admits up
to 2047 variables and 4096 additional work units. Index growth, exponent
widening, unsupported geometry and tight allowances return the unchanged table
for portable continuation after the native frame. Native preparation remains
available through arity 4096, with ordinary portable coverage beyond it. The
packed index charges storage, chain visits, insertion and deterministic
rebuilding explicitly. Charged work is therefore not directly interchangeable
with the older counter definition; matrix entry/row counts remain comparable.

Measured source `23688dd217ce`, computational commit `ae5a8eecca`, has a fresh
272-job detached driver build and compute SHA256
`1e8d11d3f563315ca4b46734330e3f0de4d95105add58ce2ec21e781d61411b2`.
Baseline source `0cb80bf73a4a` has the same executable as scheduling source
`6ede9cb261a4`, SHA256
`2ece3bf2646f90393331ce349043b8a19adb02d236ee1bf300337ceaf9e9bd67`.
Exact source blobs, manifests, build/initializer evidence, helpers, executable
hashes, raw inputs/outputs, memory and failure records are retained.

The shared AMD EPYC 9455 host uses one requested algorithm thread and an automatically
leased CPU. Lean is 4.35.0-rc3, generated-C compiler Clang 23.1.0, native FFI
compiler Clang 23.1.3, with the existing exact AVX2 dispatch where supported.
Small/medium first and repeat CPUs are 58/95 and 55/57; fixed CPUs 12/34.
Placement is not isolation, and distinct observations may overlap. Each case
runs adjacent AB then BA. Every observation retains its first campaign and sole
unchanged repeat; no further unchanged repeat is used. Every completed sample,
outlier, failure and host context remains, with no activity filter. One small
repeat setup mistakenly names a manifest as the baseline binary; hash validation
rejects it before any measured process. Its error is retained and the corrected
command supplies the sole measured repeat.

The small suite has 16 development inputs in seven families at primes 32003
and 2147483647; the medium has 14 larger inputs in the same seven families and
fields. Both use grevlex and complete monic reduced bases. Inputs and the medium
builder/public-source license are in the target-ordering provenance capsules.
These fixed development cases are not held-out or SPEC acceptance coverage.
Candidate time includes canonical packing, F4 and final interreduction. Process
time adds initialization, parsing, complete output and identical GNU-time
wrappers. Certificate generation, independent final certification and kernel
replay are separate and excluded. Child peak RSS is measured after exec.

| Observation | Complete basis pairs | Candidate B/A | Median | Process B/A | Equal-family process |
| --- | ---: | ---: | ---: | ---: | ---: |
| small | 64 | 0.9121 | 0.9620 | 1.0145 | 1.0071 |
| medium | 56 | 0.9671 | 0.9426 | 0.9438 | 0.9438 |

All 240 CLI processes succeed and all 120 complete basis pairs agree, with zero
measured failures or timeouts. Medium process time improves in this observation;
small process time is essentially flat. Several family and fixed means regress,
so there is no uniform speedup claim.

| Family | Small candidate | Small process | Medium candidate | Medium process |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 1.0620 | 1.0676 | 0.9354 | 0.9578 |
| dense-quadratic | 0.8862 | 1.0612 | 1.2026 | 0.9700 |
| eco | 0.8858 | 0.8973 | 0.7844 | 0.8015 |
| kat | 0.9767 | 1.0553 | 0.9924 | 0.9821 |
| minrank | 0.9424 | 1.0868 | 1.1217 | 1.1276 |
| noon | 0.6315 | 0.9345 | 0.9305 | 0.9285 |
| reimer | 0.9305 | 0.9643 | 0.8656 | 0.8715 |

Small candidate ratios span 0.1073–3.7104 and process ratios 0.3970–2.8165.
Medium candidate ratios span 0.5909–4.0711 and process ratios 0.3653–2.2342.
Small Noon4 at 2147483647 first AB falls 22.558227→2.420738 ms, while Cyclic5
at that prime rises 3.300693→12.246964 ms. Medium quadratic6 at that prime
first BA rises 6.008586→24.461379 ms. Every outlier remains; counters alone
do not isolate runtime or host causes.

Peak baseline/new RSS is 42016/56384 KiB (small) and 97352/100680 KiB (medium).
Lower logical index storage does not establish lower observed process RSS.

Deterministic matrix entries at 2147483647 give evidence of changed elimination
work with the same output. Work-counter units also change with the packed
index, so their cross-source ratios are not used as a speed estimate.

| Medium input | Entries before | Entries after | Rows before | Rows after |
| --- | ---: | ---: | ---: | ---: |
| cyclic7-31 | 2442163 | 2399624 | 11816 | 11769 |
| kat8-31 | 292333 | 277379 | 4119 | 4037 |
| eco11-31 | 10032086 | 8816611 | 76764 | 63247 |
| noon5-31 | 62570 | 61743 | 2942 | 2939 |
| reimer6-31 | 2158564 | 1893326 | 10298 | 9519 |
| minrank_d_2_p_2_q_4_r_2-31 | 8402 | 8402 | 134 | 134 |
| quadratic6-31 | 33102 | 33090 | 666 | 666 |

Small Cyclic5 at that prime increases entries 9067→9419; MinRank matrix
counters are unchanged. Its timing changes cannot be attributed to fewer
recorded matrix operations. Exact per-input counters remain in pooled analysis.

The registered fixed sweep retains 240 points, five declared repetitions per
case, with actual inner repeats normalized and all complete structural output
hashes equal. The larger geometric means below are retained alongside their
medians and ranges; no fixed case is removed or rerun again.

| Fixed case | B/A mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.9837 | 0.9859 | 0.8251–1.2073 |
| cyclic5 | 1.0180 | 0.9991 | 0.8909–1.9115 |
| cyclic6 | 1.2314 | 1.0185 | 0.7957–3.3605 |
| katsura3 | 0.9537 | 0.9466 | 0.9038–1.0019 |
| reimer5 | 1.0514 | 0.9204 | 0.9012–3.4175 |
| cyclic6Small | 1.1122 | 0.9651 | 0.9354–2.6278 |

The initial combined `0dc44fb7437c` snapshot remains separate: its small/medium
candidate means are 0.9519/0.9340 and process means 0.9654/0.9399, with one
initial campaign each and 120 fixed points. It passed core builds, oracles and
native tests but failed the dependency audit on missing carrier registration.
Its direct exclusive-alias coverage was incomplete. Its capsule retains that
failure and the exact original test sources; it does not claim final validation.
Cross-snapshot ratio changes are not adjacent comparisons between the two
implementations. No snapshots are pooled.

Separate component observations remain in [compact indexing](hexgroebner-compact-index.md)
and [target ordering](hexgroebner-target-columns.md). The compact component's
capsule audit success summary was overbroad: its retained dependency error is
authoritative. The current source supplies registration, explicit work units,
private C helpers, toolchain-traced build flags and stronger ownership tests.

The current 2161-job conformance/theory/driver/bench build passes, as do all
175 matrix, 567 unique SymPy/Singular basis and 1288 division oracle cases,
1134 degree/sugar profiles, both CLI corpus checks, four Clang and four GCC
ASan/UBSan native variants, 32 bench smoke checks and every dependency, phase,
release, copyright and line-count audit. Independent equal tables are consumed
by native and portable paths at count/byte/work boundaries, including arbitrary
precision limits. Each native variant records 46 exclusive reuses and six
accepted workspace/exponent-aliased insertions; the harness requires positive
counts for both. Removing `ensure_exclusive` in a
separate native object compiles but fails the direct ownership comparison;
production source is unchanged. Instrumentation separates accepted operations,
non-inserting lookups, insertions and deferrals, including five F4 deferrals.

The issue stays open. Finite extensions, parallel scaling, probabilistic and
trace support, remaining producer proofs, broader comparator/held-out coverage
and the fastest-open-source milestone remain required. No compiler/runtime
impossibility is established.

- [packed-targets-reviewed-23688dd217ce.tar.gz](raw/packed-targets-reviewed-23688dd217ce.tar.gz): `d7378fde4c4ad9df323090980cd54fd6cf44d777c7275335c6a16aeb46dcd5f0`.
- [packed-targets-0dc44fb7437c.tar.gz](raw/packed-targets-0dc44fb7437c.tar.gz): `1aa783178061bb159838407192508d591a40c3bce74fc2b0d4fc3ec558ca3317`.
