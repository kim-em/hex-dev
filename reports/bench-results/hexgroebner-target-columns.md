# F4 target ordering by leading column

Joint Macaulay elimination orders target rows by decreasing leading-column
index, then increasing support size, using a stable sort. Columns themselves
follow decreasing monomial order, so smaller leading monomials enter first.
Known reducer pivots keep their meaning. Independent normal forms retain input
positions, and traced production moves each polynomial with its derivation
root. Sorting work is charged before execution. Missing columns still return
`representation.index`, including when a public malformed matrix is sorted.

Measured implementation `b9c671b4f9af`, computational commit `8c565f0804`,
is frozen by a fresh detached 188-job build. Its default driver SHA256 is
`74fa1f6f50cb5d7cfebd733eafd0fb0fbbfbf64665ef794db1d3e3541bd219c7`.
Baseline `0cb80bf73a4a` has the same executable as scheduling source
`6ede9cb261a4`: `2ece3bf2646f90393331ce349043b8a19adb02d236ee1bf300337ceaf9e9bd67`.
Exact source blobs, toolchain, helpers, executable hashes, inputs, full outputs,
GNU-time child RSS, host load and every completed sample are retained in the
capsules below. The final source docstring only describes the measured policy.

The small suite has 16 development inputs in seven families at primes 32003
and 2147483647. The medium suite has 14 inputs, two fields for each of cyclic7,
Katsura8, Eco11, Noon5, Reimer6, MinRank and dense quadratic6. The public
structured inputs come from GamBa source
`f18c2db3a288f20f63f752b44e0171cf1cb86163`; variable names are normalized and
coefficients reduced in the explicit field. Dense quadratics use seed 10987
and the same integer coefficients in both fields. The medium builder and exact
inputs are retained. These are development cases, not held-out inputs or the
SPEC's performance acceptance suite.

Each case uses adjacent AB then BA on one automatically leased CPU of the
shared AMD EPYC 9455 host, one algorithm thread and the pinned Lean 4.35.0-rc3
toolchain. Each observation retains its first campaign and single permitted
unchanged repeat. Different observations may run concurrently on distinct
leased CPUs; placement does not imply isolation. Every failure, timeout and
outlier is retained. No further unchanged repeats are used. Candidate time
includes canonical packing, F4 and final interreduction. Whole-process time
adds initialization, input parsing, complete output and identical GNU-time
wrappers. Certificate generation, independent final certification and kernel
replay are separate and excluded here. Timing uses grevlex and default degree
scheduling; conformance checks both strategies and all supported orders.

| Observation | Complete basis pairs | Candidate B/A | Process B/A | Equal-family process |
| --- | ---: | ---: | ---: | ---: |
| small | 64 | 1.0223 | 1.0005 | 1.0055 |
| medium | 56 | 1.0102 | 0.9218 | 0.9218 |

The CLI first/repeat CPUs are 75/61 (small) and 74/22 (medium); the fixed
sweeps use 77/85. Peak child RSS is 42616/42192 KiB for the small baseline/new
arms and 97908/97412 KiB for the medium arms. Code uses the existing exact
AVX2 dispatch where supported; this change adds no native arithmetic or ISA
requirement. Lean's generated-C compiler is Clang 23.1.0, with native FFI
compiled by Clang 23.1.3; exact flags and effective host features remain in
source/build metadata.

All 240 CLI processes succeed and all 120 complete basis pairs agree; there
are zero failures or timeouts. The small aggregate is essentially flat and
includes regressions. Medium whole-process time falls in this observation,
but candidate-only time does not establish an aggregate gain.

| Family | Small candidate | Small process | Medium candidate | Medium process |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 0.9789 | 0.9661 | 1.0005 | 1.0187 |
| dense-quadratic | 1.3312 | 1.1595 | 1.0092 | 0.7722 |
| eco | 0.9298 | 0.9698 | 0.8219 | 0.8387 |
| kat | 1.0161 | 1.3036 | 1.0728 | 1.0145 |
| minrank | 0.9682 | 0.6844 | 1.1836 | 0.8398 |
| noon | 1.1877 | 1.3310 | 1.0473 | 1.0392 |
| reimer | 0.8609 | 0.8054 | 0.9729 | 0.9681 |

The small candidate range is 0.3581–9.0263 and process range 0.2428–8.8958.
The medium candidate range is 0.3040–6.0311 and process range 0.3579–1.4858.
For quadratic6 at 32003, first AB candidate time rises 4.627592→27.909451 ms;
the repeat AB falls 18.771139→5.705960 ms, with identical algorithm counters
within each arm. These observations do not isolate runtime or host causes.

The deterministic counter changes give more direct evidence of reduced matrix
work in several larger cases. They also expose regressions. At 2147483647:

| Input | Entries before | Entries after | Work before | Work after |
| --- | ---: | ---: | ---: | ---: |
| cyclic7-31 | 2442163 | 2399624 | 128588385 | 125114617 |
| kat8-31 | 292333 | 277379 | 9752892 | 9321758 |
| eco11-31 | 10032086 | 8816611 | 679429887 | 567105617 |
| noon5-31 | 62570 | 61743 | 1635185 | 1627558 |
| reimer6-31 | 2158564 | 1893326 | 43779858 | 37443398 |
| minrank_d_2_p_2_q_4_r_2-31 | 8402 | 8402 | 98660 | 98660 |
| quadratic6-31 | 33102 | 33090 | 846124 | 845900 |
| cyclic5-31 | 9067 | 9419 | 280219 | 284015 |

MinRank has unchanged non-timing counters; its timing changes cannot be
attributed to fewer recorded algebraic operations. Cyclic5 increases fill and
work. No uniform gain or fastest-implementation milestone is claimed.

The registered fixed sweep retains 240 points across both campaigns, with
five declared repetitions per case and actual inner repeats normalized. Every
complete structural output hash agrees.

| Fixed case | B/A mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 0.9928 | 0.9870 | 0.9537–1.0412 |
| cyclic5 | 1.0366 | 1.0141 | 0.9797–1.6326 |
| cyclic6 | 0.9945 | 0.9978 | 0.9595–1.0233 |
| katsura3 | 0.9662 | 0.9532 | 0.9154–1.0404 |
| reimer5 | 0.9417 | 0.9438 | 0.9093–0.9600 |
| cyclic6Small | 1.0227 | 1.0024 | 0.9926–1.4947 |

The earlier `967ae620e941` prototype is retained as a separate source snapshot.
Its pooled small/medium candidate ratios are 0.8643/0.8956 and process ratios
0.9778/0.9240; each has its own single repeat and all outliers, including a
25.4672 small candidate ratio. Its 240 fixed points are retained too. It is
not pooled with the final missing-column fallback implementation. Cross-snapshot
ratio differences are not an adjacent comparison between those implementations.

The implementation passes all 1958 conformance/theory targets, independent
175-case matrix, 567 unique SymPy/Singular basis and 1288 division oracles,
both CLI initialization profiles over 1134 scheduling profiles, four Clang and
four GCC ASan/UBSan native variants, 32 benchmark smoke checks, and dependency,
phase, release, header and size audits. All 1134 fixture bases remain equal;
347 profiles change counters. Reimer at 65537 reaches a largest sugar batch
of 58 with caps 64 and 1024 producing equal statistics and complete bases;
the 78-pair batch regression remains covered separately.

Tight work allowances may skip optional packed reducer-index preparation. A
fresh successful run therefore need not have the same statistics as an
unrestricted run. The regression checks its basis, scheduling and work bound;
every exhausted continuation still compares exact resumed statistics between
original and opposite incoming scheduling choices, and traced production also
compares derivations. The initial overstrict assertion and its diagnostic,
then the corrected complete validation, are retained. No library contract or
mathematical obligation is weakened.

Fastest-open-source coverage, additional comparators, parallel scaling, finite
extensions, probabilistic computation, trace reuse and the remaining producer
proofs are still required. These measurements establish no compiler/runtime
impossibility. The issue remains open.

- [target-columns-967ae620e941.tar.gz](raw/target-columns-967ae620e941.tar.gz): `671e9846ef47d06b8dc56f74e55b4e711b2389ca3dddd49d6bb5a064f0bac6fc`.
- [target-columns-validated-b9c671b4f9af.tar.gz](raw/target-columns-validated-b9c671b4f9af.tar.gz): `1eba883d758a6e716f85423e899cb6c2972f0838ace3e2d7b7cd16e5da41f1a1`.
- [target-columns-input-provenance.tar.gz](raw/target-columns-input-provenance.tar.gz): `ec291ab3a050ca1eec4792e2afa9ea61347d3b689df21c1335e06f34626456b1`.
