# Packed monomial-index experiment

The first packed-index snapshot `d5467b9f1aa8`, computational commit
`2786624da2`, is slower than the frozen multiplied-row baseline `c9fcd659ff93`.
This snapshot is retained as an intermediate experiment; subsequent fused
native lookup work has its own source identity and measurements.

Typed u32 heads and links replace boxed hash buckets. Stable identifiers and
exact exponent equality remain; semantic hashes only filter collision chains.
Growth doubles a power-of-two table at half load, and rebuilds in deterministic
identifier order. Index payload, temporary rebuild payload, initialization and
link/exponent visits count against parent bounds. Native searches visit at most
4096 links and 4096 exponent coordinates per call, with exact status/work prefixes.
Portable and native paths share the same charged contract. Forced collisions,
5000-entry resumed chains, width changes, malformed buffers, aliases, arbitrary
Nat budgets and every returned full basis agree with the reference.

A 14201-job build passes, including theory and all conformance. Clang/GCC four
ASan/UBSan variants pass with15978 native chain searches in the real F4 counter
window. All175 matrix,567 SymPy/Singular basis and1288 division oracles pass
after updating only the three work-counter fields for525 of567 F4 fixtures.
The initial oracle run reports that intentional fixture difference and remains
in the validation logs. All other fixture fields and full bases are unchanged.
DAG, phase, manifest, source/header audits pass.

Host chungus2, shared EPYC9455, Lean4.35.0-rc3, generated C Clang23.1.0 and
FFI Clang23.1.3. One thread, leased CPU91 for diagnostics and77 for fixed cases.
Adjacent AB then BA, unchanged16-system diagnostic suite over32003/2147483647,
10-second and16-GiB process limits, complete reduced grevlex basis comparison.
Candidate time includes canonicalization/F4/final interreduction; process time
includes startup/parse/output. Certification and kernel checking are excluded.
All64 processes complete and full bases/nonresource counters agree. Candidate
B/A geometric mean1.0652, median1.0735, range0.9732–1.1190; process geometric
mean0.9730, median0.9549, range0.8980–1.0520. These distinct boundaries do not
support an algorithmic gain. No unchanged rerun is used.

All120 registered fixed points complete with matching structural basis hashes,
five declared repetitions and actual inner-repeat normalization:

| Case | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 1.0686 | 1.0683 | 1.0401–1.0879 |
| cyclic5 | 1.0707 | 1.0739 | 1.0351–1.1039 |
| cyclic6 | 1.0964 | 1.0941 | 1.0898–1.1142 |
| katsura3 | 1.0613 | 1.0642 | 1.0182–1.0858 |
| reimer5 | 1.0777 | 1.0763 | 1.0717–1.0899 |
| cyclic6Small | 1.0925 | 1.0927 | 1.0801–1.1024 |

The regression motivated sequential perf captures on CPU74,1999Hz,DWARF,
one repetition with a two-second inner target forcyclic6Small. Neither loses
samples. Packed combine self samples6.53%, its loop3.96%, combineOwned3.18%,
native prepare2.88%, native search2.68%; allocation5.22%, decref8.85%,free5.23%.
These profiles point to repeated metadata reads and boundary bookkeeping as
further work. Sequential profiler runs are not matched timing evidence, and
unresolved kernel symbols remain unattributed. No language limitation follows.

Archives retain exact staged source blobs, manifests, frozen executable hashes,
commands, all samples and validation failures. Overlay root-sources on the
baseline and build the archived driver. SHA-256:

- [packed-index-production-bench-d5467b9f1aa8.tar.gz](raw/packed-index-production-bench-d5467b9f1aa8.tar.gz): `f04c674ffecbd8ab821c67e50d3f626b176c1cc1178bde40752482795a8562f7`
- [packed-index-production-records-d5467b9f1aa8.tar.gz](raw/packed-index-production-records-d5467b9f1aa8.tar.gz): `4093ab52f05f091f17169577a0d6a39779eaf0b50987ee6475a644c374c82b92`
- [packed-index-production-validation.tar.gz](raw/packed-index-production-validation.tar.gz): `7b30df7f2131fcf0c42e1ba554b217d26aff26fafeb6247f4d5dc6e3e2623a31`
- [packed-index-profile.tar.gz](raw/packed-index-profile.tar.gz): `5d5bdbffe2345f141937f7ce711635cde9bc8f587e9deff20793dc3d6e5e36b1`

## Fused lookup and validation snapshots

`e6dfbee3f2fc` (commit`05a36cbcaf`) fuses prepared-coordinate construction,
exact collision search and a successful table update. `fda88fabd49f`
(commit`382b0a405a`) additionally fuses validation. Both defer unsupported cases
to the exact reference. They retain the original table and budgets on failed
stages; prepared workspace bytes and every returned table field agree with the
reference, including aliased inputs and large Nat bounds. Four Clang/GCC
ASan/UBSan variants pass, with4819 successful native operations at the end of
the F4 counter window. The2111-job library/theory/bench/emitter builds and all
175/567/1288 independent oracles pass. These prototypes are intermediate
experiments; their C-to-Lean fallback is superseded by an explicit deferred
result returned to Lean before reference execution in later work.

The same baseline, suite, host and AB/BA protocol above apply. All64 diagnostic
processes per snapshot and120 fixed points per snapshot complete with equal
full bases/hashes. Only resource counters change. Neither uses an unchanged
repeat. Candidate and process boundaries retain their separate definitions.

| Snapshot | CPU | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | --- | ---: |
| e6dfbee3f2fc | 60 | 1.0287 | 1.0231 | 0.8575–2.0040 | 1.0292 |
| fda88fabd49f | 47 | 1.0029 | 1.0038 | 0.7063–1.3413 | 0.9411 |

| Fixed case | Fused lookup B/A | Fused validation B/A |
| --- | ---: | ---: |
| cyclic4 | 1.0546 | 1.0229 |
| cyclic5 | 1.0058 | 1.0249 |
| cyclic6 | 0.9380 | 1.0057 |
| katsura3 | 1.0549 | 1.0262 |
| reimer5 | 1.0745 | 0.8440 |
| cyclic6Small | 1.0002 | 1.0175 |

Fixed CPUs are17 and58. Complete per-case medians, ranges, individual ratios,
raw outputs, failures and load observations remain in the analyses. These
mixed observations do not justify selecting either snapshot for production.

## Native insertion snapshot

`e5a66b00cdff` (commit`b75ed97ee1`) additionally appends monomials without
crossing back to Lean when exponent width and hash capacity stay unchanged.
Growth and widening use the reference. All widths and aliased workspaces
match every reference result byte. Four Clang/GCC sanitizer variants pass,
with6625 successful native operations including1207 insertions at the end of
the F4 counter window. A14213-job full build and all external oracles pass.
The final counters include the late all-width tests; the earlier1196-insertion
run is also retained. Earlier failed prototype builds are retained and fixed.

The original has substantial variability, so exactly one unchanged repeat
follows. Every completed sample remains; neither run is discarded. All128
processes and240 fixed points complete with matching full bases/hashes.

| Diagnostic experiment | CPU | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | --- | ---: |
| Original | 73 | 1.1114 | 0.9984 | 0.8935–6.2956 | 1.1206 |
| Repeat | 93 | 0.9863 | 0.9870 | 0.9505–1.0240 | 0.9579 |

Pooled candidate geometric mean 1.0470, median 0.9902, range
0.8935–6.2956; process geometric mean 1.0361,
median 0.9645, range 0.4802–2.7160.

| Fixed case | Original geometric mean | Repeat geometric mean | Pooled geometric mean | Median | Range |
| --- | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 0.9840 | 0.9840 | 0.9840 | 0.9828 | 0.9308–1.0271 |
| cyclic5 | 1.6870 | 1.0830 | 1.3517 | 1.1446 | 1.0395–15.5404 |
| cyclic6 | 1.2855 | 0.9881 | 1.1270 | 0.9904 | 0.9042–2.9361 |
| katsura3 | 0.9799 | 0.9851 | 0.9825 | 0.9875 | 0.9119–1.0253 |
| reimer5 | 0.9887 | 0.9587 | 0.9736 | 0.9606 | 0.6554–1.3448 |
| cyclic6Small | 1.3935 | 1.0069 | 1.1845 | 1.0262 | 0.9544–2.4847 |

Fixed CPUs54/50. The repeated cyclic5 regression and the original15.54 ratio
remain. No additional unchanged repeat is used. Neither a consistent gain nor
a language limitation is established by these observations.

Additional archives retain source blobs/manifests, frozen executable hashes,
exact commands, all raw samples and validation logs. SHA-256:

- [monomial-hit-production-bench-e6dfbee3f2fc.tar.gz](raw/monomial-hit-production-bench-e6dfbee3f2fc.tar.gz): `1ece145eb9a6fcb0afe091e7488bd5c7864a6a40319bd70894e5f4149fc1be23`
- [monomial-hit-production-records-e6dfbee3f2fc.tar.gz](raw/monomial-hit-production-records-e6dfbee3f2fc.tar.gz): `3017066950fec15c7ed305f369aa3df2b6895c7e91de492a7429266209b5a843`
- [monomial-hit-production-validation.tar.gz](raw/monomial-hit-production-validation.tar.gz): `c86db676a8e03491dd41f421d53fb9af232d5fbbbb04e4e46e55b45fb65cb55b`
- [monomial-owned-production-bench-fda88fabd49f.tar.gz](raw/monomial-owned-production-bench-fda88fabd49f.tar.gz): `3189a02dc845b3d2a52c4b8bfff1364ebd087c8e017b23cd3a36aa9f36d70b21`
- [monomial-owned-production-records-fda88fabd49f.tar.gz](raw/monomial-owned-production-records-fda88fabd49f.tar.gz): `328d90f00be3b998c92655ae7b090c44e17172f927da7e0c138f0bde02ddd150`
- [monomial-owned-production-validation.tar.gz](raw/monomial-owned-production-validation.tar.gz): `306bef3f42e6897d2fc30e93ca3533e2d6690000d57fa646c39b0a57cc8bb2f2`
- [monomial-append-production-bench-e5a66b00cdff.tar.gz](raw/monomial-append-production-bench-e5a66b00cdff.tar.gz): `9b4b7b304384be1a075fa5f9ca135e6d355044b26120943a432a6ccfe972bd22`
- [monomial-append-production-bench-e5a66b00cdff-repeat.tar.gz](raw/monomial-append-production-bench-e5a66b00cdff-repeat.tar.gz): `0cbc3cf5fbd94985f09a9521c778e0c962c17902628448e2c3a43ef5c100aab6`
- [monomial-append-production-records-e5a66b00cdff.tar.gz](raw/monomial-append-production-records-e5a66b00cdff.tar.gz): `126847956243cde4be4eba89a5526230980fff21245e68dd1a5042b328b96770`
- [monomial-append-production-records-e5a66b00cdff-repeat.tar.gz](raw/monomial-append-production-records-e5a66b00cdff-repeat.tar.gz): `51986cb9a039f7cdb3ef0ab092e4fc1a355c10e9447d191952c496bc4205e7e7`
- [monomial-append-production-validation.tar.gz](raw/monomial-append-production-validation.tar.gz): `c74e9d202cb3d2e18fe17f0cc38969937de9f1a605dc6f5eb642addbca88d3c1`

## Bounded native interning

Fingerprint `3b564edb2ec7`, production commit `b9a0808820`, uses an explicit
accepted/deferred result. A native call returns before the reference fallback
runs. Deferred calls preserve the original table, including every malformed
shape and budget boundary. Each call examines at most 4096 links and 4096
coordinates; insertion uses native code only when exponent width and hash
capacity remain unchanged. Shared inputs remain unchanged. The portable
`attemptPortable_spec` and `combineOwned_spec` prove reference equality for the
Lean model; they do not prove the C provider. The axiom audit reports only
`propext` and `Quot.sound` for these equalities.

The baseline is frozen `c9fcd659ff93`, the earlier multiplied-row snapshot.
This comparison does not include the later owned-set change `70aacca874da`.
Adjacent AB/BA measurements retain all observations and use one unchanged
repeat. Every full basis, fixed output hash and non-resource counter agrees.

| Diagnostic run | CPU | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | --- | ---: |
| Original | 28 | 0.9930 | 0.9891 | 0.9614–1.0621 | 0.9931 |
| Repeat | 38 | 0.9832 | 0.9799 | 0.9605–1.0364 | 0.9900 |

Across 128 processes, candidate geometric mean is 0.9881, median 0.9820,
range 0.9605–1.0621. Process geometric mean is 0.9916, median 0.9905,
range 0.9504–1.0357. Fixed measurements retain 240 points on CPUs84/67.

| Fixed case | Pooled geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 1.0107 | 1.0079 | 0.9905–1.0434 |
| cyclic5 | 0.9799 | 0.9821 | 0.9519–1.0150 |
| cyclic6 | 0.9594 | 0.9590 | 0.9511–0.9701 |
| katsura3 | 1.0025 | 1.0024 | 0.9488–1.0583 |
| reimer5 | 0.9707 | 0.9710 | 0.9641–0.9775 |
| cyclic6Small | 0.9573 | 0.9586 | 0.9406–0.9678 |

These are modest gains on this snapshot, with small regressions retained.
A14213-job full build,2111-job targeted build and175 matrix/567 basis/1288
division oracle cases pass. All567 native/portable/criteria/batch/certificate
comparisons pass. Fixture differences affect only work accounting in525 cases.
Four Clang/GCC sanitizer variants pass, including later malformed-buffer,
huge-Nat and exact machine-scalar-boundary tests at test commit `d2a2558abb`.
The final instrumented F4 window counts14285 searches,6421 successful fused
operations,1095 insertions and5079 exclusive constructor reuses.

Raw archives retain source blobs, frozen binary hashes, all samples and
protocol corrections. The corrections identify stale inherited arm descriptions;
the actual command, binary hash and source manifest were already correct.
SHA-256:

- [monomial-attempt-production-bench-3b564edb2ec7.tar.gz](raw/monomial-attempt-production-bench-3b564edb2ec7.tar.gz): `da091731cf4c28c580bfda28466580372cc6364523ef5a9bd92d4142aefe7487`
- [monomial-attempt-production-bench-3b564edb2ec7-repeat.tar.gz](raw/monomial-attempt-production-bench-3b564edb2ec7-repeat.tar.gz): `c4167a1a3e7707cd2a83955f04484b8075a8e559e29b88c2ce097d0815dbbb48`
- [monomial-attempt-production-records-3b564edb2ec7.tar.gz](raw/monomial-attempt-production-records-3b564edb2ec7.tar.gz): `ea82ab74eb40c62807ee0c56fbba5a889d1d991d8e2d542478d7e748c3422423`
- [monomial-attempt-production-records-3b564edb2ec7-repeat.tar.gz](raw/monomial-attempt-production-records-3b564edb2ec7-repeat.tar.gz): `1a035e2b682321ebdad9ae675c69370b52f7f63b6520c0c0d43b2d2190f5a073`
- [monomial-attempt-production-validation.tar.gz](raw/monomial-attempt-production-validation.tar.gz): `a81b5fecae9cc470395634850a6fbcf6d2190880a8111263d0adb14775bd2f9b`
- [monomial-attempt-malformed-validation.tar.gz](raw/monomial-attempt-malformed-validation.tar.gz): `982bde9327935d2d2f30dd9ca5b194f4b6a51786ee9a0bccf5dd046ef94c9f2d`

## Comparison with the final multiplied-row baseline

`973dc8e4e614` applies the same compact interner to the final multiplied-row
code, based on merged `f8c21c8235`. The measured pre-rebase commit is
`45dc1fc110`; the content-preserving rebase is `125c621531`. The frozen
baseline is `70aacca874da`. Full bases and non-resource counters agree across
all128 processes. All240 fixed output hashes agree. Exactly one unchanged
repeat is retained, including every outlier.

| Diagnostic run | CPU | Candidate geometric mean B/A | Median | Range | Process geometric mean |
| --- | ---: | ---: | ---: | --- | ---: |
| Original | 58 | 1.5613 | 1.2488 | 0.5326–12.9568 | 0.8635 |
| Repeat | 62 | 1.7746 | 1.1151 | 0.7488–19.6089 | 0.9608 |

Pooled candidate geometric mean is1.6645, median1.1550, range0.5326–19.6089.
Process geometric mean is0.9109, median0.8559, range0.1832–4.2777.
Fixed pooled geometric means are0.9929 cyclic4,1.8775 cyclic5,1.5163 cyclic6,
1.0083 katsura3,1.0198 reimer5 and1.4438 cyclic6Small. CPUs57/0, including
ratios through16.5548. These results do not support production adoption of the
combined snapshot. The earlier small gain against the older baseline does not
establish a gain here. No further unchanged repeat is used.

The2121-job library/theory/emitter build and all175/567/1288 external oracle
cases pass. Four Clang and four GCC sanitizer variants preserve complete results,
aliases, malformed prefixes and budgets; final counters equal the earlier bounded
snapshot. Global conformance completion is recorded separately. Two exploratory
Eco10 profile blocks retain all eight complete outputs per arm, exact input and
executable hashes, raw perf data and reports. They include process startup and
are not additional matched timing observations. They do not identify a proven
compiler/runtime limitation.

SHA-256:

- [intern-final-eco-profile.tar.gz](raw/intern-final-eco-profile.tar.gz): `d974bf958da18c7812d07b8ca8f0186912e2820d158996a59bf2cb35352a6a52`
- [intern-final-production-bench-973dc8e4e614-repeat.tar.gz](raw/intern-final-production-bench-973dc8e4e614-repeat.tar.gz): `09d8a7573c4f567ec51df68bac19e16a0edf6627c2a4fc9cdd8cb547d5c43a28`
- [intern-final-production-bench-973dc8e4e614.tar.gz](raw/intern-final-production-bench-973dc8e4e614.tar.gz): `c3271c11361d880542c6772e48dd4dd3140dae533d1e5ca75a9ba39dc3376ae1`
- [intern-final-production-records-973dc8e4e614-repeat.tar.gz](raw/intern-final-production-records-973dc8e4e614-repeat.tar.gz): `b953a9555bedd4e85949e7e99226b7a1f89e762cf22b00c42a191550f9bd57d8`
- [intern-final-production-records-973dc8e4e614.tar.gz](raw/intern-final-production-records-973dc8e4e614.tar.gz): `2367f6b9931638fec2a8fc65a5d21fead25bb01bb75fcaa2376dd0ab4af25867`
