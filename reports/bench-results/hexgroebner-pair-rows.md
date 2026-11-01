# F4 matrices from multiplied critical-pair rows

Grouping multiplied basis faces by their actual LCM avoids constructing explicit
S-polynomial differences before symbolic preprocessing. The final owned-set
snapshot has diagnostic candidate B/A geometric mean **0.8953**, median
**0.9267**, against the arena-validated cache engine. Both original and one
unchanged repeat remain, including large outliers. All complete bases agree.
The recorded fixed-case ratios below are observations on a shared host, not
performance leadership. Fresh msolve comparisons leave a substantial gap.

## Algorithm and correctness boundary

Each selected LCM has one known reducer, chosen from the sparsest participating
basis polynomial, with stable index tie breaking. Every other participating
basis face appears once as a target. One owned set keyed by the complete
(LCM identifier, basis index) pair deduplicates faces, without retaining an
alias to a growing per-group set or truncating either identifier. Subtracting its known reducer gives the
selected S-polynomial span. A disconnected same-LCM graph may add valid rows,
but no selected identity is lost. Every row is an actual multiplied basis
polynomial; the certificate producer creates its derivation from the current
basis root and multiplier. Sugar uses the maximum of its group, which is exact for the single-sugar batches
selected by the pair queue. Field/order
metadata, critical-pair selection and its completed/deferred obligations retain
their existing contracts.

Symbolic preprocessing starts with the known leading pivots closed, adds their
supports and all target supports, and computes the remaining closure as before.
It cannot install a duplicate seeded leading pivot. The default empty-seed
route used by division/final interreduction retains its existing behavior.
Full final basis certification still proves both ideal containments, all final
S-pair reduction obligations and reducedness. Arbitrary ideal-membership
identities alone are never treated as the Gröbner property.

Input, unit/zero ideals, candidate versus checked results, invalid input,
representation limits, parent budgets and resumable checkpoint distinctions
retain their contracts. Failed stages commit no partial basis or pair queue.
Monomial interning and charged work can survive a failed attempt as before.
Work and matrix counters can change because the algorithm constructs different
rows and sometimes selects a different intermediate basis.

## Validation

Library/theory/driver/conformance builds pass, including all 567 native/portable,
batch-size, pair-criteria and complete-certificate comparisons. The independent
175 matrix, 567 SymPy/Singular basis and 1288 division/normal-form/membership
oracles pass. All 30 benchmark verifications pass. Four Clang ASan/UBSan native
variants exercise real F4 plus long cache comparisons (116270 scans, 198270
gathers and 4051 byte comparisons each). Existing native C is unchanged.
DAG, phase, release-manifest, source/header and admission audits pass.

Dedicated tests compare each selected S-polynomial with its multiplied faces,
including a triangle and disconnected same-LCM components. The downstream
literal certificate is regenerated to the new six-node derivation and kernel
replay passes without native_decide or new axioms. Regenerated F4 fixtures keep
every input and final basis unchanged; matrix and work statistics change as
recorded. This does not complete the deterministic F4/termination theory.

## Timing contract

B is fingerprint `064a09798b72`, the multiplied-row engine built on the final
context-bound cache/access engine A (`57149c9cc2f7`). Exact staged source blobs,
driver inputs and frozen executable hashes identify each arm independently of
rebases. Host chungus2, AMD EPYC 9455, Lean4.35.0-rc3, generated C Clang23.1.0,
FFI Clang23.1.3. One thread pins to an automatically leased CPU. Every experiment
runs adjacent AB then BA, with every completed sample retained and no quiet-host
condition. Candidate time includes canonicalization, F4 and final interreduction;
process time additionally includes startup, parse and complete output.
Certificate generation, independent certification and kernel checking are excluded.

The diagnostic suite has 16 grevlex systems over 32003/2147483647 (cyclic5/6,
Katsura6, Eco10, Noon4, Reimer5, MinRank and fixed quadratics), SHA-256
`59cec100d5b9dc6977e61f7b7f747ca26e987584811ab41a445dbd020e567e0b`.
It is neither balanced nor held out. Each process has ten seconds and 16-GiB
address space. All 128 processes complete with equal full bases; algorithmic
counters may differ and are retained in raw outputs and analyses.

| Diagnostic experiment | CPU | Candidate geometric mean | Median | Range | Process geometric mean | Median | Range |
| --- | ---: | ---: | ---: | --- | ---: | ---: | --- |
| Original | 18 | 0.9150 | 0.9018 | 0.4468–2.3306 | 0.9537 | 0.9851 | 0.3388–2.2660 |
| Rerun | 57 | 0.9604 | 0.9385 | 0.4815–2.1338 | 1.1880 | 1.2325 | 0.5208–3.0389 |

Pooled process geometric mean is 1.0644, median 1.0452, range 0.3388–3.0389.
The rerun process regression despite its candidate gain is unexplained.
Thus the candidate improvement does not imply a process-time gain. Only one
unchanged diagnostic rerun follows the mixed original observations. Work and
allocation decrease for all diagnostic inputs; matrix entries increase for
MinRank and Reimer, and Reimer has two additional rounds. These are operational
counters, not timing claims.

The fixed registered cases use five declared repetitions and complete structural
basis hashes. Ratios normalize total time by actual inner repeats. All 240
points complete with equal hashes, including the one unchanged rerun after
mixed adjacent-arm observations. CPUs are 44 and 66.

| Fixed case | Original geometric mean | Rerun geometric mean | Pooled geometric mean | Median | Range |
| --- | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 1.0000 | 1.1003 | 1.0489 | 1.0362 | 0.8361–1.3777 |
| cyclic5 | 1.0313 | 0.8465 | 0.9343 | 0.8952 | 0.7537–1.4940 |
| cyclic6 | 0.8892 | 0.8708 | 0.8800 | 0.8700 | 0.4238–1.9174 |
| katsura3 | 0.8244 | 1.0909 | 0.9484 | 0.9804 | 0.1483–1.7161 |
| reimer5 | 0.7251 | 0.7857 | 0.7548 | 0.7629 | 0.4498–0.9897 |
| cyclic6Small | 1.0676 | 0.7731 | 0.9085 | 0.9129 | 0.2347–2.8660 |

Every regression and outlier remains. No additional unchanged rerun is used.
These finite fixed inputs do not establish a general complexity law.

## Arena-validated cache baseline

The final computational snapshot `68086d6576` is content-identical over the benchmark
family to rebased PR commit `d227bebc90`, fingerprint `c9fcd659ff93`.
A is the frozen arena-validated cache/access engine `65d5517c4d57` (computational
commit `a74d092a08`); B adds multiplied pair rows. Both source manifests and
frozen executable hashes are archived. The same host, toolchain, diagnostic
inputs, output contract, limits and adjacent AB/BA schedule above apply.
This is a separate comparison from the earlier context-bound cache experiment;
its ratios are not pooled with that experiment.

All 64 diagnostic processes complete on CPU89 with equal full bases. Candidate
geometric mean is **0.8955**, median **0.8788**, range **0.8343–1.0979**.
Process geometric mean is **0.9549**, median **0.9666**, range **0.8839–1.0465**.
Counters retain the changes caused by the different matrices and intermediate
bases. The registered sweep completes all 120 points on CPU71 with matching
full structural basis hashes and five declared repetitions per arm and order.

| Fixed case | Geometric mean B/A | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 1.0301 | 1.0347 | 0.9809–1.0475 |
| cyclic5 | 0.8711 | 0.8721 | 0.8644–0.8814 |
| cyclic6 | 0.8531 | 0.8531 | 0.8456–0.8610 |
| katsura3 | 0.9684 | 0.9676 | 0.9121–1.0337 |
| reimer5 | 0.9007 | 0.9099 | 0.8423–0.9129 |
| cyclic6Small | 0.8588 | 0.8586 | 0.8547–0.8631 |

Every completed sample, including regressions, remains. No unchanged rerun was
used for this snapshot. `ldd` confirms these frozen binaries contain the Hex and
Lean code statically; subsequent worktree edits cannot change either arm.

## Owned target deduplication

The final computational snapshot is `6841f20b1f`, fingerprint `70aacca874da`.
It uses one owned set keyed by (LCM, source), validates pair indices/nonzero
sources, classifies duplicate/empty seeds as internal matrix errors, and removes
the unused traced S-polynomial constructor. Reducer selection and complete
outputs are unchanged. Tests now include several LCMs sharing sources with
different multipliers, a later sparse reducer, duplicate/reversed pairs, a
seeded lead in another target tail, duplicate/empty seeds and invalid indices.

The old rebased head `d227bebc90` was independently fingerprinted as
`c9fcd659ff93`; every one of its 42 linked archives passed SHA-256 verification.
The provenance archive records that check. Measurements above retain that
snapshot; they are not silently relabeled as final-head measurements.

The same frozen baseline `65d5517c4d57`, host, toolchain, input/output limits and
adjacent AB/BA protocol apply. The original has large timing variability, so
exactly one unchanged repeat follows; all completed samples and regressions
remain. No cross-snapshot pooling is performed.

| Diagnostic experiment | CPU | Processes | Candidate geometric mean | Median | Range | Process geometric mean | Median | Range |
| --- | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- |
| Original | 70 | 64 | 0.9356 | 0.9142 | 0.7081–1.4212 | 0.9876 | 1.0030 | 0.3403–1.7672 |
| Repeat | 78 | 64 | 0.8566 | 0.9374 | 0.5181–1.4843 | 0.9792 | 0.9220 | 0.3604–3.2657 |

All 128 processes complete with equal full bases. Pooled candidate geometric
mean is 0.8953, median 0.9267, range
0.5181–1.4843; process geometric mean is 0.9834,
median 0.9660, range 0.3403–3.2657.
The two fixed sweeps retain 240 points with matching full structural hashes,
five declared repetitions and actual inner-repeat normalization, CPUs43/8.

| Fixed case | Original geometric mean | Repeat geometric mean | Pooled geometric mean | Median | Range |
| --- | ---: | ---: | ---: | ---: | --- |
| cyclic4 | 0.9583 | 1.0380 | 0.9973 | 1.0216 | 0.2700–1.9466 |
| cyclic5 | 0.8424 | 0.7784 | 0.8098 | 0.8350 | 0.5651–0.9982 |
| cyclic6 | 0.6134 | 0.7391 | 0.6733 | 0.7838 | 0.2210–1.2836 |
| katsura3 | 0.8313 | 0.9050 | 0.8674 | 0.9566 | 0.2032–1.8513 |
| reimer5 | 0.8706 | 0.9023 | 0.8863 | 0.8190 | 0.6626–1.3053 |
| cyclic6Small | 0.8925 | 0.8424 | 0.8671 | 0.8823 | 0.3553–1.8959 |

Large gains and regressions coexist, including unaffected tiny cases; the raw
samples do not isolate the source of shared-host variability. The observations
support retaining the matrix construction but do not quantify a general gain.
No further unchanged repeat is used. Independent external oracles and all four
Clang ASan/UBSan variants pass for this snapshot, with 116270 scans, 198270
gathers, 4092 byte comparisons and 216 product validations per variant.

## Fresh current-msolve comparisons

Upstream msolve remains at `3672113ee2c696a2ac9c637636e0f7214f500ba1`
after a fresh fetch. Its GCC16.2/OpenMP build uses `-O3 -march=native`,
GMP/MPFR/FLINT3.6 and passes all 71 upstream tests. Both arms use one thread,
full reduced grevlex output, adjacent AB/BA, the same diagnostic inputs and
limits, and the frozen Hex multiplied-row engine. msolve mode2 is exact default
elimination; mode42 uses probabilistic elimination. Every complete output is
parsed and compared; neither certificate generation nor kernel checking is timed.

| msolve mode | CPU | Processes | Equal full-basis pairs | Hex/msolve process geometric mean | Median | Range |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 2 | 48 | 64 | 32/32 | 6.2498 | 6.6670 | 1.5846–11.2599 |
| 42 | 28 | 64 | 32/32 | 6.3449 | 6.1141 | 4.0365–14.3326 |

These whole-process ratios include different parsing/conversion boundaries and
startup costs. Internal msolve timers are coarse for tiny systems; no candidate
ratio is inferred from them here. The experiments do not replace the SPEC's
balanced, held-out, wider-field and parallel comparator acceptance campaign.
Earlier matched sweeps belong to their recorded snapshots and host observations;
ratios across campaigns are not used to infer an algorithm regression or gain.
No evidence establishes that language changes are necessary.

## Retained evidence

Archives retain source manifests and blobs, frozen binary hashes, exact commands,
inputs, raw samples, output comparisons, all failures, memory and variability.
Overlay `root-sources` on the declared baseline, point the archived driver at
that checkout, and build `production_compare`; fixed cases use
`hexgroebner_bench`. SHA-256:

- [msolve-l2-records-064a09798b72.tar.gz](raw/msolve-l2-records-064a09798b72.tar.gz): `32ef848829db51908a3ec297f34d87c49865e6443a9892e7d74b3335b13e9e2a`
- [msolve-l42-records-064a09798b72.tar.gz](raw/msolve-l42-records-064a09798b72.tar.gz): `0a6f0a03a419fde4bc154e6bf907c48def70513c46f84b3efae5698ade65e23c`
- [pair-rows-production-bench-064a09798b72.tar.gz](raw/pair-rows-production-bench-064a09798b72.tar.gz): `9dd3291d1444ef87bb1e930166c7ce8258738c1befae5d08495964b5c3591b2b`
- [pair-rows-production-bench-064a09798b72-repeat.tar.gz](raw/pair-rows-production-bench-064a09798b72-repeat.tar.gz): `23b61c612581a731063a1fad5c149092b6addbf8918bdeb080bb6cb9ce8ee80a`
- [pair-rows-production-records-064a09798b72.tar.gz](raw/pair-rows-production-records-064a09798b72.tar.gz): `6bd76d6c22f2efe6ce795ec289c15f7c978d0f72324b275286da7bc5b2dd4986`
- [pair-rows-production-records-064a09798b72-repeat.tar.gz](raw/pair-rows-production-records-064a09798b72-repeat.tar.gz): `95dead937e2dc2263b9fec4c45ef8047ed99529fe7b836d93b7ea5f39c1d9897`
- [pair-rows-validation.tar.gz](raw/pair-rows-validation.tar.gz): `2d62bf540b1096936a56914f543c933322426967a76ce8a33aa3b8d206474eb0`

- [pair-rows-verified-production-bench-c9fcd659ff93.tar.gz](raw/pair-rows-verified-production-bench-c9fcd659ff93.tar.gz): `32f9c3ca2da871270b1e4b5ce62d5f24faa916fa14910ae5fa9044a70482431a`
- [pair-rows-verified-production-records-c9fcd659ff93.tar.gz](raw/pair-rows-verified-production-records-c9fcd659ff93.tar.gz): `81b0ee3677df574983a0d6d698aba63a241a1a028c3b3652aeaef9d76ec5aa8a`

- [pair-rows-owned-production-bench-70aacca874da-repeat.tar.gz](raw/pair-rows-owned-production-bench-70aacca874da-repeat.tar.gz): `181a1948b799a15fba47ca2ef4d5c50c1fa3454b3ce5f2408b924b50dafc452c`

- [pair-rows-owned-production-bench-70aacca874da.tar.gz](raw/pair-rows-owned-production-bench-70aacca874da.tar.gz): `b741e3f589090e041a5ef192c396ed877be97cd89ea6a095870561feb7d0b02a`

- [pair-rows-owned-production-records-70aacca874da-repeat.tar.gz](raw/pair-rows-owned-production-records-70aacca874da-repeat.tar.gz): `cb94bb2e7d9102f96328705405b5adea479f17df6a3b50812a9c0978e282e7e8`

- [pair-rows-owned-production-records-70aacca874da.tar.gz](raw/pair-rows-owned-production-records-70aacca874da.tar.gz): `3f9707f0a9e243698495876cf1840f61e97a57f1a4a74cbc3e4ac4873a85b455`

- [pair-rows-provenance.tar.gz](raw/pair-rows-provenance.tar.gz): `6a6977a539b48db9c87a7ab12f52e525f2d1b2a401fc6616b9bec738071da3a9`
