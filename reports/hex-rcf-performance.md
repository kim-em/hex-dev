# HexRCF Performance Report

## Bench Targets

The Mathlib-free compiled track is the `hexrcf_bench` LeanBench executable.
CI builds representative tactic, supplied-literal and registered-constant
proofs through `HexRCFProofProbe`; these correctness examples have no timing
contract.

The compiled registrations are stable parametric families. Fixture generation
is outside each timed region; LeanBench's required structural result hash is
inside it. The final column copies the complexity derivation adjacent to each
`setup_benchmark` registration rather than substituting a report-level
paraphrase.

| registration | controlled schedule | registered formula | copied registration derivation |
|---|---|---|---|
| `runDecisionCarrierDegree` | `n = 16, 20, 24, 28, 32` | `n ^ 4` | The carrier has `n` active intervals over `n` Descartes levels, each dominated by a quadratic Möbius transform. The other fixed-shape decision phases are no worse on this family, giving `O(n^4)` exact-integer operations. |
| `runDedupRepeated` | `u = 256, 512, 1024, 2048, 4096` | `u` | After the first occurrence the seen prefix has size one, so each of the `u` coefficient-equality probes has bounded cost and total work is `O(u)`. The one-polynomial result has constant structural-hash cost. |
| `runDedupDistinct` | `u = 64, 128, 256, 512, 1024` | `u * u` | Every distinct fixed-degree polynomial scans a seen prefix of lengths `0, ..., u-1`; coefficient widths are bounded by the committed schedule, so the exact list/coefficient-comparison count is `O(u^2)`. LeanBench's required structural result hash is `O(u)` and therefore lower-order. |
| `runCommonCoprime` | `m = 8, 16, 32, 64, 128` | `m` | The coprime case performs one bounded-degree gcd, identity package, replay choice, and checker call for each of `m` independently prepared atoms. The required hash walks `m` bounded-size certificates, preserving `O(m)`. |
| `runCommonShared` | `m = 8, 16, 32, 64, 128` | `m` | The shared-root case likewise performs one fixed-degree public `buildCommonRoot?` call per atom; the nonconstant gcd replay remains bounded because both carrier and atom degrees are fixed. The required structural hash also walks `m` bounded-size certificates, giving `O(m)` total work. |
| `runCommonRepeated` | `m = 8, 16, 32, 64, 128` | `m` | The repeated case intentionally does not deduplicate: it invokes the public builder exactly `m` times on the same fixed-degree pair. Hashing the `m` bounded-size results is also linear, hence `O(m)` total work. |
| `runSeparationDepth` | `b = 36, 40, 44, 48, 52, 56` | `b * b * ceilLog2 (b + 1)` | The two roots `+-2^-b` keep the count-one intervals touching for `Theta(b)` bisections. Each step performs bounded fixed-degree arithmetic on `Theta(b)`-bit operands, so the wall contract `O(b M(b))` is represented by the quasi-linear multiplication proxy `b^2 ceilLog2(b+1)`. The schedule stays in one multiprecision regime and avoids the immediate-`Int`/GMP seam. |
| `runReplayCells` | `k = 18, 20, 22, 24, 26, 28` | `k ^ 5 * (ceilLog2 (k + 1)) ^ 2` | Isolation validation and the `k` root-cell common-root queries take `O(k^3)` exact operations. The primitive PRS for `prod_(j<=k)(x-j)` has operand height `B(k) = O(k^2 log k)`; with quasi-linear multiplication, the wall-cost proxy for `O(k^3 M(B(k)))` is `k^5 ceilLog2(k+1)^2`. Construction stays in `prep`. |
| `runReplaySigns` | `u = 64, 96, 128, 160, 192, 256` | `u * u` | With three carrier cells fixed, product construction, deduplication, aligned common-root lookup, sign-row construction, and formula lookup scan prefixes of the `u` distinct scalar-multiple entries, for `O(u^2)` total work. |
| `runReplayFormula` | `s = 64, 128, 256, 512, 1024, 2048` | `s` | The arithmetic payload and atom multiset stay fixed. Polynomial discovery and the strict option-valued formula fold visit each appended literal/connective node a bounded number of times, giving `O(s)` structural work. |

The informational python-flint surface consists of
`runFlintDecisionOverhead` and the paired fixed registrations
`runLeanDecision{16,20,24,28,32}` / `runFlintDecision{16,20,24,28,32}`.
The manifest records this surface as the
`python-flint univariate RCF verdict oracle` comparator.
Each substantive pair consumes the same precomputed `Sentence`, returns the
same `Bool`, and checks the same expected hash. This comparison covers carrier
degree/root count only; python-flint is not proof-producing and supplies no
comparable tactic/elaboration surface.

## Verdicts

The compiled and comparator executable was built from clean commit
`f04cd955d149e4a102cd46c708ece26fc0776545` with
`leanprover/lean4:4.32.0-rc1` on `chungus2` (AMD EPYC 9455 48-Core Processor,
96 logical CPUs, `x86_64-unknown-linux-gnu`). LeanBench reports version
`0.1.0`; its package checkout was clean commit
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`. The commands were pinned to
preregistered logical CPU 22.

The compiled source-closure claims below refer to their producing snapshot.

Exact compiled command:

```sh
taskset -c 22 .lake/build/bin/hexrcf_bench run \
  Hex.RCFBench.runDecisionCarrierDegree \
  Hex.RCFBench.runDedupRepeated \
  Hex.RCFBench.runDedupDistinct \
  Hex.RCFBench.runCommonCoprime \
  Hex.RCFBench.runCommonShared \
  Hex.RCFBench.runCommonRepeated \
  Hex.RCFBench.runSeparationDepth \
  Hex.RCFBench.runReplayCells \
  Hex.RCFBench.runReplaySigns \
  Hex.RCFBench.runReplayFormula \
  --export-file /tmp/hex-rcf-compiled-f04cd955d149-chungus2.json
```

The committed artifact is the byte-for-byte copy at
`reports/bench-results/hex-rcf-compiled-f04cd955d149-chungus2.json`, anchored
by SHA-256
`5273c4ff256581c8414130109323f88d6e564ab0553f26f3682e6260b8ace6ae`.
The embedded environment says `git_dirty=false`, commit
`f04cd955d149e4a102cd46c708ece26fc0776545`, and hostname `chungus2`.

| registration | median per-call nanoseconds in schedule order | verdict | spawn floor |
|---|---|---|---:|
| `runDecisionCarrierDegree` | `31,776,736.500000; 84,606,031; 184,256,755; 332,972,975; 541,090,562` | `consistent_with_declared_complexity` | 21,505,810 ns |
| `runDedupRepeated` | `4,334.864807; 8,692.292358; 17,490.520508; 33,875.075684; 67,772.292969` | `consistent_with_declared_complexity` | 21,087,220 ns |
| `runDedupDistinct` | `41,552.154297; 165,245.880859; 672,412.343750; 2,712,172.156250; 10,456,821.375000` | `consistent_with_declared_complexity` | 20,690,942 ns |
| `runCommonCoprime` | `46,126; 90,202.965820; 181,565.992188; 363,011.414062; 738,712.421875` | `consistent_with_declared_complexity` | 20,733,146 ns |
| `runCommonShared` | `36,302.501953; 72,581.620117; 145,149.449219; 289,423.734375; 592,625` | `consistent_with_declared_complexity` | 21,350,560 ns |
| `runCommonRepeated` | `35,174.702148; 70,431.723633; 141,532.445312; 283,192.582031; 562,754.867188` | `consistent_with_declared_complexity` | 20,781,437 ns |
| `runSeparationDepth` | `1,422,779.625000; 1,786,385.343750; 2,208,272.343750; 2,659,586.968750; 3,226,831.343750; 4,178,944.312500` | `consistent_with_declared_complexity` | 20,714,407 ns |
| `runReplayCells` | `6,609,920.562500; 11,697,033.625000; 19,231,351.250000; 26,666,543.500000; 37,682,226; 49,465,013` | `consistent_with_declared_complexity` | 20,647,979 ns |
| `runReplaySigns` | `483,483.125000; 1,105,897.671875; 1,811,406.500000; 3,055,112.687500; 3,907,871.812500; 6,932,867.375000` | `consistent_with_declared_complexity` | 21,114,050 ns |
| `runReplayFormula` | `7,735.412354; 13,491.146973; 24,456.550293; 48,304.772461; 95,916.387695; 187,613.238281` | `consistent_with_declared_complexity` | 20,606,938 ns |

All ten results are parametric, every point has status `ok`, and no result was
budget-truncated. These verdicts apply only to the committed schedules and the
declared proxy formulas in the SPEC.

All ten registrations set `signalFloorMultiplier := 1.0`. Their warm
child-side inner repeats measure the registered timed work inside the child,
not parent-side process startup, and this keeps the SPEC-fixed ladders usable
on a host whose executable startup floor was
20.606938–21.505810 ms; the exported spawn-floor values remain visible in the
table.
The harness drops the leading scheduled rung before forming each verdict band.
The effective verdict spans are therefore 20–32, 512–4096, 128–1024, 16–128
for each common-root family, 40–56, 20–28, 96–256, and 128–2048 in table order.

The proof surface is covered by CI-built quadratic, existential and registered
real-constant examples through `HexRCFProofProbe`, with ordinary kernel axiom
audits. The compiled verdicts above remain the computational performance record.

## Comparator Ratios

Exact comparator command, using python-flint 0.9.0 from the explicit virtual
environment and the same CPU 22 affinity:

```sh
env PATH="/tmp/hexrcf-flint-venv/bin:$PATH" taskset -c 22 \
  .lake/build/bin/hexrcf_bench run \
  Hex.RCFBench.runFlintDecisionOverhead \
  Hex.RCFBench.runLeanDecision16 Hex.RCFBench.runFlintDecision16 \
  Hex.RCFBench.runLeanDecision20 Hex.RCFBench.runFlintDecision20 \
  Hex.RCFBench.runLeanDecision24 Hex.RCFBench.runFlintDecision24 \
  Hex.RCFBench.runLeanDecision28 Hex.RCFBench.runFlintDecision28 \
  Hex.RCFBench.runLeanDecision32 Hex.RCFBench.runFlintDecision32 \
  --export-file /tmp/hex-rcf-comparator-f04cd955d149-chungus2.json
```

The committed byte-for-byte artifact is
`reports/bench-results/hex-rcf-comparator-f04cd955d149-chungus2.json`, SHA-256
`b4fb98cbe6989d2f3115de5da7736f1a1e4ace8847a5aadf1eab43999070d915`.
It embeds the same clean commit and host as the compiled artifact. All eleven
registrations completed without budget truncation; all repeat hashes agree and
all expected-hash checks report `match` for observed hash `0xb`.

The comparator source is the `rcf/decide` dispatch in
`scripts/oracle/flint_bench_driver.py`, backed by
`scripts/oracle/rcf_flint.py`, and driven persistently by
`Hex/BenchOracle/Flint.lean`; all three are pinned by the artifact's clean
commit. The recorded environment observation was python-flint 0.9.0. It can be
made from a clean environment using CPython 3.11.15 and bundled FLINT 3.6.0:
`/home/kim/.local/share/uv/python/cpython-3.11.15-linux-x86_64-gnu/bin/python3.11 -m venv --clear /tmp/hexrcf-flint-venv`, then
`/tmp/hexrcf-flint-venv/bin/python -m pip install python-flint==0.9.0`.
Before a rerun, the exact interpreter and both library versions are checked
with `/tmp/hexrcf-flint-venv/bin/python --version` and
`/tmp/hexrcf-flint-venv/bin/python -c 'import flint; print(flint.__version__, flint.__FLINT_VERSION__)'`.

The conservative steady-state FLINT request/reply floor median is 8,528 ns
(minimum 8,479 ns, maximum 8,663 ns over eleven repeats). The raw ratio is
`Lean median / FLINT median`. The floor is subtracted only if it is at most 50%
of the FLINT median; if it exceeds 5%, both raw and adjusted ratios are
mandatory. Here every rung is eligible and every floor fraction is below 5%,
so the raw ratio is the required headline and no adjusted ratio is reported.

| degree | Lean median | FLINT median | Lean / FLINT raw | floor / FLINT | policy |
|---:|---:|---:|---:|---:|---|
| 16 | 31,704,385 ns | 546,053 ns | 58.061003x | 1.561753% | eligible; raw ratio sufficient |
| 20 | 84,922,278 ns | 843,273 ns | 100.705558x | 1.011298% | eligible; raw ratio sufficient |
| 24 | 184,451,979 ns | 1,233,340 ns | 149.554850x | 0.691456% | eligible; raw ratio sufficient |
| 28 | 333,347,220 ns | 1,635,429 ns | 203.828610x | 0.521453% | eligible; raw ratio sufficient |
| 32 | 543,627,663 ns | 2,114,888 ns | 257.047968x | 0.403236% | eligible; raw ratio sufficient |

The Lean/FLINT ratio climbs monotonically across every eligible rung, from
58.061x at degree 16 through 100.706x, 149.555x, and 203.829x to 257.048x at
degree 32: the Lean implementation is steadily losing relative ground over
this fixed family. Across the doubled degree range, Lean grows 17.147x
(approximately `n^4.100`) while FLINT grows 3.873x (approximately `n^1.953`);
their observed exponent gap predicts 4.427x ratio growth, exactly the measured
257.048 / 58.061 = 4.427x. The divergence is therefore structural on this
schedule and is recorded as an informational finding, not a Concern. The
manifest and library SPEC assign python-flint no gating goal; it supplies an
independent non-proof-producing orientation curve for the compiled decision
track.

The comparator includes persistent-driver pipe transport and Python JSON
decoding in the timed FLINT side. It excludes process startup through the
discarded warmup call. The floor's shorter request understates parsing cost at
the degree rungs. The ratios are informational and do not compare proof
production, atom multiplicity, common-root preparation, separation, replay,
reification, literal elaboration, or the end-to-end tactic.

## Profile

Five timed-region profiles were collected against the clean
`f04cd955d149e4a102cd46c708ece26fc0776545` executable on `chungus2`: Linux
6.12.95 on NixOS 26.11 (Zokor), `x86_64`, AMD EPYC 9455 48-Core Processor.
Every case used the deterministic registered fixture (no random seed), a
999 Hz sampling rate, `samply 0.13.1`, LeanBench 0.1.0 from clean package
commit `fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, and lean-bench-samply clean
commit `a69ffaf99da33c1424ef80246d923c676159501b`. The sampling helper and
profiler threads were deliberately not constrained by `taskset`; these traces
make attribution claims only, not timing claims. Timing verdicts come from the
compiled artifacts above.

The exact commands were instances of:

```sh
python3 /tmp/lean-bench-samply/scripts/profile_bench.py \
  --bench-exe .lake/build/bin/hexrcf_bench \
  --bench-name NAME --param PARAM --target-nanos 1000000000 \
  --out OUT \
  --samply-args '--rate 999 --unstable-presymbolicate'
```

with these substitutions:

| manifest input family | `NAME` | `PARAM` | developer-local `OUT` |
|---|---|---:|---|
| `carrier-degree-roots` | `Hex.RCFBench.runDecisionCarrierDegree` | `n = 32` | `/tmp/hex-rcf-profile-f04cd955d149-carrier-32.json.gz` |
| `atom-multiplicity` | `Hex.RCFBench.runDedupDistinct` | `u = 1024` | `/tmp/hex-rcf-profile-f04cd955d149-atom-1024.json.gz` |
| `common-root-work` | `Hex.RCFBench.runCommonShared` | `m = 128` | `/tmp/hex-rcf-profile-f04cd955d149-common-128.json.gz` |
| `separation-refinement` | `Hex.RCFBench.runSeparationDepth` | `b = 56` | `/tmp/hex-rcf-profile-f04cd955d149-separation-56.json.gz` |
| `certificate-replay-size` | `Hex.RCFBench.runReplayCells` | `k = 28` | `/tmp/hex-rcf-profile-f04cd955d149-replay-28.json.gz` |

The committed analytical summary is
`reports/bench-results/profiles/hex-rcf-profiles-f04cd955d149-analysis.json`,
SHA-256
`f1d00985f8204e0d0b2012638d16712def221b742f483107c4bed07b8bfaefc9`.
It records each developer-local profile/symbol/diagnostics triple by SHA-256.
For each profile it retains the bench-thread and off-thread sample
counts, symbol-resolution counts, calibration residual and 5 ms ceiling,
confidence and sensitivity verdicts, leaf categories, and inclusive rankings.
In accordance with `SPEC/profiling.md`, the raw `*.json.gz` captures and their
sidecars are not committed. Their hashes remain in the analytical summary and
below so the local evidence used for this
report is exactly identifiable.

| case | filtered profile SHA-256 | symbols SHA-256 | diagnostics SHA-256 |
|---|---|---|---|
| carrier | `caf159df6cdd9d894c1f0aee3d26b5d2651f0aa2036c53284049b765d4ae0ad0` | `babd360286a816ce8f823bec3cf171bb1b3a5b313e949fd1ca3180200dafca04` | `ba6cdca94421b87ddf488a148b37cecc5c63fe637f199223bbc0faaf426b44b7` |
| distinct atoms | `7d1d62c15fee9b011ebc1f0eb2009b1d082275a0a70e51846c8b5cbd088c69a3` | `fe376db9e2d48a8ed94a9866328a18713d4bc897c3ae77bac9ef30274b720fcb` | `066e43460f3ad0756c90d356b4c7fee6d334f3162907e7ad45892551bd50c5b0` |
| common root | `3d9ceb2950e367a3304cc198ea6c678677da41e9c296dde89f9ecb3ae0452e85` | `081f8a9d0a279960fce8c22be06c8f68ce726624a9e0628fd954673a36dbad6d` | `4aae0b6c4c1f0ee5c5751664f55207813d77c732c39457ed1b2c4838631ba4a6` |
| separation | `05f79727e4834ebd7b4957e578ff36bddd1f3e32a5eb5817b3a14a12d8a29627` | `1a9b28f0c912a240b26bce3f7c0d2ad532bd1927f1abab28fa0f790e4d2242db` | `675f52955f1e69a992110ddd713673d53904191af23ffe77e3d432bd774c5ba7` |
| replay cells | `fbc9333644c091aadfdd3283a644e5480eacdeec6fdc1af761c13cca79c72ad2` | `9a433bcc609d015eea06df78a006b7969caf08b6973ac57f0b096a0f1a424cb8` | `e57030a17800006ccb7238e526b0614cbd963ae322c33d7977b1821573bfea31` |

All five diagnostics report `confidence=passed`, sensitivity `passed`, and
zero off-bench-thread samples inside timed windows.

| case | timed ms | retained samples | calibration residual ms | classified | own code | GMP | allocation | Lean runtime | unclassified |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| carrier | 565.982459 | 550 | 0.811102 | 99.636% | 4 (0.727%) | 174 (31.636%) | 316 (57.455%) | 54 (9.818%) | 2 (0.364%) |
| distinct atoms | 666.108650 | 655 | 1.811836 | 100.000% | 173 (26.412%) | 0 (0.000%) | 245 (37.405%) | 237 (36.183%) | 0 (0.000%) |
| common root | 601.401303 | 578 | 0.660870 | 99.481% | 71 (12.284%) | 110 (19.031%) | 286 (49.481%) | 108 (18.685%) | 3 (0.519%) |
| separation | 955.658702 | 945 | 1.681723 | 98.942% | 5 (0.529%) | 360 (38.095%) | 464 (49.101%) | 106 (11.217%) | 10 (1.058%) |
| replay cells | 846.933185 | 846 | 0.749371 | 98.936% | 4 (0.473%) | 299 (35.343%) | 431 (50.946%) | 103 (12.175%) | 9 (1.064%) |

Recursive-inclusive percentages count each named function at most once per
sample, collapsing recursive occurrences. The principal registered-path
attributions are:

| case | selected recursive-inclusive functions |
|---|---|
| carrier | `RCF.decide` 92.545%; `RCF.build?` 78.727%; `buildDecomposition?` 64.909%; `buildIsolations?` 64.545%; `SturmReplay.count` 41.091%; `IsolationCert.check` 28.364%; `Separation.separate?` 26.909% |
| distinct atoms | `dedupPolysAux` 99.847%; coefficient-equality scan 16.794% |
| common root | `buildCommonRoot?` 95.675%; polynomial `divMod` 42.734%; `xgcd` 25.260%; `CommonRootCert.check` 7.612% |
| separation | `Separation.separate?` 89.524%; `separateFrom?` 88.360%; `refine1?` / `refinePairWith?` 87.513% |
| replay cells | `SturmReplay.count` 86.879%; strict option/sign path 45.035%; `Sentence.replayCells?` 44.681%; `IsolationCert.checkStrict` 43.972%; `CommonRootCert.hasRoot` 42.908% |

In the carrier case, `RCF.decide` encloses the registered whole decision and
`RCF.build?` performs its certificate construction, so their 92.545% and
78.727% inclusive shares are expected. The nested decomposition and isolation
builders account for about 65% each because the degree-32 fixture must build
and check its real-root cells; Sturm counting and adaptive separation are the
visible arithmetic subphases. The leaf split—57.455% allocation and 31.636%
GMP—matches that exact-polynomial construction workload.

For distinct atoms, `dedupPolysAux` is the operation registered by
`runDedupDistinct`, so its 99.847% inclusive share is direct attribution. The
16.794% coefficient-equality scan is the expected growing-prefix comparison
inside that loop. The fixture has fixed small coefficients, explaining the
absence of GMP leaf cost while allocation and Lean runtime carry the lists and
coefficient arrays.

For common-root work, the registered `runCommonShared` target calls
`buildCommonRoot?` once for each of 128 atoms; its 95.675% share therefore
captures the intended workload. Polynomial division (42.734%) and `xgcd`
(25.260%) construct the nonconstant-gcd identity package, while the smaller
certificate-check share verifies it. The GMP and allocation leaf shares are
the exact-arithmetic and certificate-construction costs of those public
builder calls.

For separation, `Separation.separate?` is itself the registered operation.
`separateFrom?`, `refine1?`, and `refinePairWith?` are its nested adaptive
refinement loop, so their 87–90% inclusive shares show that the close dyadic
pair is exercising the intended depth-dependent path. GMP arithmetic and
allocation together account for 87.196% of leaves, consistent with repeatedly
refining exact dyadic intervals and replaying the fixed-degree chain.

For replay cells, `SturmReplay.count` dominates because the registered replay
must validate the isolation and answer each root-cell query. The strict
option/sign path, `Sentence.replayCells?`, `IsolationCert.checkStrict`, and
`CommonRootCert.hasRoot` at roughly 43–45% are the expected checker layers for
the prebuilt degree-28 certificate. Their GMP and allocation costs arise from
exact sign/count checks and traversal of the 57 cells, not from witness
construction, which remains outside the timed region.

Every dominant inclusive path is thus attributable to its registered target;
no suspicious unregistered dominant cost was observed.

## Concerns

`None.`

## Optional shared-formula adapter

`HexRCF.RealFormula` correspondence is covered by ordinary regression tests in
`conformance/HexRCF/RealFormulaConformance.lean`, including the cubic
`x³-x-1=0` under the half-open `(1,2]` existential. Applying the correspondence
theorem has no dedicated performance benchmark. The adapter is an explicit
development import built by `HexRCFRealFormula`; the released RCF umbrella
remains independent of the incubating frontend.
