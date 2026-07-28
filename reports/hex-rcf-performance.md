# HexRCF Performance Report

## Bench Targets

`HexRCF` has two separate Phase-4 evidence tracks. The Mathlib-free compiled
track is the `hexrcf_bench` LeanBench executable. The Mathlib-facing tactic
track is a build-only fresh-module sweep: it has no proof-probe executable,
`list`/`verify` entry, in-process clock, scientific asymptotic verdict, or
sampling profile. The two tracks are reported separately and their timings are
never added or substituted for one another.

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

The proof sweep preregisters nineteen adjacent fresh-module pairs in this exact
order. Six balanced rounds rotate the pair order and alternate the build
orientation.

| pair | reference | candidate | role |
|---|---|---|---|
| `fresh-build-null` | `Baseline` | `Baseline` | baseline null control |
| `degree10-tactic-null` | `Degree10.Tactic` | `Degree10.Tactic` | degree-10 tactic null control |
| `degree50-tactic-null` | `Degree50.Tactic` | `Degree50.Tactic` | degree-50 tactic null control |
| `double-degree50-null` | `DoubleDegree50` | `DoubleDegree50` | expensive null control containing two independent degree-50 `by rcf` theorems |
| `quadratic-reify` | `Baseline` | `Quadratic.Reify` | reification |
| `quadratic-search` | `Quadratic.Input` | `Quadratic.Search` | compiled-search attribution |
| `quadratic-literal` | `Quadratic.Input` | `Quadratic.Literal` | literal elaboration |
| `quadratic-replay` | `Quadratic.Literal` | `Quadratic.Replay` | kernel replay |
| `quadratic-tactic` | `Baseline` | `Quadratic.Tactic` | end-to-end tactic; 2 s regression-bound budget |
| `degree10-reify` | `Baseline` | `Degree10.Reify` | reification |
| `degree10-search` | `Degree10.Input` | `Degree10.Search` | compiled-search attribution |
| `degree10-literal` | `Degree10.Input` | `Degree10.Literal` | literal elaboration |
| `degree10-replay` | `Degree10.Literal` | `Degree10.Replay` | kernel replay |
| `degree10-tactic` | `Baseline` | `Degree10.Tactic` | end-to-end tactic; 12 s regression-bound budget |
| `degree50-reify` | `Baseline` | `Degree50.Reify` | reification |
| `degree50-search` | `Degree50.Input` | `Degree50.Search` | compiled-search attribution |
| `degree50-literal` | `Degree50.Input` | `Degree50.Literal` | literal elaboration |
| `degree50-replay` | `Degree50.Literal` | `Degree50.Replay` | kernel replay |
| `degree50-tactic` | `Baseline` | `Degree50.Tactic` | end-to-end tactic; 30 s adversarial-ceiling budget |

`HexRCFProofProbe` is the reduced structural CI target. It checks the common
support, all three reified goals, every committed literal against both the
accepted checker and the builder-output hash, and the quadratic module matrix.
`HexRCFProofProbeScientific` owns the degree-10 and degree-50 measured modules
and the expensive `DoubleDegree50` module.

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

The proof-producing commit `b44d6d8527886947dcce9218e4c05d020aa155ec`
and merged retry-headroom commit `f04cd955d149e4a102cd46c708ece26fc0776545`
have the identical tree `1f47d9c696547b4044d3af3ceb187c3e03886700`.
The compiled artifact's `leanprover/lean4:4.32.0-rc1` and proof artifact's
`leanprover/lean4:v4.32.0-rc1` are two renderings of the same
`lean-toolchain` pin. Source-closure claims below are anchored to that exact
producing snapshot; they are not claims about later report/status prose or
unrelated theorem additions on the eventual merged head.

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

The proof-track release command is:

```sh
python3 scripts/bench/hexrcf_proof_sweep.py --samples 6 \
  --timeout 300 --warm-timeout 600 \
  --shared-host --expected-host chungus2 --cpu 22 \
  --max-pair-retries 32 \
  --output /tmp/hexrcf-proof-probes-b44d6d852788-chungus2.json
```

The command fixes six samples, 300 s measured-arm and 600 s warm-build
timeouts, logical CPU 22, the preregistered hostname, a 0.002 aggregate
foreign-plus-SMT interference ratio, at most 32 whole-pair retries (attempts
1 through 33), a 2 s
quiet-core preflight window with at most two busy ticks on the target and each
SMT sibling, a 300 s preflight timeout, and a 0.15 frequency-spread ceiling.
The arm-admission allowance is the larger of 0.002 times arm wall time and
three scheduler ticks (0.030 s). The tick floor binds at these arm lengths,
giving a maximum effective ratio ceiling of 0.005481, above the admitted
maximum of 0.005396.
The runner sets `LEAN_NUM_THREADS=1`, inherits the CPU affinity into every timed
child, accounts measurement-CPU foreign work as
`busy-minus-child-minus-runner-minus-irq-softirq`, adds all SMT-sibling busy
time, and rejects the entire oriented pair if either arm exceeds the common
interference gate.

The proof artifact is committed byte-for-byte at the repository path below,
and this report cites its SHA-256 rather than mutable `/tmp` state.

| proof artifact field | artifact value |
|---|---|
| artifact | `reports/bench-results/hexrcf-proof-probes-b44d6d852788-chungus2.json` |
| artifact SHA-256 | `91ec1dc1c5438ca67ec3a22905accee3b654fc45ac0b01e1b9ea481f7538bc01` |
| embedded source-hash map | `source_sha256` in the cited artifact |
| schema | `hexrcf-proof-probes-v6` |
| measurement | `paired-fresh-module-olean-wall-v1` |
| measurement state | `complete` |
| release quality | `True` |
| validity exceptions | `[]` |
| host protocol | `designated-shared-host-v3` |
| git commit / dirty | `b44d6d8527886947dcce9218e4c05d020aa155ec` / `False` |
| toolchain / host | `leanprover/lean4:v4.32.0-rc1` / `chungus2` |
| CPU topology | logical `22`, package `0`, core `52`, sibling list `22,70`, governor `schedutil` |
| accepted paired samples / timed arms | `114` / `228` |
| contaminated-pair retry cap / allowed attempt range / observed maximum attempt | `32` / `1..33` / `9` |
| rejected pair attempts | `93` |
| rejected preflight windows / failures | `103` / `0` |
| exhausted pairs | `0` |
| maximum admitted aggregate core-interference ratio | `0.005396` |
| maximum effective quantized core-interference ratio | `0.005481` |
| maximum interference allowance | `0.030000000 s` |
| frequency range / spread | `3150000.000` … `3150000.000 kHz`; `0.000000` |
| maximum preflight wait | `18.007466254 s` |
| maximum one-minute load per logical CPU | `0.082417806` |
| maximum CPU-pressure `some` delta | `4,626,814 us` |
| maximum concurrent Lake/Lean process count | `7` |

Only wholly admitted complete-pair attempts enter the following raw tables.
Each cell is `attempt, orientation; reference / candidate / signed
candidate-reference`, with wall times rendered from the artifact's exact
nanosecond values. `R->C` and `C->R` are build orientations. The four null
controls are reported before substantive measurements and are descriptive
only.

| null control | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `fresh-build-null` | `a1, R->C; 5,500,740,005 ns / 5,491,887,621 ns / -8,852,384 ns` | `a1, C->R; 5,496,524,925 ns / 5,494,621,165 ns / -1,903,760 ns` | `a1, R->C; 5,506,516,301 ns / 5,511,857,883 ns / +5,341,582 ns` | `a1, C->R; 5,571,531,183 ns / 5,518,101,343 ns / -53,429,840 ns` | `a1, R->C; 5,497,132,461 ns / 5,473,273,595 ns / -23,858,866 ns` | `a1, C->R; 5,544,893,007 ns / 5,489,753,647 ns / -55,139,360 ns` |
| `degree10-tactic-null` | `a1, R->C; 10,011,518,429 ns / 10,044,665,255 ns / +33,146,826 ns` | `a4, C->R; 9,786,592,825 ns / 9,844,267,273 ns / +57,674,448 ns` | `a2, R->C; 9,808,178,732 ns / 9,833,463,945 ns / +25,285,213 ns` | `a6, C->R; 9,806,844,524 ns / 9,811,166,439 ns / +4,321,915 ns` | `a1, R->C; 9,808,860,052 ns / 9,801,224,151 ns / -7,635,901 ns` | `a1, C->R; 9,910,271,933 ns / 9,904,756,537 ns / -5,515,396 ns` |
| `degree50-tactic-null` | `a2, R->C; 9,855,667,155 ns / 9,817,186,316 ns / -38,480,839 ns` | `a3, C->R; 9,876,195,709 ns / 9,834,905,245 ns / -41,290,464 ns` | `a2, R->C; 9,885,213,534 ns / 9,824,585,273 ns / -60,628,261 ns` | `a1, C->R; 9,886,299,250 ns / 9,776,576,860 ns / -109,722,390 ns` | `a1, R->C; 9,868,009,108 ns / 9,859,602,312 ns / -8,406,796 ns` | `a1, C->R; 9,857,474,466 ns / 9,765,018,422 ns / -92,456,044 ns` |
| `double-degree50-null` | `a1, R->C; 14,145,392,504 ns / 14,169,484,450 ns / +24,091,946 ns` | `a5, C->R; 14,006,193,294 ns / 14,040,185,473 ns / +33,992,179 ns` | `a1, R->C; 13,942,844,592 ns / 13,981,409,606 ns / +38,565,014 ns` | `a1, C->R; 13,939,820,325 ns / 13,928,965,499 ns / -10,854,826 ns` | `a4, R->C; 13,934,184,948 ns / 14,009,286,365 ns / +75,101,417 ns` | `a6, C->R; 13,993,523,335 ns / 13,948,899,883 ns / -44,623,452 ns` |

| null control | signed range | absolute span | relative range | median relative delta | median signed delta | zero-centred envelope | build magnitude |
|---|---|---|---|---|---|---|---|
| `fresh-build-null` | `-55,139,360 ns … +5,341,582 ns` | `60,480,942 ns` | `-0.994417% … +0.097005%; span 1.091422%` | `-0.297477%` | `-16,355,625 ns` | `55,139,360 ns` | `5,503,628,153 ns` |
| `degree10-tactic-null` | `-7,635,901 ns … +57,674,448 ns` | `65,310,349 ns` | `-0.077847% … +0.589321%; span 0.667168%` | `+0.150934%` | `+14,803,564 ns` | `57,674,448 ns` | `9,838,865,609 ns` |
| `degree50-tactic-null` | `-109,722,390 ns … -8,406,796 ns` | `101,315,594 ns` | `-1.109843% … -0.085192%; span 1.024650%` | `-0.515702%` | `-50,959,362 ns` | `109,722,390 ns` | `9,872,102,408 ns` |
| `double-degree50-null` | `-44,623,452 ns … +75,101,417 ns` | `119,724,869 ns` | `-0.318886% … +0.538972%; span 0.857859%` | `+0.206505%` | `+29,042,062 ns` | `75,101,417 ns` | `13,995,347,985 ns` |

| substantive pair | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `quadratic-reify` | `a1, R->C; 5,474,655,722 ns / 5,574,279,157 ns / +99,623,435 ns` | `a1, C->R; 5,587,719,271 ns / 5,647,035,149 ns / +59,315,878 ns` | `a1, R->C; 5,497,596,322 ns / 5,566,353,906 ns / +68,757,584 ns` | `a1, C->R; 5,481,852,110 ns / 5,603,343,566 ns / +121,491,456 ns` | `a1, R->C; 5,504,570,814 ns / 5,592,714,740 ns / +88,143,926 ns` | `a3, C->R; 5,590,524,547 ns / 5,648,575,540 ns / +58,050,993 ns` |
| `quadratic-search` | `a1, R->C; 5,511,905,524 ns / 5,603,141,965 ns / +91,236,441 ns` | `a1, C->R; 5,584,987,947 ns / 5,577,564,880 ns / -7,423,067 ns` | `a1, R->C; 5,562,697,284 ns / 5,524,480,498 ns / -38,216,786 ns` | `a1, C->R; 5,512,114,057 ns / 5,551,612,942 ns / +39,498,885 ns` | `a2, R->C; 5,586,804,475 ns / 5,590,654,233 ns / +3,849,758 ns` | `a1, C->R; 5,575,091,870 ns / 5,579,397,816 ns / +4,305,946 ns` |
| `quadratic-literal` | `a1, R->C; 5,575,239,332 ns / 5,616,939,672 ns / +41,700,340 ns` | `a1, C->R; 5,608,990,269 ns / 5,630,657,763 ns / +21,667,494 ns` | `a1, R->C; 5,518,371,521 ns / 5,565,815,228 ns / +47,443,707 ns` | `a1, C->R; 5,511,905,583 ns / 5,553,157,477 ns / +41,251,894 ns` | `a3, R->C; 5,602,564,979 ns / 5,631,457,412 ns / +28,892,433 ns` | `a5, C->R; 5,596,381,482 ns / 5,626,545,270 ns / +30,163,788 ns` |
| `quadratic-replay` | `a3, R->C; 5,601,564,994 ns / 5,770,125,560 ns / +168,560,566 ns` | `a4, C->R; 5,575,183,809 ns / 5,733,511,928 ns / +158,328,119 ns` | `a1, R->C; 5,586,455,063 ns / 5,694,525,936 ns / +108,070,873 ns` | `a1, C->R; 5,590,342,120 ns / 5,710,402,625 ns / +120,060,505 ns` | `a1, R->C; 5,587,241,182 ns / 5,753,474,099 ns / +166,232,917 ns` | `a2, C->R; 5,646,610,411 ns / 5,785,275,135 ns / +138,664,724 ns` |
| `quadratic-tactic` | `a1, R->C; 5,597,141,309 ns / 5,851,923,364 ns / +254,782,055 ns` | `a1, C->R; 5,551,014,522 ns / 5,851,565,512 ns / +300,550,990 ns` | `a1, R->C; 5,520,561,528 ns / 5,772,557,457 ns / +251,995,929 ns` | `a1, C->R; 5,563,992,451 ns / 5,862,542,785 ns / +298,550,334 ns` | `a1, R->C; 5,569,230,235 ns / 5,849,116,449 ns / +279,886,214 ns` | `a2, C->R; 5,546,143,098 ns / 5,879,965,965 ns / +333,822,867 ns` |
| `degree10-reify` | `a1, R->C; 5,527,733,135 ns / 6,017,550,102 ns / +489,816,967 ns` | `a1, C->R; 5,577,066,829 ns / 6,070,235,722 ns / +493,168,893 ns` | `a1, R->C; 5,566,997,280 ns / 6,032,997,202 ns / +465,999,922 ns` | `a4, C->R; 5,534,189,192 ns / 6,075,181,534 ns / +540,992,342 ns` | `a1, R->C; 5,559,865,151 ns / 6,079,063,269 ns / +519,198,118 ns` | `a2, C->R; 5,512,942,290 ns / 6,032,939,587 ns / +519,997,297 ns` |
| `degree10-search` | `a1, R->C; 5,538,147,272 ns / 5,604,814,162 ns / +66,666,890 ns` | `a1, C->R; 5,543,876,317 ns / 5,613,559,229 ns / +69,682,912 ns` | `a1, R->C; 5,563,927,424 ns / 5,638,066,085 ns / +74,138,661 ns` | `a2, C->R; 5,610,182,040 ns / 5,713,834,852 ns / +103,652,812 ns` | `a4, R->C; 5,533,367,974 ns / 5,619,066,630 ns / +85,698,656 ns` | `a1, C->R; 5,599,441,033 ns / 5,617,700,235 ns / +18,259,202 ns` |
| `degree10-literal` | `a4, R->C; 5,765,647,372 ns / 6,306,829,700 ns / +541,182,328 ns` | `a1, C->R; 5,575,299,615 ns / 6,303,817,248 ns / +728,517,633 ns` | `a1, R->C; 5,622,784,640 ns / 6,398,679,449 ns / +775,894,809 ns` | `a6, C->R; 5,589,342,091 ns / 6,381,936,114 ns / +792,594,023 ns` | `a1, R->C; 5,544,800,818 ns / 6,277,966,862 ns / +733,166,044 ns` | `a2, C->R; 5,537,673,953 ns / 6,335,114,314 ns / +797,440,361 ns` |
| `degree10-replay` | `a3, R->C; 6,299,814,956 ns / 10,087,007,827 ns / +3,787,192,871 ns` | `a1, C->R; 6,308,370,070 ns / 9,990,043,234 ns / +3,681,673,164 ns` | `a3, R->C; 6,261,160,448 ns / 9,925,643,971 ns / +3,664,483,523 ns` | `a1, C->R; 6,414,725,952 ns / 10,026,145,806 ns / +3,611,419,854 ns` | `a1, R->C; 6,313,854,832 ns / 10,032,448,792 ns / +3,718,593,960 ns` | `a3, C->R; 6,301,119,160 ns / 10,064,265,415 ns / +3,763,146,255 ns` |
| `degree10-tactic` | `a1, R->C; 5,504,251,583 ns / 9,838,084,906 ns / +4,333,833,323 ns` | `a1, C->R; 5,520,109,945 ns / 9,800,803,719 ns / +4,280,693,774 ns` | `a6, R->C; 5,568,308,768 ns / 9,903,699,313 ns / +4,335,390,545 ns` | `a2, C->R; 5,502,448,394 ns / 9,760,969,709 ns / +4,258,521,315 ns` | `a6, R->C; 5,580,548,610 ns / 9,928,734,892 ns / +4,348,186,282 ns` | `a1, C->R; 5,514,155,781 ns / 9,809,974,834 ns / +4,295,819,053 ns` |
| `degree50-reify` | `a1, R->C; 5,499,503,667 ns / 6,104,679,700 ns / +605,176,033 ns` | `a1, C->R; 5,586,684,276 ns / 6,131,579,039 ns / +544,894,763 ns` | `a1, R->C; 5,487,297,767 ns / 6,083,310,150 ns / +596,012,383 ns` | `a1, C->R; 5,501,769,190 ns / 6,106,033,418 ns / +604,264,228 ns` | `a1, R->C; 5,501,640,719 ns / 6,145,183,473 ns / +643,542,754 ns` | `a1, C->R; 5,492,715,977 ns / 6,059,827,504 ns / +567,111,527 ns` |
| `degree50-search` | `a1, R->C; 5,511,497,749 ns / 6,507,169,590 ns / +995,671,841 ns` | `a3, C->R; 5,593,306,846 ns / 6,588,892,435 ns / +995,585,589 ns` | `a9, R->C; 5,611,863,153 ns / 6,613,112,483 ns / +1,001,249,330 ns` | `a1, C->R; 5,611,034,870 ns / 6,499,202,203 ns / +888,167,333 ns` | `a1, R->C; 5,559,515,917 ns / 6,525,642,692 ns / +966,126,775 ns` | `a1, C->R; 5,547,518,394 ns / 6,514,306,692 ns / +966,788,298 ns` |
| `degree50-literal` | `a1, R->C; 5,540,503,692 ns / 5,799,193,548 ns / +258,689,856 ns` | `a1, C->R; 5,603,146,495 ns / 5,860,002,561 ns / +256,856,066 ns` | `a2, R->C; 5,640,351,973 ns / 5,879,586,723 ns / +239,234,750 ns` | `a2, C->R; 5,594,879,018 ns / 5,894,378,236 ns / +299,499,218 ns` | `a1, R->C; 5,512,182,387 ns / 5,822,002,298 ns / +309,819,911 ns` | `a1, C->R; 5,593,153,961 ns / 5,835,931,475 ns / +242,777,514 ns` |
| `degree50-replay` | `a1, R->C; 5,806,918,660 ns / 8,537,104,937 ns / +2,730,186,277 ns` | `a1, C->R; 5,807,157,511 ns / 8,551,840,097 ns / +2,744,682,586 ns` | `a1, R->C; 5,811,721,060 ns / 8,522,355,544 ns / +2,710,634,484 ns` | `a3, C->R; 5,798,746,277 ns / 8,518,951,336 ns / +2,720,205,059 ns` | `a1, R->C; 5,815,586,554 ns / 8,605,634,932 ns / +2,790,048,378 ns` | `a1, C->R; 5,812,887,338 ns / 8,589,774,670 ns / +2,776,887,332 ns` |
| `degree50-tactic` | `a1, R->C; 5,524,731,283 ns / 9,906,924,367 ns / +4,382,193,084 ns` | `a1, C->R; 5,511,034,474 ns / 9,855,380,715 ns / +4,344,346,241 ns` | `a1, R->C; 5,519,214,487 ns / 9,817,163,643 ns / +4,297,949,156 ns` | `a1, C->R; 5,494,378,373 ns / 9,812,585,838 ns / +4,318,207,465 ns` | `a5, R->C; 5,606,123,428 ns / 9,857,211,050 ns / +4,251,087,622 ns` | `a1, C->R; 5,508,409,577 ns / 9,793,718,567 ns / +4,285,308,990 ns` |

For every pair, build magnitude is the larger of the median reference and
candidate wall times. A null is comparable when the larger/smaller build
magnitude ratio is at most 3; among comparable nulls, the runner selects the
one whose magnitude has the smallest normalized distance from the substantive
pair. The recorded control ratio is `max(pair, control) / min(pair, control)`.
The raw null spread and zero-centred maximum-absolute envelope are multiplied
by `max(pair magnitude, control magnitude) / control magnitude`, rounded up to
integer nanoseconds. Thus a cheaper control scales up and a more expensive
control is never scaled down. A pair is resolved exactly when the absolute
median signed delta is greater than the scaled envelope. Null medians are never
subtracted, and all reported proof times and deltas remain raw and uncorrected.
The signed-delta column is the median of the six paired deltas, not the
difference between the separately computed reference and candidate medians;
it is the paired statistic consumed by the resolution and budget rules.

| substantive pair | median reference | median candidate | median signed delta | selected control | magnitude ratio | raw control span | raw envelope | scaled span | scaled envelope | resolution |
|---|---|---|---|---|---|---|---|---|---|---|
| `quadratic-reify` | `5,501,083,568 ns` | `5,598,029,153 ns` | `+78,450,755 ns` | `fresh-build-null` | `1.017153` | `60,480,942 ns` | `55,139,360 ns` | `61,518,342 ns` | `56,085,139 ns` | `resolved` |
| `quadratic-search` | `5,568,894,577 ns` | `5,578,481,348 ns` | `+4,077,852 ns` | `fresh-build-null` | `1.013601` | `60,480,942 ns` | `55,139,360 ns` | `61,303,526 ns` | `55,889,294 ns` | `unresolved` |
| `quadratic-literal` | `5,585,810,407 ns` | `5,621,742,471 ns` | `+35,707,841 ns` | `fresh-build-null` | `1.021461` | `60,480,942 ns` | `55,139,360 ns` | `61,778,934 ns` | `56,322,716 ns` | `unresolved` |
| `quadratic-replay` | `5,588,791,651 ns` | `5,743,493,013 ns` | `+148,496,421 ns` | `fresh-build-null` | `1.043583` | `60,480,942 ns` | `55,139,360 ns` | `63,116,886 ns` | `57,542,502 ns` | `resolved` |
| `quadratic-tactic` | `5,557,503,486 ns` | `5,851,744,438 ns` | `+289,218,274 ns` | `fresh-build-null` | `1.063252` | `60,480,942 ns` | `55,139,360 ns` | `64,306,492 ns` | `58,627,043 ns` | `resolved` |
| `degree10-reify` | `5,547,027,171 ns` | `6,051,616,462 ns` | `+506,183,505 ns` | `fresh-build-null` | `1.099569` | `60,480,942 ns` | `55,139,360 ns` | `66,502,943 ns` | `60,629,507 ns` | `resolved` |
| `degree10-search` | `5,553,901,870 ns` | `5,618,383,432 ns` | `+71,910,786 ns` | `fresh-build-null` | `1.020851` | `60,480,942 ns` | `55,139,360 ns` | `61,742,021 ns` | `56,289,063 ns` | `resolved` |
| `degree10-literal` | `5,582,320,853 ns` | `6,320,972,007 ns` | `+754,530,426 ns` | `fresh-build-null` | `1.148510` | `60,480,942 ns` | `55,139,360 ns` | `69,462,968 ns` | `63,328,107 ns` | `resolved` |
| `degree10-replay` | `6,304,744,615 ns` | `10,029,297,299 ns` | `+3,700,133,562 ns` | `degree50-tactic-null` | `1.015923` | `101,315,594 ns` | `109,722,390 ns` | `102,928,857 ns` | `111,469,516 ns` | `resolved` |
| `degree10-tactic` | `5,517,132,863 ns` | `9,824,029,870 ns` | `+4,314,826,188 ns` | `degree10-tactic-null` | `1.001510` | `65,310,349 ns` | `57,674,448 ns` | `65,310,349 ns` | `57,674,448 ns` | `resolved` |
| `degree50-reify` | `5,500,572,193 ns` | `6,105,356,559 ns` | `+600,138,305 ns` | `fresh-build-null` | `1.109333` | `60,480,942 ns` | `55,139,360 ns` | `67,093,508 ns` | `61,167,914 ns` | `resolved` |
| `degree50-search` | `5,576,411,381 ns` | `6,519,974,692 ns` | `+981,186,943 ns` | `fresh-build-null` | `1.184668` | `60,480,942 ns` | `55,139,360 ns` | `71,649,865 ns` | `65,321,861 ns` | `resolved` |
| `degree50-literal` | `5,594,016,489 ns` | `5,847,967,018 ns` | `+257,772,961 ns` | `fresh-build-null` | `1.062566` | `60,480,942 ns` | `55,139,360 ns` | `64,264,981 ns` | `58,589,198 ns` | `resolved` |
| `degree50-replay` | `5,809,439,285 ns` | `8,544,472,517 ns` | `+2,737,434,431 ns` | `degree10-tactic-null` | `1.151489` | `65,310,349 ns` | `57,674,448 ns` | `65,310,349 ns` | `57,674,448 ns` | `resolved` |
| `degree50-tactic` | `5,515,124,480 ns` | `9,836,272,179 ns` | `+4,308,078,310 ns` | `degree10-tactic-null` | `1.000264` | `65,310,349 ns` | `57,674,448 ns` | `65,310,349 ns` | `57,674,448 ns` | `resolved` |

The artifact classifies the quadratic and degree-10 budgets as
`regression-bound` and the degree-50 budget as `adversarial-ceiling`. The tactic
budget status is `passed` only when both the median signed delta is
strictly below its fixed budget and `median delta + scaled envelope` is
strictly below that budget. Under the shared-host protocol, the artifact's
two-arm `budget_interference_ceiling_nanos` must also be strictly below the
budget. No null value is subtracted or used to change a budget.

| tactic pair | budget | kind | median signed delta | scaled envelope | median + envelope | two-arm interference ceiling | status |
|---|---:|---|---:|---:|---:|---:|---|
| `quadratic-tactic` | 2,000,000,000 ns | `regression-bound` | `+289,218,274 ns` | `58,627,043 ns` | `+347,845,317 ns` | `60,000,000 ns` | `passed` |
| `degree10-tactic` | 12,000,000,000 ns | `regression-bound` | `+4,314,826,188 ns` | `57,674,448 ns` | `+4,372,500,636 ns` | `60,000,000 ns` | `passed` |
| `degree50-tactic` | 30,000,000,000 ns | `adversarial-ceiling` | `+4,308,078,310 ns` | `57,674,448 ns` | `+4,365,752,758 ns` | `60,000,000 ns` | `passed` |

Only `Replay`, `Tactic`, and `DoubleDegree50` print axioms; their fixed expected
set is `[propext, Classical.choice, Quot.sound]`. The artifact also records the
emitted module sizes, retained arm wall times, timeout configuration, and the
source hash for the runner that implements timeout cleanup.

| module | expected / observed axioms | ilean bytes | olean bytes | private bytes | server bytes | source bytes |
|---|---|---:|---:|---:|---:|---:|
| `Baseline` | `null / null` | `195` | `1,672` | `808` | `904` | `338` |
| `DoubleDegree50` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `840` | `13,880` | `295,720` | `1,760` | `836` |
| `Quadratic.Reify` | `null / null` | `202` | `2,176` | `5,208` | `912` | `462` |
| `Quadratic.Input` | `null / null` | `545` | `4,344` | `30,160` | `1,296` | `430` |
| `Quadratic.Search` | `null / null` | `547` | `4,344` | `30,160` | `1,320` | `503` |
| `Quadratic.Literal` | `null / null` | `924` | `4,992` | `57,720` | `1,568` | `523` |
| `Quadratic.Replay` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `1,462` | `5,968` | `59,496` | `1,800` | `843` |
| `Quadratic.Tactic` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `372` | `8,680` | `69,176` | `1,280` | `687` |
| `Degree10.Reify` | `null / null` | `201` | `2,176` | `5,368` | `912` | `458` |
| `Degree10.Input` | `null / null` | `540` | `4,344` | `65,784` | `1,296` | `427` |
| `Degree10.Search` | `null / null` | `542` | `4,344` | `65,784` | `1,320` | `498` |
| `Degree10.Literal` | `null / null` | `915` | `5,176` | `2,421,848` | `1,568` | `519` |
| `Degree10.Replay` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `1,446` | `6,008` | `2,422,912` | `1,800` | `838` |
| `Degree10.Tactic` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `369` | `14,544` | `409,168` | `1,280` | `683` |
| `Degree50.Reify` | `null / null` | `201` | `2,176` | `5,416` | `912` | `458` |
| `Degree50.Input` | `null / null` | `540` | `4,344` | `70,616` | `1,296` | `427` |
| `Degree50.Search` | `null / null` | `542` | `4,344` | `70,616` | `1,320` | `498` |
| `Degree50.Literal` | `null / null` | `915` | `5,176` | `387,968` | `1,568` | `519` |
| `Degree50.Replay` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `1,446` | `6,008` | `389,032` | `1,800` | `838` |
| `Degree50.Tactic` | `[propext, Classical.choice, Quot.sound] / [propext, Classical.choice, Quot.sound]` | `369` | `12,280` | `275,944` | `1,280` | `683` |

Proof-track timeout cleanup was not exercised: every retained arm completed
below the recorded 300 s timeout, no pair was exhausted, and no preflight
failed. Thus the observed state is clean; the cleanup implementation is pinned
by the recorded `scripts/bench/fresh_module_sweep.py` source hash.

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
compiled and proof artifacts above.

The proof track is represented by
`reports/bench-results/hexrcf-proof-probes-b44d6d852788-chungus2.json`.
Timed-region sampling does not apply to that build-only fresh-module surface:
its evidence is the rotated external compiler/kernel sweep, not an executable
with an in-process timed region.

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
