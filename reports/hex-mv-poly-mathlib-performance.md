# HexMvPolyMathlib Performance Report

## Bench Targets

`HexMvPolyMathlib` is a proof-only companion. Its Phase-4 evidence lives under
`bench/HexMvPolyMathlib/ProofProbe/` and is built as fresh downstream modules
with:

```sh
lake build +<module>:olean
```

The suite covers sparse addition, low- and high-collision multiplication,
`Int` and `Rat` cancellation identities, sum-of-squares certificates, and a
rename/substitution collision case. The axes include arity 4 and 8, lex,
grlex, and grevlex, and matched production/sorted support streams. Each
measured theorem uses `decide +kernel`; every emitted proof is audited with
`#print axioms`.

The paired sweep is driven by
`scripts/bench/hex_mv_poly_kernel_sweep.py`. Reference modules use the
production Hex `ExtTreeMap` representation. Candidate modules use the
canonical sorted-list MvSparsePoly proxy from
`bench/HexMvPolyMathlib/ProofProbe/Support.lean`, with linear merge addition
and balanced translated-row multiplication.

The companion surface also passes the pinned consumer acceptance described in
`reports/hex-mv-poly-performance.md`: the full SOS tactic and example suite
compile and replay their kernel-checked certificates, and CompPoly's
univariate and bivariate recursive-view adapters compile after the disclosed
toolchain proof rewrite.

## Verdicts

The release-quality sweep used clean commit
`12cc25590c2eead26613704e2421822306faa943` on `chungus2` (AMD EPYC 9455,
x86-64 Linux), one Lean thread pinned to logical CPU 22, six rotated paired
samples, and complete fresh-module builds. Command:

```sh
python3 scripts/bench/hex_mv_poly_kernel_sweep.py \
  --samples 6 \
  --timeout 300 \
  --warm-timeout 600 \
  --shared-host \
  --expected-host chungus2 \
  --cpu 22 \
  --max-pair-retries 32 \
  --output reports/bench-results/hex-mv-poly-kernel-12cc2559-chungus2.json
```

The committed export is
`reports/bench-results/hex-mv-poly-kernel-12cc2559-chungus2.json`
(SHA-256
`d55476ad38d668a87e5bd0fc5c55077a481a9f09b1e4ad844972cc63682546ff`).
It is complete, reports `release_quality: true`, has no validity exceptions,
preflight failures, or exhausted pairs, and records two rejected contaminated
pair attempts before successful retries.

The import-only baseline median is 1.356371 s. Its centred variability has a
2.806 ms IQR and a 6.570 ms robust Tukey envelope. Both substantive workloads
must exceed that envelope before their ratio can be classified. The raw-ratio
cap is `Hex raw / import baseline`: it is the largest raw fresh-build ratio
possible even if the candidate workload itself took zero time.

| case | Hex raw | sorted raw | Hex workload | sorted workload | Hex / sorted workload | raw-ratio cap | ratio status |
|---|---:|---:|---:|---:|---:|---:|---|
| `addition-inputs-32` | 2.059 s | 1.572 s | 0.703 s | 0.214 s | 3.290× | 1.518× | resolved construction control |
| `addition-32` | 2.961 s | 1.769 s | 1.603 s | 0.413 s | 3.885× | 2.183× | resolved before construction subtraction |
| `addition-32`, net arithmetic | — | — | 0.902 s | 0.199 s | 4.528× | — | noise-limited |
| `multiplication-sparse-6` | 1.763 s | 2.459 s | 0.408 s | 1.104 s | 0.369× | 1.300× | resolved |
| `multiplication-collide-8` | 2.160 s | 2.159 s | 0.803 s | 0.802 s | 1.001× | 1.593× | noise-limited |
| `cancellation-4` | 1.965 s | 1.756 s | 0.610 s | 0.400 s | 1.527× | 1.449× | resolved |
| `cancellation-6` | 3.360 s | 2.359 s | 2.003 s | 1.001 s | 2.001× | 2.477× | resolved |
| `sos-3` | 1.959 s | 1.657 s | 0.603 s | 0.300 s | 2.008× | 1.444× | resolved |
| `sos-4` | 2.659 s | 1.862 s | 1.302 s | 0.505 s | 2.579× | 1.961× | resolved |
| `structural-8` | 1.460 s | 1.459 s | 0.101 s | 0.101 s | 0.997× | 1.076× | noise-limited |

The addition result has an additional matched construction control because the
two representations do not build their input polynomials at the same cost.
Subtracting that control round by round leaves 0.902 s of median Hex
arithmetic and 0.199 s of sorted arithmetic. The combined full-pair and
construction-control null envelope is 302.339 ms, so the sorted net arm lies
inside the envelope. Its 4.528× point ratio is therefore noise-limited and
does not count toward the representation threshold.

The paired raw wall-time deltas (`sorted - Hex`) were:

- `addition-inputs-32`: −596.4, −497.8, −486.4, −404.2, −496.1, −491.8 ms.
- `addition-32`: −1089.4, −1196.6, −1001.5, −1202.9, −999.9, −1194.6 ms.
- `multiplication-sparse-6`: +696.9, +702.7, +395.4, +696.7, +692.1, +801.4 ms.
- `multiplication-collide-8`: −7.2, +4.3, −7.2, +13.8, −6.4, +403.3 ms.
- `cancellation-4`: −199.2, −204.0, −208.5, −204.2, −215.8, −304.1 ms.
- `cancellation-6`: −993.9, −1101.0, −990.6, −1003.3, −998.5, −1004.1 ms.
- `sos-3`: −302.9, −299.4, −296.9, −299.6, −306.1, −305.8 ms.
- `sos-4`: −703.7, −801.4, −794.6, −803.5, −787.6, −791.2 ms.
- `structural-8`: −2.2, −0.0, −4.5, +4.4, +0.2, +0.4 ms.

The cheap null has a 4.010 ms IQR and 9.094 ms robust envelope; the expensive
null has a 104.408 ms IQR and 255.339 ms robust envelope. Their IQR/build
ratios are 0.296% and 3.112%, below the 10% invalidation limit. Interpolating
these envelopes resolves every substantive delta except
`multiplication-collide-8` and `structural-8`. The additional construction
subtraction makes `addition-32` noise-limited as described above.

At the largest measured rung in each registered family:

| family | case | Hex / sorted workload | threshold result |
|---|---|---:|---|
| `kernel-sparse-addition` | `addition-32` | 4.528× net | unresolved; does not pass |
| `kernel-sparse-multiplication` | `multiplication-collide-8` | 1.001× | unresolved |
| `kernel-cancellation-identities` | `cancellation-6` | 2.001× | passes narrowly |
| `kernel-structural-collisions` | `structural-8` | 0.997× | unresolved |
| `kernel-sos-certificates` | `sos-4` | 2.579× | passes |

Exactly two families have resolved greater-than-2× sorted wins. The
predeclared threshold is therefore met: a second kernel-specialized sorted
representation is justified. This does not replace the compiled
`ExtTreeMap` representation, and the benchmark proxy is not promoted as a
public implementation. The follow-up representation belongs behind the
swappable polynomial abstraction recorded in `SPEC/future-work.md`. The
cancellation family clears 2× by only 0.1%, so the result satisfies the written
rule without establishing a wide margin.

Every measured reference and candidate theorem reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `axiom`, or `native_decide` is used by the proof probes.

## Comparator Ratios

The named informational comparator is **Mathlib MvSparsePoly**. That
implementation is absent from the pinned Mathlib revision because its
upstream PR series has not landed. The measured candidate is a local
canonical sorted-list proxy implementing the specified algorithmic shape; no
claim is made about the precise constant factors of unavailable upstream
code.

The workload ratios in the Verdicts table are the decision ratios. Raw
fresh-module ratios cannot show the SOS result faithfully: its mathematical
cap is only 1.961× because import/elaboration overhead dominates the candidate
arm. Round-matched import subtraction is therefore material, not cosmetic.
For addition, the additional construction subtraction is equally material:
the large point ratio remains unresolved once only arithmetic work is
attributed to the pair.

The native companion ratios are recorded separately in
`reports/hex-mv-poly-performance.md`. They help characterize compiled
throughput but do not override the kernel-specific decision.

## Profile

Sampling profiles are not applicable. `HexMvPolyMathlib` has no compiled
LeanBench timed region: its registrations are downstream fresh-module
elaboration and kernel-checking probes. Per `SPEC/profiling.md`, the
replacement evidence is the rotated paired-build record, source and compiler
artifact hashes, proof axioms, import and same-module null controls,
CPU-accounting record, and retry history in the committed export.

The export records the clean source commit, toolchain and dependency
checkouts, CPU topology and affinity, per-pair build order, wall time, peak
RSS, scheduler/frequency observations, rejected attempts, module artifact
sizes, exact comparison axes, and source SHA-256 values. The host protocol
observed a 1.48% frequency spread, at most three concurrent Lake/Lean
processes, two rejected pair attempts, three rejected quiet-core windows, and
no validity violation.

## Concerns

The Phase-4 artifact itself has no validity exception. It makes a positive
decision under the preregistered rule, but the cancellation family clears the
2× boundary by only 0.1%; that is threshold-compliant evidence, not a broad
performance margin. Sparse addition is explicitly unresolved after matched
construction subtraction. The production library therefore remains a single
`ExtTreeMap` representation, while an opt-in kernel-specialized sorted form is
recorded only as follow-up work behind a representation abstraction.

The unavailable upstream `Mathlib MvSparsePoly` remains an explicit comparator
limitation. Before shipping the second representation, its local proxy
algorithms need a supported public type, correspondence proofs, and a repeat
of the SOS kernel-consumer acceptance; the current proof-probe adapter is
evidence, not production API.
