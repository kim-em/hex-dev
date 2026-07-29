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

Addition, cancellation, and SOS have matched construction-only modules. Their
input-building costs are subtracted round by round after import subtraction,
so a faster constructor cannot be reported as faster polynomial arithmetic.
The threshold classifier then applies the interpolated null envelope to both
arms of the resulting ratio.

The companion surface also passes the pinned consumer acceptance described in
`reports/hex-mv-poly-performance.md`: the full SOS tactic and example suite
compile and replay their kernel-checked certificates, and CompPoly's
univariate and bivariate recursive-view adapters compile after the disclosed
toolchain proof rewrite.

## Verdicts

The release-quality sweep used clean commit
`77b76dd35be098a0bb4c5508306ba7957bb8d4b4` on `chungus2` (AMD EPYC 9455,
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
  --output reports/bench-results/hex-mv-poly-kernel-77b76dd3-chungus2.json
```

The committed export is
`reports/bench-results/hex-mv-poly-kernel-77b76dd3-chungus2.json`
(SHA-256
`308fa199e10c666a13761a8a3a41ef7096c7a9de5b2bc07834e5836119491897`).
It is complete, reports `release_quality: true`, has no validity exceptions,
preflight failures, rejected pair attempts, or exhausted pairs. Three
preflight windows were rejected before measurement.

The import-only baseline median is 1.359564 s. Its centred variability has a
3.356 ms IQR and a 7.387 ms robust Tukey envelope. The raw-ratio cap is
`Hex raw / import baseline`: it is the largest raw fresh-build ratio possible
even if the candidate workload itself took zero time.

| case | Hex raw | sorted raw | Hex workload | sorted workload | Hex / sorted workload | raw-ratio cap | ratio status |
|---|---:|---:|---:|---:|---:|---:|---|
| `addition-inputs-32` | 2.061 s | 1.565 s | 0.700 s | 0.204 s | 3.426× | 1.516× | resolved construction control |
| `addition-32` | 2.818 s | 1.762 s | 1.459 s | 0.402 s | 3.629× | 2.073× | resolved before construction subtraction |
| `addition-32`, net arithmetic | — | — | 0.757 s | 0.198 s | 3.817× | — | noise-limited |
| `multiplication-sparse-6` | 1.762 s | 2.463 s | 0.402 s | 1.103 s | 0.364× | 1.296× | resolved |
| `multiplication-collide-8` | 2.162 s | 2.071 s | 0.803 s | 0.709 s | 1.133× | 1.590× | resolved |
| `cancellation-4` | 1.960 s | 1.760 s | 0.601 s | 0.399 s | 1.507× | 1.442× | resolved |
| `cancellation-6` | 3.163 s | 2.360 s | 1.805 s | 1.000 s | 1.805× | 2.327× | resolved |
| `cancellation-inputs-8` | 1.461 s | 1.368 s | 0.101 s | 0.007 s | 15.083× | 1.075× | baseline-limited construction control |
| `cancellation-8` | 4.961 s | 3.264 s | 3.601 s | 1.902 s | 1.893× | 3.649× | resolved before construction subtraction |
| `cancellation-8`, net arithmetic | — | — | 3.499 s | 1.895 s | 1.847× | — | resolved |
| `sos-3` | 1.960 s | 1.659 s | 0.601 s | 0.299 s | 2.009× | 1.442× | resolved |
| `sos-4` | 2.560 s | 1.861 s | 1.200 s | 0.500 s | 2.400× | 1.883× | resolved |
| `sos-inputs-6` | 1.460 s | 1.365 s | 0.102 s | 0.005 s | 21.007× | 1.074× | baseline-limited construction control |
| `sos-6` | 4.964 s | 2.662 s | 3.604 s | 1.303 s | 2.765× | 3.651× | resolved before construction subtraction |
| `sos-6`, net arithmetic | — | — | 3.502 s | 1.297 s | 2.699× | — | resolved |
| `structural-8` | 1.460 s | 1.459 s | 0.101 s | 0.099 s | 1.020× | 1.074× | noise-limited |

Addition's sorted net arm is smaller than the 228.967 ms combined null
envelope, so its 3.817× point ratio is noise-limited. Cancellation and SOS
retain resolved net point ratios after their matched construction controls
are subtracted.

A point ratio does not by itself pass the 2× gate. For a reference workload
`r`, candidate workload `c`, and interpolated noise envelope `e`, the sweep
reports the conservative interval
`(r - e) / (c + e)` through `(r + e) / (c - e)`. A family passes only when
the lower bound is greater than 2; an unresolved arm remains unresolved even
when its point estimate is large.

At the largest measured rung in each registered family:

| family | case | point ratio | conservative interval | threshold result |
|---|---|---:|---:|---|
| `kernel-sparse-addition` | `addition-32` | 3.817× net | [1.235×, unbounded] | unresolved |
| `kernel-sparse-multiplication` | `multiplication-collide-8` | 1.133× | [0.897×, 1.435×] | failed |
| `kernel-cancellation-identities` | `cancellation-8` | 1.847× net | [1.447×, 2.402×] | unresolved |
| `kernel-structural-collisions` | `structural-8` | 1.020× | [0.663×, 1.572×] | unresolved |
| `kernel-sos-certificates` | `sos-6` | 2.699× net | [1.987×, 3.857×] | unresolved |

No family has a conservative lower bound above 2×. In particular, the SOS
point estimate is large but its 1.987× lower bound does not clear the
threshold. The predeclared two-family gate is therefore not met, and the
single production `ExtTreeMap` representation stands. The sorted proxy
remains comparison evidence rather than a proposed public implementation.

The cheap same-module null has a 4.302 ms IQR and 11.902 ms robust envelope;
the expensive null has a 72.612 ms IQR and 183.574 ms robust envelope. Their
IQR/build ratios are 0.316% and 2.293%, below the 10% invalidation limit.

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

The net workload ratios and their conservative intervals in the Verdicts
table are the decision evidence. Raw fresh-module ratios cannot show the SOS
result faithfully because import/elaboration overhead dominates the
candidate arm. Round-matched import and construction subtraction are
therefore material, not cosmetic. Point estimates are reported for diagnosis,
but only a conservative lower bound can pass the gate.

The native companion ratios are recorded separately in
`reports/hex-mv-poly-performance.md`. They characterize compiled throughput
but do not override the kernel-specific decision.

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
observed a 2.93% frequency spread, no concurrent Lake/Lean processes, no
rejected pair attempts, three rejected quiet-core windows, and no validity
violation.

## Concerns

The Phase-4 artifact has no validity exception. It makes a negative
representation decision under the preregistered rule: no family has a
conservative lower bound greater than 2×, and sparse addition is explicitly
noise-limited after matched construction subtraction. The production library
therefore remains a single `ExtTreeMap` representation.

The unavailable upstream `Mathlib MvSparsePoly` remains an explicit comparator
limitation. The current sorted proof-probe adapter is evidence, not production
API, and the measured result does not justify promoting it.
