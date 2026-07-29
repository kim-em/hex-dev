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
toolchain proof rewrite. The machine-readable record is
`reports/bench-results/hex-mv-poly-consumers-d05d0635.json`.

## Verdicts

The release-quality sweep used clean commit
`45f01eb6435f0666e60247899cea152b16275d3c` on `chungus2` (AMD EPYC 9455,
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
  --output reports/bench-results/hex-mv-poly-kernel-45f01eb6-chungus2.json
```

The committed export is
`reports/bench-results/hex-mv-poly-kernel-45f01eb6-chungus2.json`
(SHA-256
`b1e425c09a79a8c7a6bc92ab3a69ccd0a34f1c7bbd357a01686596ab711c5490`).
It is complete, reports `release_quality: true`, has no validity exceptions,
preflight failures, or exhausted pairs. The shared host was active during the
capture, so the protocol rejected 52 preflight windows and 10 complete
measured pair attempts; all retained pairs have six accepted samples.

The import-only baseline build magnitude is 1.359639 s. Its centred
variability has a 3.702 ms IQR, a 10.946 ms Tukey envelope, and a
20.885 ms conservative envelope after including the maximum observed
absolute delta. The raw-ratio cap is
`Hex raw / import baseline`: it is the largest raw fresh-build ratio possible
even if the candidate workload itself took zero time.

| case | Hex raw | sorted raw | Hex workload | sorted workload | Hex / sorted workload | raw-ratio cap | ratio status |
|---|---:|---:|---:|---:|---:|---:|---|
| `addition-inputs-64` | 3.016 s | 1.861 s | 1.656 s | 0.503 s | 3.290× | 2.222× | construction control |
| `addition-64` | 5.015 s | 2.257 s | 3.657 s | 0.900 s | 4.063× | 3.694× | resolved before construction subtraction |
| `addition-64`, net arithmetic | — | — | 2.038 s | 0.395 s | 5.164× | — | noise-limited |
| `multiplication-sparse-6` | 1.761 s | 2.458 s | 0.403 s | 1.100 s | 0.366× | 1.297× | resolved |
| `multiplication-collide-inputs-12` | 1.458 s | 1.460 s | 0.101 s | 0.101 s | 0.991× | 1.074× | construction control |
| `multiplication-collide-12` | 3.156 s | 3.210 s | 1.799 s | 1.853 s | 0.971× | 2.325× | resolved before construction subtraction |
| `multiplication-collide-12`, net arithmetic | — | — | 1.698 s | 1.750 s | 0.971× | — | resolved |
| `cancellation-4` | 1.960 s | 1.758 s | 0.602 s | 0.401 s | 1.501× | 1.444× | resolved |
| `cancellation-6` | 3.162 s | 2.359 s | 1.805 s | 1.002 s | 1.802× | 2.330× | resolved |
| `cancellation-inputs-10` | 1.458 s | 1.417 s | 0.099 s | 0.057 s | 1.741× | 1.074× | construction control |
| `cancellation-10` | 8.164 s | 4.463 s | 6.801 s | 3.104 s | 2.191× | 6.014× | resolved before construction subtraction |
| `cancellation-10`, net arithmetic | — | — | 6.704 s | 3.046 s | 2.201× | — | resolved |
| `sos-3` | 1.958 s | 1.659 s | 0.602 s | 0.303 s | 1.984× | 1.442× | resolved |
| `sos-4` | 2.557 s | 1.860 s | 1.198 s | 0.501 s | 2.390× | 1.883× | resolved |
| `sos-inputs-8` | 1.460 s | 1.459 s | 0.101 s | 0.097 s | 1.042× | 1.076× | construction control |
| `sos-8` | 9.570 s | 3.873 s | 8.213 s | 2.516 s | 3.264× | 7.050× | resolved before construction subtraction |
| `sos-8`, net arithmetic | — | — | 8.109 s | 2.496 s | 3.249× | — | resolved |
| `structural-inputs-32` | 1.463 s | 1.469 s | 0.103 s | 0.109 s | 0.948× | 1.078× | construction control |
| `structural-32` | 1.861 s | 1.662 s | 0.502 s | 0.303 s | 1.660× | 1.371× | resolved before construction subtraction |
| `structural-32`, net operation | — | — | 0.397 s | 0.192 s | 2.068× | — | resolved |

Addition's sorted net arm is smaller than its 443.251 ms combined null
envelope, so its 5.164× point ratio is noise-limited. The other four terminal
net comparisons are resolved after their matched construction controls are
subtracted.

A point ratio does not by itself pass the 2× gate. For a reference workload
`r`, candidate workload `c`, and interpolated noise envelope `e`, the sweep
reports the conservative interval
`(r - e) / (c + e)` through `(r + e) / (c - e)`. A family passes only when
the lower bound is greater than 2; an unresolved arm remains unresolved even
when its point estimate is large.

At the largest measured rung in each registered family:

| family | case | point ratio | conservative interval | threshold result |
|---|---|---:|---:|---|
| `kernel-sparse-addition` | `addition-64` | 5.164× net | [1.903×, unbounded] | unresolved |
| `kernel-sparse-multiplication` | `multiplication-collide-12` | 0.971× net | [0.896×, 1.052×] | failed |
| `kernel-cancellation-identities` | `cancellation-10` | 2.201× net | [1.377×, 3.898×] | unresolved |
| `kernel-structural-collisions` | `structural-32` | 2.068× net | [1.459×, 3.078×] | unresolved |
| `kernel-sos-certificates` | `sos-8` | 3.249× net | [1.772×, 8.092×] | unresolved |

No family has a conservative lower bound above 2×. Addition comes closest,
but its 1.903× lower bound and noise-limited candidate arm do not clear the
threshold. The predeclared two-family gate is therefore not met, and the
single production `ExtTreeMap` representation stands. The sorted proxy
remains comparison evidence rather than a proposed public implementation.

The baseline, medium, and large same-module nulls respectively have
3.702 ms, 15.290 ms, and 539.040 ms IQRs and 20.885 ms, 37.984 ms, and
1,294.121 ms conservative envelopes. Their IQR/build ratios are 0.272%,
0.483%, and 5.692%, below the 10% invalidation limit. The large null is what
keeps SOS-8 magnitude-comparable while also making its threshold interval
appropriately broad.

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
observed a 2.02% frequency spread. It saw other Lake/Lean activity elsewhere
on the shared host, rejected 52 non-quiet core windows and 10 contaminated
complete pair attempts, retained six accepted samples for every pair, and
reported no validity violation.

## Concerns

The implementation milestone is complete, but four terminal threshold
comparisons remain statistically unresolved: their point estimates are not
evidence that the conservative 2× threshold was crossed. Collision-heavy
multiplication is a resolved failure. Under the preregistered rule, zero
families pass and the production library therefore remains a single
`ExtTreeMap` representation.

The unavailable upstream `Mathlib MvSparsePoly` remains an explicit comparator
limitation. The current sorted proof-probe adapter is evidence, not production
API, and the measured result does not justify promoting it. The terminal
construction-controlled rungs still finish well below the 300-second
per-module budget; future evidence may extend them, but that is a new
performance investigation rather than an unfinished acceptance obligation.
