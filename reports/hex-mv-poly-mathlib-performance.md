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
`reports/bench-results/hex-mv-poly-consumers-b9ce25d6.json`.

## Verdicts

The release-quality sweep used clean commit
`91adf91b04cd9aa676e7bb08fed176f2038fd0a2` on `chungus2` (AMD EPYC 9455,
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
  --output reports/bench-results/hex-mv-poly-kernel-91adf91b-chungus2.json
```

The committed export is
`reports/bench-results/hex-mv-poly-kernel-91adf91b-chungus2.json`
(SHA-256
`13882174fe64728fb90bc43c60e32585ffa00e0298b7118fc404f45f3f145c11`).
It is complete, reports `release_quality: true`, has no validity exceptions,
preflight failures, or exhausted pairs. The shared host was active during the
capture, so the protocol rejected 68 preflight windows and 6 complete
measured pair attempts; all retained pairs have six accepted samples.

The import-only baseline build magnitude is 1.522454 s. Its centred
variability has an 84.975 ms IQR, a 215.255 ms Tukey envelope, and a
796.139 ms conservative envelope after including the maximum observed
absolute delta. The raw-ratio cap is
`Hex raw / import baseline`: it is the largest raw fresh-build ratio possible
even if the candidate workload itself took zero time.

| case | Hex raw | sorted raw | Hex workload | sorted workload | Hex / sorted workload | raw-ratio cap | ratio status |
|---|---:|---:|---:|---:|---:|---:|---|
| `addition-inputs-64` | 3.661 s | 2.258 s | 2.205 s | 0.662 s | 3.331× | 2.420× | construction control |
| `addition-64` | 7.007 s | 2.853 s | 5.306 s | 1.263 s | 4.201× | 4.632× | resolved before construction subtraction |
| `addition-64`, net arithmetic | — | — | 3.104 s | 0.595 s | 5.216× | — | noise-limited |
| `multiplication-sparse-6` | 2.307 s | 3.009 s | 0.566 s | 1.358 s | 0.417× | 1.525× | resolved |
| `multiplication-collide-inputs-12` | 1.632 s | 1.609 s | 0.059 s | 0.126 s | 0.470× | 1.079× | construction control |
| `multiplication-collide-12` | 4.255 s | 4.522 s | 2.676 s | 2.912 s | 0.919× | 2.813× | unresolved before construction subtraction |
| `multiplication-collide-12`, net arithmetic | — | — | 2.514 s | 2.702 s | 0.930× | — | resolved |
| `cancellation-4` | 2.459 s | 2.153 s | 0.765 s | 0.505 s | 1.513× | 1.625× | unresolved |
| `cancellation-6` | 4.368 s | 2.908 s | 2.664 s | 1.393 s | 1.912× | 2.887× | resolved |
| `cancellation-inputs-10` | 1.756 s | 1.717 s | 0.101 s | 0.036 s | 2.803× | 1.161× | construction control |
| `cancellation-10` | 10.862 s | 5.512 s | 9.350 s | 3.815 s | 2.451× | 7.180× | resolved before construction subtraction |
| `cancellation-10`, net arithmetic | — | — | 8.999 s | 3.782 s | 2.379× | — | resolved |
| `sos-3` | 2.471 s | 2.002 s | 0.818 s | 0.412 s | 1.984× | 1.633× | unresolved |
| `sos-4` | 3.514 s | 2.354 s | 1.916 s | 0.701 s | 2.734× | 2.323× | resolved |
| `sos-inputs-8` | 1.777 s | 1.555 s | 0.134 s | 0.078 s | 1.729× | 1.175× | construction control |
| `sos-8` | 11.726 s | 5.078 s | 10.274 s | 3.601 s | 2.853× | 7.750× | resolved before construction subtraction |
| `sos-8`, net arithmetic | — | — | 9.906 s | 3.428 s | 2.890× | — | resolved |
| `structural-inputs-32` | 1.457 s | 1.457 s | 0.103 s | 0.029 s | 3.549× | 0.963× | construction control |
| `structural-32` | 1.911 s | 1.705 s | 0.501 s | 0.302 s | 1.658× | 1.263× | unresolved before construction subtraction |
| `structural-32`, net operation | — | — | 0.450 s | 0.284 s | 1.586× | — | noise-limited |

Addition's net arms are smaller than its 1.022 s combined null envelope, so
its 5.216× point ratio is noise-limited. Structural collisions are likewise
noise-limited after construction subtraction. The multiplication,
cancellation, and SOS terminal net comparisons are resolved as workload
comparisons, but their threshold intervals remain conservative.

A point ratio does not by itself pass the 2× gate. For a reference workload
`r`, candidate workload `c`, and interpolated noise envelope `e`, the sweep
reports the conservative interval
`(r - e) / (c + e)` through `(r + e) / (c - e)`. A family passes only when
the lower bound is greater than 2; an unresolved arm remains unresolved even
when its point estimate is large.

At the largest measured rung in each registered family:

| family | case | point ratio | conservative interval | threshold result |
|---|---|---:|---:|---|
| `kernel-sparse-addition` | `addition-64` | 5.216× net | [1.287×, unbounded] | unresolved |
| `kernel-sparse-multiplication` | `multiplication-collide-12` | 0.930× net | [0.359×, 2.329×] | unresolved |
| `kernel-cancellation-identities` | `cancellation-10` | 2.379× net | [1.265×, 5.650×] | unresolved |
| `kernel-structural-collisions` | `structural-32` | 1.586× net | not bounded; noise-limited | unresolved |
| `kernel-sos-certificates` | `sos-8` | 2.890× net | [1.477×, 8.061×] | unresolved |

No family has a conservative lower bound above 2×. SOS comes closest, but
its 1.477× lower bound does not clear the threshold; addition and structural
collisions are noise-limited. The predeclared two-family gate is therefore
not met, and the single production `ExtTreeMap` representation stands. The
sorted proxy remains comparison evidence rather than a proposed public
implementation.

The final v5 rule was fixed before this capture, but it evolved after a
superseded clean v4 capture at `77b76dd3`. That earlier run put SOS-6 at a
2.699× point ratio with interval [1.987×, 3.857×], a near miss. The null
envelope was subsequently floored by the maximum observed absolute null
delta because a Tukey fence over six samples does not bound the observed
tail. The larger SOS-8 arm then exceeded the permitted 2× magnitude distance
from the medium null, so a third SOS-scale same-module control was registered
before the v5 capture. Both changes make the decision rule more conservative.
Consequently the evidence supports “a pass was not demonstrated”; it does
not support the stronger claim that the sorted form is slower.

The baseline, medium, and large same-module nulls respectively have
84.975 ms, 115.462 ms, and 377.683 ms IQRs and 796.139 ms, 299.155 ms, and
1,199.284 ms conservative envelopes. Their IQR/build ratios are 5.581%,
2.886%, and 3.252%, below the 10% invalidation limit. The large null is what
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
observed a 2.20% frequency spread. It saw other Lake/Lean activity elsewhere
on the shared host, rejected 68 non-quiet core windows and 6 contaminated
complete pair attempts, retained six accepted samples for every pair, and
reported no validity violation.

## Concerns

[Issue #9810](https://github.com/kim-em/hex-dev/issues/9810) tracks the
unresolved proof-track gate described below.

The implementation milestone is complete, but all five terminal threshold
comparisons remain statistically unresolved: their point estimates are not
evidence that the conservative 2× threshold was crossed. Under the
preregistered rule, zero families pass and the production library therefore
remains a single `ExtTreeMap` representation.

The unavailable upstream `Mathlib MvSparsePoly` remains an explicit comparator
limitation. The current sorted proof-probe adapter is evidence, not production
API, and the measured result does not justify promoting it. The terminal
construction-controlled rungs are the largest registered rungs, but they
finish well below the 300-second per-module budget and therefore are not the
largest sizes that fit that budget. This capture does not exercise the
strongest clause of the positive gate and cannot justify a second
representation. Under the standing rule that anything short of two
conservative passes leaves the single representation in place, the default
remains `ExtTreeMap`. A future positive decision needs preregistered larger
rungs, more samples, and preferably a quiescent host.
