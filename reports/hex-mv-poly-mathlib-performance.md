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
canonical sorted-list proxy from
`bench/HexMvPolyMathlib/ProofProbe/Support.lean`, with linear merge addition
and balanced translated-row multiplication.

The companion surface also passes the pinned consumer acceptance described in
`reports/hex-mv-poly-performance.md`: SOS's original verifier helpers and
kernel certificate path compile unchanged, and CompPoly's univariate and
bivariate recursive-view adapters compile after the disclosed toolchain proof
rewrite.

## Verdicts

The release-quality sweep used clean commit
`7acdff89b67d7b4fdfbb2b1b5b77a182097331d3` on `chungus2` (AMD EPYC 9455,
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
  --output reports/bench-results/hex-mv-poly-kernel-7acdff89-chungus2.json
```

The committed export is
`reports/bench-results/hex-mv-poly-kernel-7acdff89-chungus2.json`
(SHA-256
`9f69bd71cde21583c55b689a1243219c341fafe814b36700e9dc4308015f3308`).
It is complete, reports `release_quality: true`, has no validity exceptions,
preflight failures, or exhausted pairs, and records two rejected contaminated
pair attempts before successful retries.

The import-only baseline median is 1.358423 s. Its centred variability has a
0.939 ms IQR and a 1.947 ms robust Tukey envelope. Both substantive workloads
must exceed that envelope before their ratio can be classified. The raw-ratio
cap is `Hex raw / import baseline`: it is the largest raw fresh-build ratio
possible even if the candidate workload itself took zero time.

| case | Hex raw | sorted raw | Hex workload | sorted workload | Hex / sorted workload | raw-ratio cap | ratio status |
|---|---:|---:|---:|---:|---:|---:|---|
| `addition-32` | 2.766 s | 1.659 s | 1.408 s | 0.300 s | 4.697× | 2.036× | resolved |
| `multiplication-sparse-6` | 1.760 s | 2.361 s | 0.401 s | 1.003 s | 0.400× | 1.295× | resolved |
| `multiplication-collide-8` | 2.112 s | 2.058 s | 0.755 s | 0.700 s | 1.079× | 1.555× | resolved |
| `cancellation-4` | 1.959 s | 1.757 s | 0.600 s | 0.398 s | 1.507× | 1.442× | resolved |
| `cancellation-6` | 3.159 s | 2.359 s | 1.802 s | 1.001 s | 1.800× | 2.326× | resolved |
| `sos-3` | 1.960 s | 1.662 s | 0.602 s | 0.304 s | 1.977× | 1.443× | resolved |
| `sos-4` | 2.559 s | 1.856 s | 1.199 s | 0.497 s | 2.411× | 1.884× | resolved |
| `structural-8` | 1.459 s | 1.459 s | 0.100 s | 0.101 s | 0.999× | 1.074× | noise-limited |

The paired raw wall-time deltas (`sorted - Hex`) were:

- `addition-32`: −1203.4, −1105.1, −1108.1, −1103.2, −1105.7, −1202.0 ms.
- `multiplication-sparse-6`: +604.0, +600.1, +599.1, +598.4, +603.0, +613.1 ms.
- `multiplication-collide-8`: −102.4, −11.9, −6.9, −91.5, −14.7, −102.9 ms.
- `cancellation-4`: −202.1, −203.6, −202.3, −199.8, −191.6, −200.4 ms.
- `cancellation-6`: −797.2, −802.8, −807.3, −797.9, −798.5, −706.3 ms.
- `sos-3`: −304.0, −293.4, −302.9, −295.8, −294.2, −299.3 ms.
- `sos-4`: −701.5, −701.1, −701.9, −702.7, −704.2, −699.9 ms.
- `structural-8`: +0.5, +0.1, +2.4, +1.4, −2.5, −0.4 ms.

The cheap null has a 2.087 ms IQR and 4.900 ms robust envelope; the expensive
null has an 11.227 ms IQR and 23.226 ms robust envelope. Their IQR/build ratios
are 0.154% and 0.355%, well below the 10% invalidation limit. Interpolating
these envelopes leaves every substantive delta resolved except
`structural-8`, whose 0.337 ms median delta is inside its 5.926 ms envelope.

At the largest measured rung in each registered family:

| family | case | Hex / sorted workload | threshold result |
|---|---|---:|---|
| `kernel-sparse-addition` | `addition-32` | 4.697× | passes |
| `kernel-sparse-multiplication` | `multiplication-collide-8` | 1.079× | does not pass |
| `kernel-cancellation-identities` | `cancellation-6` | 1.800× | does not pass |
| `kernel-structural-collisions` | `structural-8` | 0.999× | unresolved |
| `kernel-sos-certificates` | `sos-4` | 2.411× | passes |

Exactly two families have resolved greater-than-2× sorted wins. The
predeclared threshold is therefore met: a second kernel-specialized sorted
representation is justified. This does not replace the compiled
`ExtTreeMap` representation, and the benchmark proxy is not promoted as a
public implementation. The follow-up representation belongs behind the
swappable polynomial abstraction recorded in `SPEC/future-work.md`.

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
fresh-module ratios cannot show the addition and SOS result faithfully:
their mathematical caps are only 2.036× and 1.884× because import/elaboration
overhead dominates the candidate arm. Round-matched import subtraction is
therefore material, not cosmetic.

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
observed a 1.45% frequency spread, no concurrent Lake/Lean process, two
rejected pair attempts, four rejected quiet-core windows, and no validity
violation.

## Concerns

The Phase-4 measurement itself has no unresolved validity concern. It made a
positive design decision whose implementation is deliberately follow-up work:
the production library still has one `ExtTreeMap` representation, while the
measured evidence justifies adding an opt-in kernel-specialized sorted form
behind a representation abstraction.

The unavailable upstream `Mathlib MvSparsePoly` remains an explicit comparator
limitation. Before shipping the second representation, its local proxy
algorithms need a supported public type, correspondence proofs, and a repeat
of the SOS kernel-consumer acceptance; the current proof-probe adapter is
evidence, not production API.
