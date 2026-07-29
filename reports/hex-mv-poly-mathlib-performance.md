# HexMvPolyMathlib Performance Report

## Bench Targets

`HexMvPolyMathlib` is a proof-only companion. Its Phase-4 evidence lives under
`bench/HexMvPolyMathlib/ProofProbe/` and is built as fresh downstream modules
with:

```sh
lake build +<module>:olean
```

The `kernel-cancellation-identities` family covers production `Int` and `Rat`
polynomials at two sizes. The `kernel-sos-certificates` family covers
representative sum-of-squares certificate identities at two sizes. A
supplemental `structural-collisions` probe checks the rename/substitution
shape. Each measured theorem uses `decide +kernel`; every emitted proof was
audited with `#print axioms`.

The paired sweep is driven by
`scripts/bench/hex_mv_poly_kernel_sweep.py`. Its reference modules use the
production Hex ExtTreeMap representation. Candidate modules use the canonical
sorted-list proxy from
`bench/HexMvPolyMathlib/ProofProbe/Support.lean`.

The companion surface also passed the consumer acceptance described in
`reports/hex-mv-poly-performance.md`: the `sos` verifier modules and
CompPoly's two recursive-view equivalence consumers compile against the public
Hex API.

## Verdicts

The release-quality sweep used clean commit
`3dcbf9e9c0150b8937b98b68a79579823c5fc72a` on `chungus2` (AMD EPYC 9455,
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
  --output /tmp/hex-mv-poly-kernel-3dcbf9e9-chungus2.json
```

The committed export is
`reports/bench-results/hex-mv-poly-kernel-3dcbf9e9-chungus2.json`
(SHA-256
`c21c95df516718397a8216d9ff04fba4669ade757536d183f81e36afd726b2d2`).
It is complete, has no validity exceptions or exhausted pairs, and records two
rejected contaminated pair attempts before successful retries.

| case | family | Hex median | sorted median | sorted / Hex | paired median delta | resolution |
|---|---|---:|---:|---:|---:|---|
| `cancellation-4` | `kernel-cancellation-identities` | 1.951 s | 1.739 s | 0.892× | −207.9 ms | resolved |
| `cancellation-6` | `kernel-cancellation-identities` | 3.050 s | 3.958 s | 1.298× | +900.8 ms | resolved |
| `sos-3` | `kernel-sos-certificates` | 1.739 s | 1.645 s | 0.946× | −97.8 ms | below null envelope |
| `sos-4` | `kernel-sos-certificates` | 2.242 s | 2.138 s | 0.954× | −98.8 ms | resolved |
| `structural-8` | supplemental structural probe | 1.442 s | 1.356 s | 0.940× | −97.8 ms | resolved |
| `fresh-build-null` | fresh-build noise | 1.302 s | 1.337 s | 1.027× | +5.1 ms | null control |
| `cancellation-6-null` | fresh-build noise | 3.051 s | 3.038 s | 0.996× | −1.0 ms | null control |

All six paired deltas were:

- `cancellation-4`: −199.6, −184.4, −217.5, −199.1, −235.5, −216.1 ms.
- `cancellation-6`: +900.7, +901.0, +896.7, +996.9, +885.1, +907.9 ms.
- `sos-3`: −100.3, −85.8, −11.1, −102.8, −102.1, −95.2 ms.
- `sos-4`: −97.6, −90.3, −135.6, −103.5, −99.9, −96.0 ms.
- `structural-8`: −100.0, −82.5, −104.7, −83.6, −128.0, −95.6 ms.

The null-control envelopes classify `sos-3` as unresolved; no direction is
claimed for it. The sorted proxy is about 11% faster at `cancellation-4`,
about 30% slower at the larger `cancellation-6` case, 5% faster at `sos-4`,
and 6% faster on the supplemental structural case. It never approaches the
predeclared requirement of a greater-than-2× win on two families. The
decision is therefore to retain a single ExtTreeMap representation.

Every measured reference and candidate theorem reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `axiom`, or `native_decide` is used by the proof probes.

## Comparator Ratios

The named informational comparator is **Mathlib MvSparsePoly**. That
implementation is absent from the pinned Mathlib revision because its
upstream PR series has not landed. The candidate measured above is therefore
a canonical sorted-list proxy implementing the specified linear merge and
balanced translated-row multiplication shape, not the upstream code.

The relevant proof-build ratios are the `sorted / Hex` column in the Verdicts
table. At the largest measured case in each registered family:

- `kernel-cancellation-identities`: 1.298×, so the sorted proxy is slower.
- `kernel-sos-certificates`: 0.954×, only a 1.05× sorted-proxy speedup.

Neither family clears 2×, so zero families satisfy the two-family threshold.
The native companion ratios are recorded separately in
`reports/hex-mv-poly-performance.md`; they do not override the kernel decision.

## Profile

Sampling profiles are not applicable. `HexMvPolyMathlib` has no compiled
LeanBench timed region: its two registered input families are downstream
fresh-module elaboration and kernel-checking probes. Per
`SPEC/profiling.md`, the replacement evidence is the raw rotated paired-build
record, compiler artifacts, proof axioms, null controls, CPU-accounting
record, and source hashes in the committed kernel export.

The export records all required provenance, including the clean commit,
toolchain and dependency checkouts, CPU topology and affinity, per-pair build
order, wall time, peak RSS, scheduler/frequency observations, retry history,
module artifact sizes, and source SHA-256 values. Its validity block reports
`release_quality: true` and no violations.

## Concerns

No unresolved Phase-4 concern remains.

The unavailable upstream `Mathlib MvSparsePoly` is an explicit comparator
limitation. The proxy is sufficient for the SPEC's representation decision
because it implements the intended efficient sorted traversal shape and still
misses the predeclared threshold by a wide margin; the report makes no claim
about the precise constant factors of code that has not landed.
