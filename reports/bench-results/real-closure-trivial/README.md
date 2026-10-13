# Rational complete root route comparison

The [protocol](protocol.md) compares `Trivial.Rational.roots` with the existing
`RealAlgebraicPoly.roots` backend on identical rational polynomials. Both arms
construct the complete result and force the same exact consumer: root order,
signs, square identities and multiplicities. The zero polynomial returns `all`;
the nonzero constant returns an empty finite set. Input preparation and
rational coefficient lifting are outside timing.

All 72 arms completed in six trial-major rounds, with adjacent arms alternating
AB/BA. Fresh twelve-arm functional output agrees with the committed fixture
and independent python-flint 0.9.0 / FLINT 3.6.0 checks. Nine rejection tests
cover altered coefficients, roots, ordering, multiplicities and result kinds.

Measured source: `10a175609f9b0f14d3774f1152f91c69590a3803`. Host: `chungus2`;
leased CPU: `52`. [capture.tar.gz](capture.tar.gz) retains every raw export,
command, configured compiler identity, source snapshot, repeat count and host observation.
The compiled executable is omitted; [archive-index.json](archive-index.json)
records its size and SHA-256. Capture reused an existing binary; its digest
identifies the measured bytes. The configured compiler and captured version
do not identify the compiler that produced those existing objects.
No completed observation was discarded or rerun.

## Batch per-call estimates

Each median and range summarizes six completed batches. Ratios use adjacent
arms within the same round. [analysis.json](analysis.json) retains all estimates,
full timing ranges, paired ratios and raw batch points.

| Input | Generic median ms | Canonical median ms | Median paired generic / canonical (range) |
| --- | --- | --- | --- |
| Zero | 0.000047913 | 0.000045098 | 1.062 (1.057–1.067) |
| Constant 5 | 0.000111202 | 0.311237299 | 0.000359 (0.000354–0.000364) |
| `(X² − 2)` | 6.065261 | 2.195145 | 2.769 (2.737–2.819) |
| `(X² − 2)²` | 6.069783 | 2.573039 | 2.363 (2.334–2.378) |
| `(X² − 2)⁴` | 6.083170 | 3.538975 | 1.715 (1.485–1.731) |
| `(X² − 2)⁸` | 6.099443 | 6.301954 | 0.969 (0.962–0.980) |

The generic route was slower in every retained pair for multiplicities 1, 2
and 4, and faster in every pair for multiplicity 8 and the constant. The zero
case mostly measures dispatch and the exact result-kind consumer. These are
descriptive shared-host batch estimates, with recorded concurrent host activity;
no significance test or asymptotic claim is inferred. The constant case includes
common-field coefficient preparation in the canonical backend before its
degree-zero return; zero returns before that preparation. This source-level
control flow explains the large constant/zero difference, without a profiled
cost allocation.

The generic route performs checked isolation and converts its selected
descriptors to canonical real algebraic numbers. Conversion invokes the existing
canonical backend again for each selected root, so these inputs re-enumerate the
same squarefree head twice. The canonical arm uses its
complete backend directly. This is the permitted generic route; the capture
does not introduce or measure a new trivial-base algorithm. The two distinct
roots remain fixed while polynomial degree grows through 2, 4, 8 and 16. This
family therefore does not establish a general winner across squarefree degree,
growing numbers of roots, the rational-root conversion branch, selected
algebraic coefficients or arbitrary towers. This remains partial evidence. Both timings include
the common consumer and cannot be interpreted as exclusive isolation costs.

Other Phase 4 obligations remain in the
[coverage table](../../real-closure-phase4.md#measurement-coverage-and-remaining-work).

## Recompute

Extract `capture.tar.gz` into a fresh directory and run:

```sh
python3 scripts/bench/analyze_real_closure_trivial.py /path/to/extracted \
  --archive-index reports/bench-results/real-closure-trivial/archive-index.json \
  --output /tmp/trivial-analysis.json
```

The analyzer verifies the archive digest, 237 retained files and exact extracted
bytes including metadata, CPU affinity, every retained artifact digest, source
snapshot, all 72
scheduled positions, recorded commands, frozen source/function bindings,
consumer hashes, fixed-call configuration and complete batches.
