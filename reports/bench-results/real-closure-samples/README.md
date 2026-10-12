# Matched sector sample results

The [protocol](protocol.md) fixes the original boundary roots, three sampling
methods, exact sign consumer and adjacent alternating comparison schedule.
All 96 arms completed across six trial-major rounds. Fresh native output for
all twelve arms agrees with the committed fixture and the independent pinned
Z3 RCF / python-flint oracle. Nine rejection tests cover wrong signs, inputs,
sector, context, method ordering and dyadic work.

Measured source: `33003db1a06a5bf8d0ee97a9cdad8740999c8330`. Host: `chungus2`; leased CPU: `60`.
The executable digest and configured compiler identity, raw batches, repeat counts, commands,
source snapshots and host observations are retained in [capture.tar.gz](capture.tar.gz).
The 120 MB executable is omitted; [archive-index.json](archive-index.json) retains its digest.
The capture build reused the existing executable; its digest identifies the
measured bytes. The captured compiler override records configuration, and does
not establish which compiler produced that existing executable.
The initial escaped-package-name failure occurred before measurement and is
retained in [preparation-failure.tar.gz](preparation-failure.tar.gz).

## Batch per-call estimates

Each table cell summarizes six completed batch estimates. Ratios use adjacent
arms within the same round. These are shared-host observations; no significance
test or asymptotic bound is inferred.

| Gap exponent k | Pair | Alternative median ms (range) | Infinitesimal median ms (range) | Median paired alternative / infinitesimal |
| --- | --- | --- | --- | --- |
| 0 | midpoint | 0.565086 (0.560143–0.570425) | 0.301041 (0.299471–0.303469) | 1.876 |
| 0 | dyadic | 0.372390 (0.368168–0.373538) | 0.301526 (0.299205–0.303066) | 1.235 |
| 4 | midpoint | 0.688550 (0.682777–0.696498) | 0.301694 (0.298362–0.304508) | 2.281 |
| 4 | dyadic | 1.711087 (1.695898–1.717105) | 0.301549 (0.296299–0.325503) | 5.674 |
| 8 | midpoint | 0.689504 (0.679011–0.715984) | 0.299744 (0.297222–0.302106) | 2.300 |
| 8 | dyadic | 3.042052 (3.003172–3.365318) | 0.301576 (0.299090–0.302849) | 10.115 |
| 12 | midpoint | 0.692612 (0.690811–0.698995) | 0.302866 (0.299796–0.307031) | 2.283 |
| 12 | dyadic | 4.390976 (4.353171–4.883399) | 0.301130 (0.298497–0.303203) | 14.626 |

The infinitesimal arm was faster in every retained pair in this family. It
rebuilds one boundary context, while the midpoint collects two boundary roots
and the bench-local dyadic prototype performs increasingly many calls to the
generic selected-root comparator. Each comparison rebuilds prepared sign queries
and replay; this arm does not reuse a prepared domain. The measured dyadic ratios
apply to this implementation, not to an optimized dyadic sample backend. The cut counts are
independently recovered by exact rational FLINT arithmetic. This observation
does not establish a general winner for arbitrary tower or sample families.

## Exact sizes and search work

| k | Method | Base / algebraic depth | Value bytes | Full context bytes | Dyadic cuts |
| --- | --- | --- | --- | --- | --- |
| 0 | midpoint | 0 / 2 | 41 | 1402 | 0 |
| 0 | dyadic | 0 / 0 | 7 | 9 | 1 |
| 0 | infinitesimal | 1 / 1 | 61 | 1297 | 0 |
| 4 | midpoint | 0 / 2 | 41 | 1416 | 0 |
| 4 | dyadic | 0 / 0 | 9 | 9 | 6 |
| 4 | infinitesimal | 1 / 1 | 61 | 1297 | 0 |
| 8 | midpoint | 0 / 2 | 41 | 1430 | 0 |
| 8 | dyadic | 0 / 0 | 13 | 9 | 10 |
| 8 | infinitesimal | 1 / 1 | 61 | 1297 | 0 |
| 12 | midpoint | 0 / 2 | 41 | 1444 | 0 |
| 12 | dyadic | 0 / 0 | 15 | 9 | 14 |
| 12 | infinitesimal | 1 / 1 | 61 | 1297 | 0 |

Sizes count compact integer-only JSON. Full context bytes include retained
root frames and their evidence; they are separate from the sample value bytes.
An infinitesimal sample is interpreted in its native extension, not offered as
an ordinary-real witness.

The comparison covers rational initial bases and bounded positive quadratic
sectors. Non-Archimedean dyadic gaps, other section/ray families, arbitrary
tower depths, ordinary-real reconstruction and whole-library operation
counters remain outside this capture. Other Phase 4 obligations remain in the
[coverage table](../../real-closure-phase4.md#measurement-coverage-and-remaining-work).

## Recompute

Extract `capture.tar.gz` into a fresh directory and run:

```sh
python3 scripts/bench/analyze_real_closure_samples.py /path/to/extracted \
  --archive-index reports/bench-results/real-closure-samples/archive-index.json \
  --output /tmp/sample-analysis.json
```

The analyzer verifies every retained artifact digest, all 96 scheduled positions,
exact source/function bindings, consumer hashes, complete batches and paired
rounds. [analysis.json](analysis.json) retains every estimate and raw batch.
