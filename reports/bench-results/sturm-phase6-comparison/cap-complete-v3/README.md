# Complete Sturm computational comparison

All 58 timing families pass the pinned 10-percent native regression rule
against the most recent committed benchmark baseline. Four complete balanced
AB/BA blocks contain 464 parent exports and 1,968 measurement points, producing
246 parameter comparisons. All 58 native guards return zero. The largest
median increase is **5.156%**, for `Hex.SturmFrontendBench.runSparseInteger`
at 16,384 (baseline 5,776,127.53125 ns, candidate 6,073,929.0625 ns).
Every comparison is stable or an improvement. No timing family, declared
parameter, failed sample or inconclusive result is omitted.

## Source and protocol

- Baseline: `75fbfa04550ae0f76df074176f44bf0f2533334a`.
- Producer: `8e5b3e40a69117c84bb6f0c19aaad93a26049ab8`.
- Collector tooling: `f80b63bd857d58e0acff89cb3954a81bba56fa9c`, retained at
  `audit/issue-10575-sturm-cap-tooling-v3`.
- Native LeanBench: `8a37daf1074c3bdbd0da479b55538bad4a0022db`;
  CLI: `843844fa601dd56767b1eb22b7ada5b64d5e567a`.
- Host: `chungus2`, CPU 43. Load, affinity, memory and process outputs are
  retained as context; no quiet-core gate or sample rejection is used.

The [cap protocol](../cap-protocol.md) increases the same two frozen arms'
operational per-call timeout to 3,600 whole seconds. All 58 original families,
parameter ladders, inner targets, warmup, signal-floor rules and four adjacent
AB/BA blocks are retained. This is a complete restart under the separately
reviewed protocol, not continuation of a partial ladder or an unchanged retry.
The concrete decision, collector/helper sources, source manifests, commands,
raw stdout/stderr, exports and finalized persistent reservation are archived.
The reserved attempt completed without an integrity failure or inconclusive
rerun. The [original cap failure](../README.md) and earlier preflights remain
separate and unchanged as evidence; the original reservation was not reset.

This result discharges the computational comparison, not a new Phase-4 scaling
model, proof-cost measurement or family/publication acceptance. The
[current-source reconciliation](current-source.json) records the two
comment-only differences in the 62-file native import cone and the original
CLI pin's scope. The [Sturm acceptance](../../../sturm-proof-acceptance.md)
separately assesses proof/API, conformance and documentation criteria.

The original 120-second high-bit deadline remains an operational concern for
future complete comparisons. In this capture, the eight timed
`runRationalHigh` observations at 1,048,576 range from 96.978 to 100.331 seconds,
all below 120 seconds. Across the entire capture, the slowest timed point is
`runPreparedCertificateHigh` at 1,048,576: 104.708 seconds in
`3-39-baseline.json`, leaving only about 15.3 seconds before that original
limit. Timed samples alone do not prove that an entire
invocation, including untimed setup, fits the original deadline; the earlier
cap failure remains evidence. Future complete comparisons must account for
that failure when choosing a matched operational timeout. This result does
not change the registrations or establish that every future comparison will
fail under their defaults.

## Retention and replay

[manifest.json](manifest.json) binds all 1,579 archived files by compressed and
original SHA-256, and original byte length. Deterministic gzip preserves every
capture file plus the finalized reservation. [archive-replay.json](archive-replay.json)
records the replay driver SHA-256, host, verification of every binding and exact
reproduction of all 58 report JSON values using the original hash-bound native guard. That replay collects
no new measurements. The original executable retention is described in
[../binary-retention.json](../binary-retention.json); binaries are host-local,
not included in this portable data archive.

The committed [replay driver](replay.py) verifies all archive bindings and,
when given the original guard, extracts into a temporary directory and
reproduces all 58 reports. Its exact invocation is:

```sh
python3 reports/bench-results/sturm-phase6-comparison/cap-complete-v3/replay.py \
  --guard /home/kim/.local/state/hex/issue-10575-sturm-phase6/compare-exports
```

Omit `--guard` to verify archive bindings alone on another host. The driver
refuses a changed archive or guard digest and mismatched function/guard labels.
[replay-controls.json](replay-controls.json) retains the refusal-control setup
and stderr alongside the exact driver hash.
It does not rebuild or execute a benchmark workload.

To extract and verify the data from the repository root:

```sh
python3 - <<'PYVERIFY'
import gzip, hashlib, json
from pathlib import Path
root = Path('reports/bench-results/sturm-phase6-comparison/cap-complete-v3')
out = Path('/tmp/sturm-complete-v3')
out.mkdir(exist_ok=True)
manifest = json.loads((root / 'manifest.json').read_text())
for name, record in manifest['files'].items():
    packed = (root / record['archive']).read_bytes()
    raw = gzip.decompress(packed)
    assert hashlib.sha256(packed).hexdigest() == record['archive_sha256']
    assert len(raw) == record['bytes']
    assert hashlib.sha256(raw).hexdigest() == record['sha256']
    (out / name).write_bytes(raw)
print(len(manifest['files']), 'verified files')
PYVERIFY
```

The native guard is the historical `hexsturm_compare_exports` built at the
producer revision, with SHA-256
`9fb1fa9c1b2c24b2a2bfa91a7f4d4575ad09d191903130545723b2ff0d1ce12f`.
To replay an individual family `i`, pass a fresh output path followed by
`0-i-baseline.json` through `3-i-baseline.json`, then `0-i-candidate.json`
through `3-i-candidate.json`. Its exact invocation and outputs are retained
in `context.json`. Use `lake build hexsturm_compare_exports` in the preserved
producer checkout if rebuilding; a rebuild is not claimed byte-identical to
the retained guard. Do not rerun the measurement collector: the successful
attempt's reservation is consumed.

## Family results

Changes below are candidate versus baseline medians under the pinned native
rule, across each family's complete declared parameters. Host-specific
observations do not predict absolute performance on other machines.

| Family | Parameters | Smallest change | Largest change |
| --- | ---: | ---: | ---: |
| `Hex.SturmBench.runChain` | 4 | -1.316% | -0.726% |
| `Hex.SturmBench.runClearing` | 4 | -0.775% | +0.170% |
| `Hex.SturmBench.runClearingWide` | 4 | -0.595% | +0.536% |
| `Hex.SturmBench.runDomain` | 4 | -3.028% | +0.997% |
| `Hex.SturmBench.runEndpoints` | 4 | -2.805% | +0.199% |
| `Hex.SturmBench.runInitial` | 4 | -2.815% | +2.684% |
| `Hex.SturmBench.runInitialHigh` | 4 | -0.328% | +4.091% |
| `Hex.SturmBench.runInitialWide` | 4 | -0.320% | +1.096% |
| `Hex.SturmBench.runInteger` | 4 | -1.203% | +0.581% |
| `Hex.SturmBench.runIntegerHigh` | 4 | -0.317% | +3.415% |
| `Hex.SturmBench.runRational` | 4 | -1.755% | -0.564% |
| `Hex.SturmBench.runRationalHigh` | 4 | -0.610% | +1.032% |
| `Hex.SturmBench.runRationalValue` | 4 | -1.191% | +0.053% |
| `Hex.SturmBench.runReducedRational` | 4 | -0.199% | +0.180% |
| `Hex.SturmBench.runReplay` | 4 | -1.466% | +2.064% |
| `Hex.SturmBench.runReplayHigh` | 4 | -0.936% | +0.287% |
| `Hex.SturmFrontendBench.runCachedReplay` | 4 | -1.476% | +1.514% |
| `Hex.SturmFrontendBench.runCachedReplayBits` | 5 | -0.365% | +0.666% |
| `Hex.SturmFrontendBench.runCertificate` | 4 | -3.038% | +0.416% |
| `Hex.SturmFrontendBench.runCertificateBits` | 5 | -0.406% | +0.115% |
| `Hex.SturmFrontendBench.runClear` | 4 | -1.716% | +0.205% |
| `Hex.SturmFrontendBench.runClearBits` | 5 | -0.381% | +0.049% |
| `Hex.SturmFrontendBench.runCoefficientBits` | 5 | -0.115% | +0.707% |
| `Hex.SturmFrontendBench.runCount` | 4 | -3.944% | +1.322% |
| `Hex.SturmFrontendBench.runCountBits` | 5 | -0.725% | +0.580% |
| `Hex.SturmFrontendBench.runCountCertificate` | 4 | -0.349% | +2.288% |
| `Hex.SturmFrontendBench.runCountCertificateBits` | 5 | -0.442% | +0.077% |
| `Hex.SturmFrontendBench.runEmbed` | 4 | -1.349% | +0.350% |
| `Hex.SturmFrontendBench.runEmbedSparse` | 5 | -0.710% | +0.831% |
| `Hex.SturmFrontendBench.runEndpointBits` | 5 | -0.015% | +0.578% |
| `Hex.SturmFrontendBench.runFieldReplay` | 4 | -0.918% | -0.176% |
| `Hex.SturmFrontendBench.runFieldReplayBits` | 5 | -0.287% | -0.016% |
| `Hex.SturmFrontendBench.runFractionalBits` | 5 | -0.244% | +1.046% |
| `Hex.SturmFrontendBench.runInfinite` | 4 | -2.571% | +0.505% |
| `Hex.SturmFrontendBench.runInfiniteBits` | 5 | -0.453% | +0.254% |
| `Hex.SturmFrontendBench.runPrepared` | 4 | -1.256% | +1.095% |
| `Hex.SturmFrontendBench.runPreparedBits` | 5 | -0.479% | -0.019% |
| `Hex.SturmFrontendBench.runPreparedCertificate` | 4 | -2.472% | +0.084% |
| `Hex.SturmFrontendBench.runPreparedCertificateBits` | 5 | -0.405% | +0.002% |
| `Hex.SturmFrontendBench.runPreparedCertificateHigh` | 4 | -2.521% | -0.325% |
| `Hex.SturmFrontendBench.runPreparedCount` | 4 | -2.397% | +2.028% |
| `Hex.SturmFrontendBench.runPreparedCountBits` | 5 | -0.169% | +0.098% |
| `Hex.SturmFrontendBench.runPreparedHigh` | 4 | -0.943% | +0.142% |
| `Hex.SturmFrontendBench.runRetarget` | 4 | +0.797% | +2.319% |
| `Hex.SturmFrontendBench.runRetargetWide` | 4 | -0.092% | +0.181% |
| `Hex.SturmFrontendBench.runSparseCachedReplay` | 4 | -3.416% | -2.654% |
| `Hex.SturmFrontendBench.runSparseCertificate` | 4 | -4.452% | -3.329% |
| `Hex.SturmFrontendBench.runSparseClear` | 4 | -1.191% | +1.933% |
| `Hex.SturmFrontendBench.runSparseCount` | 4 | -3.630% | -2.268% |
| `Hex.SturmFrontendBench.runSparseCountCertificate` | 4 | -3.788% | -2.483% |
| `Hex.SturmFrontendBench.runSparseDomain` | 4 | -4.424% | -1.939% |
| `Hex.SturmFrontendBench.runSparseEmbed` | 4 | -3.662% | -0.181% |
| `Hex.SturmFrontendBench.runSparseInteger` | 4 | +0.130% | +5.156% |
| `Hex.SturmFrontendBench.runSparsePrepared` | 4 | -3.875% | -2.583% |
| `Hex.SturmFrontendBench.runSparsePreparedCertificate` | 4 | -4.683% | -2.108% |
| `Hex.SturmFrontendBench.runSparsePreparedCount` | 4 | -4.813% | -1.930% |
| `Hex.SturmFrontendBench.runSparseQuery` | 4 | -3.512% | -2.006% |
| `Hex.SturmFrontendBench.runSparseReplay` | 4 | -3.245% | -1.937% |
