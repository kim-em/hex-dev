# SignDet computational comparison

The required Phase-6 comparison is **incomplete**. The primary campaign stopped
at its first source pair because the candidate runner returned exit 2: all seven
successful measurements were below its signal floor. The independent interacting
campaign completed all four balanced blocks and passed both native comparisons.
Neither result establishes acceptance of the complete computational library.

## Inputs and scope

The candidate is `560daa57dc04d54e59faaaf60327733194bfbc92`, retained by
`audit/issue-10575-sign-det-integrated-candidate-v1`. It combines the reviewed
declaration/API changes, fixed-result checker, five expected-hash controls and
collector. All those changes are merged through
`8572e4a1e5bc03c51438decb8ea796cfe118abad`. The primary and interacting native
import closures have respectively 188 and 175 monorepo files; every one is
byte-identical on that main commit. The remaining source differences concern
tactic/proof controls and documentation. Dependency pins and native build
settings are unchanged. The retained
[source reconciliation](integrated-main-native-reconciliation-v1.json) lists
the exact paths; the Lake changes add proof/conformance modules and targets.

The baselines are fresh builds of unmodified committed sources:

| Profile | Baseline source | Candidate executable SHA-256 |
| --- | --- | --- |
| Primary | `61153ea57efbef51a909cead7d0cd4e6be679541` | `b5fa5cfed9ad0b046e1205512ba5e2af2f2d21bd29c840556d2fc8859af359b2` |
| Interacting | `bfa40a88c88b332c4f97f071f054a3814b4724d4` | `8adf0a849291f9cfcf8eee8f31bbeef9eb1a2111560fd06761a9b32581dad3a9` |

The reconstructed binaries differ from the original retained binaries. Their
complete source/pin inventories describe these fresh builds; they do not
reconstruct unrecorded original inputs or original timings. Both campaigns use
the pinned LeanBench comparison and its ten-percent rule, with automatically
leased CPUs on the shared host. Every completed observation is retained.

The primary selection contains all 25 parameterized and six fixed timing
workloads; three tiny reference solves are correctness controls only. The
interacting selection contains both fixed workloads. Four trial-major adjacent
AB/BA/AB/BA blocks were specified, with original ladders, repeats, targets,
floors and deadlines. Both correctness/source preflights passed before timing.

## Primary stopped attempt

[`initial-capture`](initial-capture/manifest.json) retains the entire output
directory, including the decision, source inventories, native verification,
both first-pair exports, raw stdout/stderr and terminal context. Only the first
block of `Hex.SignDetBench.Height.runCheck` was measured. Each arm completed
all seven parameters, 8192 through 524288, and the answer hashes match.

The candidate's measured spawn floor was 113.739337 ms. Its declared multiplier
of ten therefore required about 1.137 seconds per measurement. All seven
measurements took between 0.552 and 0.959 seconds and were marked below floor.
The pinned runner exported them and returned 2, documenting that it had zero
verdict-eligible rows. This is insufficient timing resolution, with no observed
arithmetic or hash failure. It is not a performance pass or a regression finding.

The collector treated every nonzero runner exit as fatal. Consequently the
campaign's terminal status is `failed`; it is not a completed inconclusive
campaign and is **not eligible for the existing unchanged-rerun allowance**.
Its consumed reservation, original decision and captures remain untouched.
No primary retry or change to timing thresholds has been made.

The collector now recognizes this specific complete below-floor export and
retains it for the existing native checker. Failed/unhashed/truncated exports
and other nonzero exits still stop collection. The checker still requires every
declared parameter and all four eligible source trials. Retaining below-floor
rows cannot make this attempted comparison pass. The correction supplies no
permission to reset an already consumed attempt.

## Interacting result

[`interacting-complete-v1`](interacting-complete-v1/manifest.json) retains all
16 parent exports and raw streams, both native checker reports and terminal
context. This was its first attempt, executed after the primary process exited;
it does not retry the primary selection.

| Workload | Baseline median ns/call | Candidate median ns/call | Change | Native result |
| --- | ---: | ---: | ---: | --- |
| `depthOne` | 5,798,810 | 5,707,137 | −1.580893% | Pass |
| `depthTwo` | 27,981,454 | 26,128,237 | −6.623019% | Pass |

The native checker computes the integer per-call, upper-middle pooled median
from the original fixed repeats. Both reports contain zero regressions. The
final source, tool, helper, executable and checker integrity checks pass.
These are observations on this host, without a general speedup claim.

## Archive checks

Each manifest binds both compressed and original bytes. From the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
import gzip, hashlib, json
root = Path('reports/bench-results/sign-det-phase6-comparison')
for directory in ('initial-capture', 'interacting-complete-v1'):
    archive = root / directory
    manifest = json.loads((archive / 'manifest.json').read_text())
    for item in manifest['files']:
        encoded = (archive / item['path']).read_bytes()
        assert hashlib.sha256(encoded).hexdigest() == item['gzip_sha256']
        raw = gzip.decompress(encoded)
        assert len(raw) == item['raw_bytes']
        assert hashlib.sha256(raw).hexdigest() == item['raw_sha256']
    print(directory, len(manifest['files']), 'bindings pass')
PY
python3 scripts/bench/test_sturm_regression.py
```

The actual stopped export is a regression-test fixture for exit-2 handling.
The tests also refuse failed, truncated, malformed, unhashed and wrong-subject
exports and exercise completion of all simulated blocks to an inconclusive
checker result. They collect no benchmark measurements.

The unresolved requirement is a complete primary computational comparison with
adequate timing resolution under an explicitly agreed protocol. No library
phase or publication eligibility is advanced by these results.
