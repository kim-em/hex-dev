# SignDet computational comparison

The complete primary Phase-6 comparison reports **two regressions**. Its matched
resolution campaign completed all 31 workloads and four balanced blocks; the
native checker passes 29 workloads and flags direct joint checking at size 127
and reduced joint production at size 255. The earlier stopped below-floor
attempt remains retained. The independent interacting campaign passed both
comparisons. These results do not establish core Phase-6 acceptance.

## Inputs and scope

The candidate is `560daa57dc04d54e59faaaf60327733194bfbc92`, retained by
`audit/issue-10575-sign-det-integrated-candidate-v1`. It combines the reviewed
declaration/API changes, fixed-result checker, five expected-hash controls and
collector. All those changes are merged through
`8572e4a1e5bc03c51438decb8ea796cfe118abad`. The primary and interacting native
import closures have respectively 188 and 175 monorepo files; every one is
byte-identical on that main commit. The remaining source differences include original-input algebraic adapter
modules, companion proof helpers, their conformance/CI controls and documentation. Dependency pins and native build
settings are unchanged. The retained
[source reconciliation](integrated-main-native-reconciliation-v1.json) lists
all changed paths; each archived candidate-source inventory supplies the exact
native closure paths and resolver hash. The Lake changes add algebraic adapter
modules and proof/conformance targets.

The baselines are fresh builds of unmodified committed sources:

| Profile | Baseline source | Candidate executable SHA-256 |
| --- | --- | --- |
| Primary | `61153ea57efbef51a909cead7d0cd4e6be679541` | `b5fa5cfed9ad0b046e1205512ba5e2af2f2d21bd29c840556d2fc8859af359b2` |
| Interacting | `bfa40a88c88b332c4f97f071f054a3814b4724d4` | `8adf0a849291f9cfcf8eee8f31bbeef9eb1a2111560fd06761a9b32581dad3a9` |

The reconstructed binaries differ from the original retained binaries. Their
complete source/pin inventories describe these fresh builds; they do not
reconstruct unrecorded original inputs or original timings. All three campaigns use
the pinned LeanBench comparison and its ten-percent rule, with automatically
leased CPUs on the shared host. Every completed observation is retained.

The primary selection contains all 25 parameterized and six fixed timing
workloads; three tiny reference solves are correctness controls only. The
interacting selection contains both fixed workloads. Four trial-major adjacent
AB/BA/AB/BA blocks were specified. The original primary and interacting
campaigns use their original ladders, repeats, targets, floors and deadlines.
The resolution campaign preserves those settings except for its four matched
inner-work targets, as detailed below. The archived in-run native verifications
pass before timing. Separate source
preflights also passed; their output directories remain local and are not part
of this archive.

## Primary stopped attempt

[`initial-capture`](initial-capture/manifest.json) retains the entire output
directory, including the decision, source inventories, native verification,
both first-pair exports, raw stdout/stderr and terminal context. Only the first
block of `Hex.SignDetBench.Height.runCheck` was measured. Each arm completed
all seven parameters, 8192 through 524288, and the answer hashes match.

The baseline measured a spawn floor of 57.392388 ms, with six of seven rows
eligible; its 16384 row was below floor. The candidate's measured spawn floor
was 113.739337 ms. Its declared multiplier
of ten therefore required about 1.137 seconds per measurement. All seven
measurements took between 0.552 and 0.959 seconds and were marked below floor.
The per-call times in the two arms differ by less than 0.6%. LeanBench measures
the spawn floor with one child launch per export, so the two floor probes
changed eligibility despite similar workload timings. Both arms retain the
same one-second inner-work target and multiplier; the baseline's missing row
alone would also prevent a complete native comparison pass. No causal claim
about host activity or a workload regression follows from these observations.

The pinned runner exported the candidate rows and returned 2, documenting that it had zero
verdict-eligible rows. This is insufficient timing resolution, with no observed
arithmetic or hash failure. It is not a performance pass or a regression finding.

The collector treated every nonzero runner exit as fatal. Consequently the
campaign's terminal status is `failed`; it is not a completed inconclusive
campaign and is **not eligible for the existing unchanged-rerun allowance**.
Its consumed reservation, original decision and captures remain untouched.
That attempt was not restarted and its reservation was not reset.

The collector now recognizes this specific complete below-floor export and
retains it for the existing native checker. Failed/unhashed/truncated exports
and other nonzero exits still stop collection. The checker still requires every
declared parameter and all four eligible source trials. Retaining below-floor
rows cannot make this attempted comparison pass. The correction supplies no
permission to reset an already consumed attempt. It applies to future bound
collector sources, not to the immutable candidate used in this capture.

The [matched resolution protocol](resolution-protocol.md) specifies one separately
authenticated increase of the inner-work target for both unchanged source arms.
Its [proposal](resolution-proposal.json) binds this original failure and both
exports. The completed campaign below uses that separate resolution reservation;
it is not an unchanged retry of the stopped attempt.

## Complete primary resolution result

[`resolution-complete-v1`](resolution-complete-v1/manifest.json) retains all
849 capture files and the consumed resolution reservation, with compressed and
original-byte bindings. The collector source is
`199ee1a9179aeee0506551b5a365dbe138278f0b`, retained by
`audit/issue-10575-sign-det-resolution-input-v1`. The source arms and checker
are unchanged from the original primary campaign. Only the four named
floor-filtered workloads use the matched 2.25-second targets specified by the
protocol; all other workload settings remain unchanged. The archived decision's
generic schedule wording says original inner targets are unchanged; its explicit
`resolution_protocol` supplies these four overrides. The immutable decision is
retained as collected.

The [collection-precondition record](collector-precondition.json) binds the
required collector PR [#10945](https://github.com/kim-em/hex-dev/pull/10945):
its exact-head CI completed successfully on October 15 at 20:05:58 UTC, and
its merge followed at 20:08:01 UTC. The first timed export is dated October 16
at 02:09:33 UTC. All 188 recorded monorepo native inputs match that merge.
This is distinct from the resolution collector/protocol PR
[#10959](https://github.com/kim-em/hex-dev/pull/10959), which merged at
04:08:08 UTC after collection started. Its four executed tool-source hashes
match tooling freeze `199ee1a9179aeee0506551b5a365dbe138278f0b`; its exact-head
CI completed at 03:49:23 UTC, also after collection started. Thus the executed
resolution changes had not completed CI when timing began. The bound decision
names #10945, not #10959, as its before-collection merge precondition.

The run completes 248 source exports: 31 workloads × four blocks × two arms,
in adjacent AB/BA/AB/BA order on automatically leased CPU 23. Both native
preflights cover the 31 timed workloads and three correctness-only references.
All timed rows succeed with matching answer hashes. Final candidate-source,
helper, collector and checker integrity checks pass; both executable hashes are
unchanged. The collector does not recheck baseline source files at the end. The terminal outcome
is `regression`, not failed collection or insufficient timing resolution.

| Workload | Parameter | Baseline median ns/call | Candidate median ns/call | Change | Native result |
| --- | ---: | ---: | ---: | ---: | --- |
| `Joint.runCheckDirect` | 127 | 53,490,330,879.5 | 66,908,931,470 | +25.086030% | Regression |
| `Joint.runReduced` | 255 | 794,628,001,023.5 | 1,101,601,341,997 | +38.631075% | Regression |

For parameterized workloads the pinned checker averages the two middle values
of the four pooled observations. Fixed workloads use the upper-middle value.
Both use the unchanged ten-percent rule. The immutable decision's generic
upper-middle median wording describes the fixed path; the parameterized path
uses the pinned comparator's mean-of-middle-two rule.
Every other workload passes its full ladder or fixed comparison. The retained
[untimed native replay](native-replay-v1/manifest.json) rebuilds the comparator
from the same eleven hash-bound source inputs and pinned toolchain. Its build
log, executable hashing command and output, commands, all 31 reports, raw streams and exit codes
are archived. Every JSON report is byte-identical to the collected report;
the outcome remains 29 passing workloads and two regressions. The rebuilt checker's computed SHA-256 matches the historical checker's hash.
This identity and all report hashes are retained. The replay runs no benchmark
and collects no new timings.

The raw per-call seconds at the two flagged parameters vary across blocks:

| Block | Direct baseline | Direct candidate | Reduced baseline | Reduced candidate |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 53.872245329 | 79.006739898 | 791.031277123 | 786.108784330 |
| 1 | 53.273237019 | 110.636285053 | 798.224724924 | 1,828.739953414 |
| 2 | 53.161157650 | 54.811123042 | 776.104551960 | 1,324.823202195 |
| 3 | 53.707424740 | 54.237685017 | 1,132.217426261 | 878.379481799 |

Variation also occurs in the baseline at smaller `runReduced` parameters in
block 1. The flags do not grow with parameter size: direct checking at 255 is
+1.132235%, while reduced production at 127 is −0.072646%.
All observations remain in the verdict. Recorded host load and memory provide
context; they do not justify removing samples or attributing the findings to
host activity. A source cause has not been established. Both findings remain
open for investigation. No unchanged retry or phase promotion follows from
this result.

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
from the original fixed repeats. Each export has one repeat, so each pooled
median has four observations per arm. Both reports contain zero regressions. The
final source, tool, helper, executable and checker integrity checks pass.
These are observations on this host, without a general speedup claim.

## Archive checks

Each manifest binds both compressed and original bytes. From the repository root:

```sh
python3 - <<'PY'
from pathlib import Path
import gzip, hashlib, json
root = Path('reports/bench-results/sign-det-phase6-comparison')
for directory in ('initial-capture', 'interacting-complete-v1',
                  'resolution-complete-v1', 'native-replay-v1'):
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
exports and exercise completion of all simulated blocks with a stub checker returning
2. The existing `ExportGuardTest.test_all_source_trials_below_floor` in
`scripts/bench/test_sturm_compare_exports.py` separately checks that the actual
compiled checker returns 2 on below-floor rows. An inconsistent checker pass is
also refused by the collector. These controls collect no benchmark measurements.

The unresolved requirements are investigation and resolution of the two primary
regression findings, followed by the applicable final computational acceptance.
No library phase or publication eligibility is advanced by these results.
