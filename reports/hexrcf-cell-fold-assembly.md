# Algebraic cell-fold proof assembly

This build-only experiment asks whether replacing `mkDecideProof` with explicit
construction of its `of_decide_eq_true` application changes the cost of checking
the fixed complete algebraic-cell example. Both variants submit the same
proposition to the unchanged guarded ordinary-kernel checker. All original
true/false folds, producer reduction exclusions and axiom audits remain.

The old helper adds an `id` type ascription and performs small elaborator
unification and instance-synthesis work. The ascription already prevents heavy
elaborator reduction. The new expression omits that assembly; the decisive
kernel reduction is the same in both variants. It is not a replacement of
elaborator validation with kernel validation: the kernel validated both.

## Matched observations

The retained schedule has two adjacent trials, AB then BA, on automatically
selected CPU 23. A is the existing helper; B is explicit proof assembly. Each
sample forces a fresh build of `HexRCF.CellReplay.Algebraic.Check` with identical
imports and fixed literal certificates. Implicit Lake cache restoration is
disabled inside the bounded command. All four completed samples are retained;
host load is recorded without a quiet-core preflight or sample rejection.

| Trial/order | Arm | Build wall time (s) | Observed cgroup peak (GiB) | Module `.olean` bytes |
| --- | --- | ---: | ---: | ---: |
| 0 / AB | A | 69.454 | 4.375 | 192,024 |
| 0 / AB | B | 66.046 | 4.225 | 212,328 |
| 1 / BA | B | 60.658 | 4.291 | 212,328 |
| 1 / BA | A | 63.251 | 4.874 | 192,024 |

In these two pairs, B's wall time is 4.9% and 4.1% lower; its observed peak is
3.4% and 12.0% lower. These few shared-host observations are inconclusive about
a repeatable speedup or a general memory improvement. The memory counter is
sampled from the build cgroup; full raw systemd summaries are also retained.
The module size includes the elaborator implementation and metadata. It is
not a measurement of the emitted proof term alone.

An earlier standalone fresh build observed 81.090 seconds and a rounded 9 GiB
cgroup peak; an unmatched candidate smoke build observed 74.739 seconds and
4 GiB. These are retained diagnostics outside the matched schedule. Their
difference does not establish a halving of memory use. The initial diagnostic
requested a cache environment setting on its wrapper parent without forwarding
it; the corrected record explicitly makes no cache-control claim. Its log
does establish that the target was rebuilt. The matched runner passes the
setting inside the bounded command.

## Validation and source scope

The [record](data/hexrcf-cell-fold-assembly/context.json) binds the two changed
source files and the actual kernel guard to PR source
`eec8df2e18233a37fccb323c9799cf954e99b265`. The measurement worktree at
`5da4aa647ee82620cf23a296f1a0d089bc063eed` also contains a separately staged
serialization continuation. Its 918 local imports for this target were
independently compared byte for byte with the PR source. The staged serializer
modules and the adapter's `CellBuild`, `RootBuild` and `CellDiscover` modules
are absent from this import closure. External imports are tied to the retained
toolchain and dependency manifest.

All samples pass the actual guarded kernel checks and the standard-three-axiom
audit. The separate 11,010-job fresh quotation build passes the two algebraic
source proofs, all six Boolean folds, four Boolean source proofs and the
binding controls, taking 4 minutes 47.960 seconds and peaking at 5.7 GiB.
The importing manual chapter is subsequently built at the PR source: 11,612
jobs, 62.528 seconds and a 4.7 GiB peak. The latter incremental build reuses
already checked artifacts; it is not a fresh compilation rate. Displayed
manual text and styles are unchanged, so there is no new rendering claim.

Every own build is serial under an aggregate 32 GiB limit, zero swap and two
Lean threads. These are Mathlib-importing build-only probes. They are not
executable numerical benchmarks, a full-tactic scaling study or extension
completeness evidence.

CI run 38721246777 attempt 1 ended with SIGTERM/exit 143 during conformance;
its retained log and annotations identify neither a Lean proof error nor an
explicit timeout or out-of-memory cause. This experiment does not identify
that cause or establish that the proof-assembly change prevents it. Later CI
attempts and source revisions must be assessed on their own exact heads.
