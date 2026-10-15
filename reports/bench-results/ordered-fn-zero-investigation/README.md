# OrderedFn zero-storage investigation

The question was whether a proved compiled replacement of the polynomial-zero
comparison could remove the zero construction and improve the retained slow
paths. The experimental source is `67ac425cf12303eade7a6d4d3615838fa2da64eb`;
the unmodified parent is `446b7f29910d2e2d4bbc0fa8c195b5cae830a9e7`.
Three compiler simplification equalities preserve the public definitions and all
semantic hypotheses. Core, semantic/conformance and native builds pass; the new
proofs have only the standard kernel axioms. The selected compiled sign path
removes the zero-polynomial construction, equality setup and their allocation
calls. The raw selected-symbol assembly is retained; it is not a whole-program
allocation count or a timing verdict.

The [decision](decision.json) was recorded before measurement. The unmodified
parent was rebuilt under the same toolchain and requirements as the variant.
Its binary differs from the older historical candidate: this experiment compares
only the local change with its actual unmodified parent. Child `git_commit`
fields record the clean invocation checkout, not either executable's producer.
The decision and manifest bind the separate source and binary identities.

| Workload | Parameter | Parent median ns | Variant median ns | Change |
| --- | ---: | ---: | ---: | ---: |
| height | 128 | 70.631704 | 57.662392 | −18.36% |
| height | 2048 | 70.029410 | 57.841311 | −17.40% |
| third | 1024 | 59052.123657 | 63011.383972 | +6.70% |
| approximation | 12288 | 4357420024 | 4372292578 | +0.34% |

All 24 scheduled arms completed, in three fixed trial-major adjacent AB/BA
blocks pinned to one automatically selected CPU. Every parsed observation and host observation is retained in the append-only
JSONL record. The reused probe driver omitted the parameter from its raw-file
stem: `height@2048` overwrote the same trial/arm's `height@128` stdout/stderr.
Eighteen original stdout/stderr pairs survive, not 24. The six earlier height
observations remain in full in the JSONL record, but their original raw byte
files are lost. This recording defect prevents a claim of complete raw-output
retention. Do not rerun to hide or replace it. Independent-arm medians
use the existing comparison arithmetic; paired medians do not replace it.
Small returned hashes are consistency observations, not mathematical oracles.

The declared condition for expanding to a full comparison was a greater than
10% improvement at both height parameters and at the third-level parameter,
with no greater than 10% approximation regression. The third-level condition
fails. Do not expand this probe, repeat it unchanged, promote the experimental
implementation as a resolution, or erase any of the four retained historical
findings. No phase counter or publication eligibility changes.

Native executables and generated C remain locally in
`/home/kim/.codex/tasks/hex-10575/orderedfn-zero-investigation`; their hashes
are in [manifest.json](manifest.json). [probe-summary.json](probe-summary.json)
retains each observation and median, and [probe.py.txt](probe.py.txt) retains the
actual driver. The driver reuses the existing repository CPU-lease helper.
