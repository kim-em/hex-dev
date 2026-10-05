# Direct sign-determination conformance

The [retained execution](data/sign-det-final-conformance/c377f14544/metadata.json)
checks the compiled BKR/Thom interfaces independently of the tactic and tower
clients. All commands succeeded. Their outputs, errors, source reconstruction
and original metadata are retained in the [archive](data/sign-det-final-conformance/c377f14544/archive.json),
with hashes of both compressed and original bytes. Applying the source patch
to its recorded base reproduces the entire captured source tree exactly.

The 33 compiled API checks include ℚ(∛2), the real quartic common field of
√2 and √3, rational and noninjective rational storage, and infinitesimal roots. They cover tables, selected
signs, completion, root enumeration, comparison, re-encoding, conversion,
noninjective storage and rejection of stale or mismatched evidence.

FLINT independently checks rational roots/signs, signs of close algebraic
values, and original selected embeddings in independently constructed common
fields. The three common-field cases use √2 and √3 in both orders and ∛2 with
∛4. Z3 independently checks the nested infinitesimal inputs and complete tables
at all four depths. The oracle also requires the rejection flags reported by
the native checker; Z3 does not decide those certificate rejections. These oracles read
computed coefficients and outputs; matching saved fixture hashes is not their
correctness criterion.

| Check | Result | Whole-command elapsed seconds |
| --- | --- | ---: |
| Compiled coefficient-field API checks | 33/33 passed | 8.525 |
| Rational fixture emission | 102 cases, subsequently checked by FLINT | 2.787 |
| Close-value scalar emission | 20 signs, subsequently checked by FLINT | 0.046 |
| Common-field emission | 3 cases, subsequently checked by FLINT | 0.619 |
| Nested infinitesimal emission | depths 1–4, subsequently checked by Z3 | 454.828 |
| Rational FLINT oracle | 102 cases, 0 failures | 0.108 |
| Close-value FLINT oracle | 20 signs, 0 failures | 0.088 |
| Common-field FLINT oracle | 3 cases, 0 failures | 0.054 |
| Nested Z3 oracle | 4 cases, 0 failures | 0.160 |
| Independent JSON byte oracle | 324 cases, 0 failures | 0.190 |
| Oracle regression tests (positive and mutation) | 51 tests passed | 0.901 |

The mutation tests cover omitted support, wrong counts or signs, substituted
inputs, changed selected embeddings and malformed byte records. The native
field checks separately exercise the actual certificate checker; oracle
mutation tests alone do not establish its rejection behavior.

The execution binds source `c377f1454431abc75d4d11e0d6fe98dfbb316a4d` and all
six compiled binary hashes. It used automatically leased CPU 57 on `chungus2`
and retained host load before execution and after every command. The oracle
environment used python-flint 0.9.0 / FLINT 3.6.0 and z3-solver 4.15.4.0.
The retained original collector asserts clean source and binary identity before
and after execution. Its code is included in the archive; the original metadata
records one revision and binary-hash set, rather than separate final fields. Every completed command is retained.

The captured commit was on the collector branch before its rebase onto main;
it was not a merged commit. Compared with main `7d59cacdc8`, the BKR/Thom,
number-field, real-algebraic and rational-function implementations and these
conformance/oracle sources are unchanged. The dependency changes are a
sign-det README addition and proof-only edits in `HexOrderedFn.Oracle`; the
Lake changes add client/companion targets. This is direct native-library
conformance, not a run of every consumer at a merged head.

The nested stderr contains per-depth timings, rather than errors. This
first collection does not include the separate infinitesimal emitter/oracle
and native JSON stress probes from the CI set. The supplementary execution
below covers these checks explicitly.

These are descriptive single-run times, including construction and output,
not isolated operation timings, medians, proof-checking costs or scientific
scaling verdicts. The capture does not measure allocated bytes or live memory.
The ordinary-kernel replay examples, shared coefficient-evidence interfaces
and remaining Phase-4 obligations have their own evidence; this collection
alone does not complete #10377.

To repeat the direct checks, build `hexsigndet_field_checks`,
`hexsigndet_emit_fixtures`, `hexsigndet_emit_field_signs`,
`hexsigndet_emit_common_fields`, `hexsigndet_emit_nested_fields` and
`hexsigndet_json_bytes` with `lake build`. The retained metadata lists every
exact emitter, oracle and regression-test command. Use the nested emitter's
`--profile local` and the corresponding oracle's `--profile local` for all
four depths. The oracle package versions are part of the input contract.

To reconstruct the captured source, create a separate checkout of the base
recorded in `archive.json`, decompress `source.patch.gz` and apply it with
`git apply`. Build and run from that checkout's repository root. Install the
oracle environment with `python -m pip install python-flint==0.9.0 z3-solver==4.15.4.0`. Adapt the archived absolute worktree/output paths to the
new checkout; command arguments and package pins remain as recorded. The
retained collector documents CPU pinning and its before/after assertions.

## Supplementary CI oracle checks

The [supplementary execution](data/sign-det-final-conformance/da92b2a188/metadata.json)
covers the separate infinitesimal fixtures, their independent Z3 oracle and
regression tests, and native JSON capacity probes. All four commands exited
successfully. It records collector-branch source `da92b2a188`, based on
`7d59cacdc8`, with source reconstruction and the collector retained. This
source contains the rebased in-process kernel collector; it was not yet
merged when captured. Its before/after revision, clean-tree state, binary
hashes and CPU affinity are explicit fields in the original metadata.

| Check | Result | Whole-command elapsed seconds |
| --- | --- | ---: |
| Infinitesimal fixture emission | completed | 20.341 |
| Independent infinitesimal Z3 oracle | 31 cases, 0 failures | 10.841 |
| Infinitesimal oracle regression tests | 18 tests passed | 66.677 |
| Native JSON stress probes | all capacity/rejection and stack controls passed | 4.111 |

The JSON probes exercise a 4 MiB string, arrays and objects with one million
entries, an escaped string, nesting depth 128, and explicit byte/depth/digit
rejections. A stack canary verifies that the runtime actually applies the
8 MiB stack setting. These are capacity/correctness checks, not timing or
combined depth/width memory bounds. The time observations have the same
whole-command limitations as the first collection.
