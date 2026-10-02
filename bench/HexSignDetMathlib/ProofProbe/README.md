# Sign-determination proof examples

`lake build HexSignDetMathlibProofProbe` builds every file in this declared
proof-example root in the existing CI job.

- `Replay`: literal BKR graph acceptance/rejection and mathematical root counts.
- `SelectedSigns`: selected-root signs over the actual cubic `QAdjoin` field.
- `Completion`: partial Thom encodings, zero derivative signs and completion.
- `Reencoding`: checked re-encoding/refinement preserving the selected root.
- `Nested`: one-level rational-function coefficients, supplied graph acceptance,
  arithmetic/context rejection and normalization-certificate checks.

The imported conformance modules combine executable examples with ordinary
kernel correspondence proofs and guarded axiom inventories. Literal graph
replay and rejection proofs use ordinary kernel reduction. They contain no
admitted proof or `native_decide`.

Larger optional correctness fixtures live under
`conformance/HexSignDetMathlib/Diagnostics`
and are outside the declared proof-example root. Build an individual module
through Lake when it addresses a concrete diagnostic question. Completed
measurements and their original source snapshots remain under `reports/data`;
computational Phase-4 scaling, comparison, allocation and profile obligations
are unaffected by this proof-example layout.
