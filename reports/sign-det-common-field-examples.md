# Common-field sign/root examples

The `common-fields.jsonl` emitter runs three actual BKR/Thom computations over
`QAdjoin` coordinates. Independent inputs √2 and √3 are used in both orders in
degree-four common fields; independently constructed ∛2 and ∛4 are used in a
degree-three field. The outputs contain complete sign tables, root lists and
selected signs, cross-polynomial comparisons, a comparison of the same root
defined by `x − a` and `x² − a²`, re-encoding, and replay rejection results.
FLINT `qqbar` independently reconstructed the selected embeddings and checked
all three records exactly (0 failures); eight adversarial oracle tests passed.

The generic proofs used by these examples are `determine_correct`,
`Descriptor.signAt_correct`, and `Descriptor.compare_correct`. The companion
specializations `CommonFieldConformance.table_correct`, `signAt_correct`, and
`comparison` apply those results to the selected real embedding of the actual
common number field. `CommonFieldConformance.value_eq` identifies the fixture
coefficient conversion with the existing `Coefficients.ofField` interpretation.
Guarded axiom inventories for the specialized results contain only Lean's
standard logical axioms. The manual's executable `#guard` is a computation
check; the companion theorems supply its mathematical justification.

One descriptive whole-emitter measurement on shared host `chungus2`, pinned to
automatically selected logical CPU 5, took 110.40 seconds elapsed and 109.95
seconds user CPU, with 67,548 KiB peak process RSS. The process emitted all
three cases, and its output matched the committed JSONL byte for byte. The
binary SHA-256 was
`50cfb94414b934a3558a0def782a30ad9f33dc627815cbf25edfe43f08b8d268`;
the tested source is commit `c42a39212`. The timing includes common-field
construction, sign determination, root enumeration, comparison, re-encoding
and output generation. It does not isolate any one operation, report allocated
bytes, or serve as a Phase-4 scaling verdict. No completed run was discarded.
