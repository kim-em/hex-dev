# Checked generator-window proof costs

`rcf.algebraic.signRefinements` remains zero by default. A four-step budget
removes full sign queries in a checked lower-precision fixed-field example,
but this comparison does not establish a useful reduction in whole-module
cost. The three source examples also show small, mixed changes. No run was
discarded and no unchanged rerun was taken.

The producer uses the existing root-refinement API to propose a smaller
rational interval. The literal table keeps its original generator polynomial,
outer interval and count. Replay checks containment and a second count-one
certificate, which proves the inner interval selects the same real root.
All entries use that checked inner interval; inconclusive Horner signs retain
full rational query evidence. The entry order and coefficient representation
stay fixed. Budget exhaustion or an unavailable contained window retains the
already checked table. Invalid proposed evidence is terminal. Frozen replay
never runs refinement or repairs a malformed window.

The fixed case uses `SquareTwo.square` at eight bits and the formula
`x² = θ ∧ 1 < x ∧ x < 2`. Its candidate proof must contain a literal inner
window; the original proof must contain none. The fixture's conformance requires a strict decrease in full-query entries and
preserves every key and sign. The current producer additionally retains the
original table whenever a bounded attempt removes no full query, and skips
refinement in full-query mode.
The source cases are the further-root, reciprocal and cubic manual examples.
Both arms use identical imports and goals, monic carriers, unreduced-coordinate
quotation, Horner evidence, indexed retrieval and split kernel replay. Only the
zero/four-step refinement budget differs.

The exact measured source is
[`ce95c8f1f8400bbc9e649ee366cdb6242503c808`](https://github.com/kim-em/hex-dev/tree/evidence/hexrcf-window-ce95c8f1f),
based on `6b4acf58b33bf810976ec224ee188d12099ba84e`.
The measured source predates the prepared frontend on `4ddaf23f1`. The current
`CommonTactic`, `Preparation`, `Replay` and frozen serializer differ from that
source, as do the refinement-quality and cancellation guards. The retained
timings measure their named source, not the current shipped tactic. Current
proof builds validate compatibility without establishing performance equality.

Repository and package checkouts were clean and stayed unchanged during the
comparison. The source hashes, full checkout identities, compiler outputs,
artifact sizes, memory observations and every completed arm are in the
[raw report](bench-results/hex-rcf-window-proofs-ce95c8f1f-chungus2.json) and
[incremental samples](bench-results/hex-rcf-window-proofs-ce95c8f1f-chungus2.json.samples.jsonl).

Four trial-major rounds use adjacent pairs, rotate pair order and alternate
AB/BA. The shared-host runner automatically leased CPU 87 (SMT sibling 39),
with one Lean thread. Host activity is recorded context; samples are retained
regardless of that activity. All 32 proof builds passed their ordinary-kernel
axiom guards: only `propext`, `Classical.choice` and `Quot.sound` occur.

| Case | Original median s | Refined median s | Median paired change s | Private proof bytes | Median peak RSS KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| fixed | 12.844 | 12.821 | +0.007 | 528336 → 590008 | 4033170 → 4034566 |
| further | 13.273 | 13.479 | +0.157 | 641784 → 641784 | 4054264 → 4054496 |
| reciprocal | 13.412 | 13.379 | -0.067 | 700144 → 700144 | 4024844 → 4024590 |
| cubic | 14.748 | 14.616 | -0.133 | 623744 → 623744 | 4202548 → 4204728 |

The separate [quoted-syntax audit](data/hexrcf-window-signs/ce95c8f1f/audit.json)
checks the final timing artifacts, with their hashes captured before that audit.
The public/private probe files remained byte-identical during the audit.
These are hashes of the final artifacts, not per-arm hash captures. Its
[complete compiler output](data/hexrcf-window-signs/ce95c8f1f/compiler-output.json) is
retained as JSON-encoded complete text, separately from the timings.

| Case | Original solver Horner/query entries | Refined solver Horner/query entries | Inner window |
| --- | ---: | ---: | --- |
| Fixed eight-bit field | 123 / 3 | 126 / 0 | candidate only |
| Further source goal | 126 / 0 | 126 / 0 | neither |
| Reciprocal source goal | 123 / 0 | 123 / 0 | neither |
| Cubic source goal | 120 / 0 | 120 / 0 | neither |

The reciprocal proof also has a separate source-authentication table with
one full query in both arms. The solver optimization does not refine that
table. On the current monic/indexed path, the three source-example solver
tables already decide all recorded signs with Horner evaluation. No tighter
solver window is emitted in those cases. Counts describe distinct quoted table
syntax and recorded entries, not heap sharing or expanded execution work.

The median paired change is calculated from adjacent differences and need
not equal the difference of the two marginal medians. The first further-root
pair's +3.023-second difference remains in the report and summaries.
The fixed-field candidate adds 61,672 private proof bytes without an observed
material time improvement; the source cases have unchanged private-file sizes.
The collector reports `no-comparable-control`. This is a focused whole fresh
Lake-module cost comparison, including elaboration, production, quotation and
kernel work. It is not isolated sign timing, an asymptotic bound, physical
sharing evidence or a general precision-scaling attestation.

Reproduce the fixed schedule with:

```sh
python3 scripts/bench/hexrcf_window_proofs.py --timeout 120
```

The timeout is an operational per-arm safeguard. Completed samples are retained
outside the checkout before being copied here; do not mutate the measured tree
or dependencies during a comparison. Fresh checked-window and malformed-window
regressions belong to the default build. The paired studies remain on demand.
