# Complete native packets from original algebraic inputs

[`AlgebraicCells.build`](../adapters/HexRCF/RealCoefficients/AlgebraicCells.lean)
constructs the actual selected presentation of every original
`RealAlgebraicNumber`, gathers its owner and produces complete emitted packets.
Separate finite indices retain coefficient order, repeated coordinates and
all original guards, including guard-only inputs. Every declared input is
presented and gathered, including unused inputs; an unused irrational input
can enlarge the tower. Original zero guards reject before presentation
construction. Presentation and native cell errors retain
their distinct causes.

`presentations_success` consumes the owner's `NumberField.present?_success`.
`entry_real` authenticates the actual selected generator through
`NumberField.model_read`, `Shared.Model.value_of_model` and the owner's
`Presentation.generator_value`. The rational interpretation comes from the
public provider factory and its nominal-context equality; no new interpretation
or model-agreement premise is supplied. `compatible` derives the actual
rational origins through `Root.origin_base`.

`build_complete` concludes successful public production and both accepted
complete-replay verdicts at the original real values, given nonzero original
guards. It assumes neither presentation/gathering success nor a chosen enlarged
model. `build_domains` concludes that all original real divisors are nonzero
from successful production. `build_sound` derives both accepted verdicts from
the successful build equation alone, obtaining guard validity from that checked
conclusion rather than an additional premise. These results use the existing
shared formula language and native fields; they introduce no primitive number-field model.

[`AlgebraicCellsConformance`](../conformance/HexRCF/AlgebraicCellsConformance.lean)
uses both selected signs of √2 with independent positive √3. Its simultaneous
conditions contain a repeated zero root and distinguish the selected conjugate.
Both quantified verdicts are true for the positive input and false for the
negative one. Guard-only one, an unused zero input, repeated original guard
indices, late original zero rejection and empty true/false constant inputs are
covered. Additional linear constraints a < x < 1 give existential true and
universal false for a = −√2, and both false for a = √2. They test a coefficient
in variable-dependent atoms and separate the two quantifiers. These `#eval`
controls are separate from twelve actual automatic-input theorem-body and
transitive axiom audits, restricted to the standard three axioms.

The original source-scoped record precedes the merge at f9f3b4d054. Its
11,767-job selection checked eleven then-existing automatic-input bodies
(14.438 s, 1.6 GiB peak, zero swap) and the earlier manual text. The subsequent
automatic-input example has a separate 11,658-job chapter build (10.628 s,
1.3 GiB), a full 14,296-job renderer and ten inspected desktop/narrow captures.
These versions retain their own exact hashes; they do not claim final-head
validation.

Current-main integration at f9f3b4d054 passes the expanded 11,772-job selection
(14m9.918s, 13.6 GiB peak, zero swap), including the new actual bodies and fresh
algebraic/Boolean source quotations. The revised 10 gathering and 12 automatic
input bodies, guard-concluding acceptance theorems and linear controls pass
their 10,999-job selection (11.896s, 1.7 GiB). The combined source at
9336360f98 passes 11,773 jobs (5m7.728s, 6 GiB peak, zero swap), including the
direct owner descriptor reuse and fresh algebraic/Boolean source quotations.
The separate revised renderer passes 14,296 jobs (3m31.899s, 2.8 GiB) and all
ten captures were opened, with zero local overflow. API captures share a
paragraph anchor but record distinct scroll offsets and code-box bounds.
The [current integration record](data/hexrcf-algebraic-input-cells/review-context.json)
retains these versions separately from the initial context.

Current DAG/umbrella and admission checks cover 647 cones/1,547 modules; the
initial pre-merge scan covers 646/1,546. Eleven admission-checker and eleven
DAG-checker tests pass. The explicit stress build
is an auxiliary Lake target, separate from default conformance, with matching
structural metadata.

[`AlgebraicCellsStress`](../conformance/HexRCF/AlgebraicCellsStress.lean) retains
the stronger condition x² = √2 with 1 < x < √3 and its negative-conjugate
control. The initial combined test at source `d873312be6cfdb6dedcd786bc06023dac72bd999`
was stopped by the operator after 12 min 33.377 s (12 min 31.616 s CPU,
1.4 GiB peak, zero swap). It has no final module result or recorded acceptance.
Lake buffers job output, so neither the active case nor the producer/replay
phase is established. The systemd wrapper reports `result: success` for an
operator stop, but its `code=killed, status=15/TERM` and absence of a completed
Lake build distinguish this interruption from a passing run.

Three retained stack samples, expanded to identify more callers, show nested
`Algebraic.Element.inversePolynomial`/`inverseFactors`, polynomial gcd/xgcd,
Sturm queries and sign work beneath an IR interpreter call chain. They
identify sampled work during an observed execution problem without
establishing a scaling law or a repeatable speedup. The stronger case remains
an unresolved performance requirement; routine controls do not discharge it.
The interrupted source and the separately retained stress target are both
bound in the [context record](data/hexrcf-algebraic-input-cells/context.json).

All own Lean builds and rendering run serially under an aggregate 32 GiB
cgroup, swap disabled and two Lean threads. Build observations concern the
Mathlib-facing proof/test track, not a Mathlib-free executable benchmark.
Raw failed attempts, the interrupted run, stack samples, cap properties,
renderer/browser artifacts and exact source hashes are retained.

These native-input results do not reconstruct frozen source/provider/context
or predecessor histories, authenticate every reached arithmetic record,
certify a new primitive common-field presentation, establish strict compiled
rejection of arbitrary missing records, or finish general frontend quotation
and accepted completeness. Full #10358 remains open for those obligations and
the remaining realization and performance requirements.
