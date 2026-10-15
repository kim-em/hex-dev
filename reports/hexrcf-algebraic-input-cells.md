# Complete native packets from original algebraic inputs

[`AlgebraicCells.build`](../adapters/HexRCF/RealCoefficients/AlgebraicCells.lean)
constructs the actual selected presentation of every original
`RealAlgebraicNumber`, gathers its owner and produces complete emitted packets.
Separate finite indices retain coefficient order, repeated coordinates and
all original guards, including guard-only inputs. Original zero guards reject
before presentation construction. Presentation and native cell errors retain
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
from successful production. These results use the existing shared formula
language and native fields; they introduce no primitive number-field model.

[`AlgebraicCellsConformance`](../conformance/HexRCF/AlgebraicCellsConformance.lean)
uses both selected signs of √2 with independent positive √3. Its simultaneous
conditions contain a repeated zero root and distinguish the selected conjugate.
Both quantified verdicts are true for the positive input and false for the
negative one. Guard-only one, an unused zero input, repeated original guard
indices, late original zero rejection and empty true/false constant inputs are
covered. These `#eval` controls are separate from eleven actual theorem-body
and transitive axiom audits, restricted to the standard three axioms.

The 11,767-job selected proof/optional-library build passes with these eleven
body audits (14.438 s, 1.6 GiB peak, zero swap). Its manual source predates the
new automatic-input example; that example has its own successful 11,658-job
chapter build (10.628 s, 1.3 GiB). The full 14,296-job renderer and ten inspected
desktop/narrow captures separately validate the changed displayed content.
The DAG/umbrella and admission checks cover 646 cones/1,546 modules; eleven
admission-checker and eleven DAG-checker tests pass. The explicit stress build
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
Sturm queries and sign work. They explain an observed execution problem without
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
