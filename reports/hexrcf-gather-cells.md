# Complete cell packets from independently owned coefficients

[`GatherCells.build`](../adapters/HexRCF/RealCoefficients/GatherCells.lean)
preflights every original typed divisor, gathers the actual native owners, and
runs the complete cell producer. Coefficient arity is independent of owner
count. Coordinates may repeat; original guards retain their separate order and
may mention values absent from the normalized matrix. Errors distinguish a
zero original divisor, gathering refusal and the actual discovery error.

`build_complete` composes `Shared.gather?_models` and
`CellDiscover.run_complete`. Compatible original signatures and an ordinary
base interpretation imply successful gathering and both accepted emitted
quantifier verdicts at the original owner values. Neither child success nor a
chosen enlarged model is an additional premise. `build_domains` derives
nonzero original typed guards from production success. `build_sound` derives
compatible origins, a gathered interpretation and both accepted verdicts from
the successful build equation without a nonzero-guard premise. `build_zero` rejects
before gathering, including constant formulas with an empty coefficient tuple.

[`NumberField.model_read`](../adapters/HexRCF/RealCoefficients/NumberField.lean)
derives the canonical owner-reader equation for the actual selected-field
presentation. `GatherCells.field_value` uses that equation and
`Shared.Model.value_of_model` to identify the gathered coordinate with its
original `Coefficients.ofField` real value. Context and packed-coordinate
identities remain explicit literal bindings. The adapter unfolds only the
owner's existing `Presentation.model` definition through `import all`; it
composes the public conversion and canonical-reader laws without copying
arithmetic, root selection or the owner's proof implementation.
`build_fields_complete` composes this binding for every independently presented
coordinate and concludes both emitted verdicts at the original selected-field
real values. Its inputs bind actual owner contexts and packed coordinates;
there is no extra semantic agreement or child-success hypothesis.

[`GatherCellsConformance`](../conformance/HexRCF/GatherCellsConformance.lean)
combines independently selected positive square roots of two and three. Its
three coefficient coordinates repeat one owner. Actual production and complete
literal replay check a simultaneous positive quadratic and a nonnegative
quadratic with a cancelled fourth-degree leading term and a repeated zero
root. Swapped coefficient coordinates are refused. A false constant with no
coefficient parameters retains nonempty original guards and both false
quantifier verdicts; an appended original zero divisor is rejected first.
These native executions are controls, separate from the actual theorem-body
and transitive axiom audits.

The optional umbrella, Lake conformance selection and mandatory admission-scan
root include the new module. The admission checker's existing synthetic-project
fixture includes that required root; its eleven unit tests pass. The manual
adds a runnable generic API example in the existing algebraic-cell chapter.
All eight retained desktop/narrow captures were opened and inspected, with zero
local overflow. Its displayed source is unchanged by the later model-binding
proof additions.

The [source-bound records](data/hexrcf-gather-cells/context.json) retain the
initial source, later proof source, raw build and metadata logs (including
failed attempts), browser script, captures and wrapper definitions. Source
versions are separate: the initial 11,766-job affected build and 14,295-job full
renderer concern the initial six-proof version; the later selected build
adds the canonical selected-field transport proofs and direct original-value
progress theorem. The intermediate eight-proof rebuild passes 11,766 jobs in
9 min 18.680 s at 15 GiB peak with zero swap, including the fresh algebraic and
Boolean source quotation audits. The final affected rebuild checks nine actual
proof bodies, each restricted to the standard three axioms. These operational
observations are operational evidence, not a before/after timing comparison. Every own Lean build and
render uses one aggregate 32 GiB cgroup with swap disabled and two Lean threads;
only one such invocation runs at a time.

These results concern native contexts and complete emitted packets. They do
not reconstruct frozen source/provider/predecessor histories, authenticate all
reached arithmetic records, provide strict compiled rejection of arbitrary
missing records, certify a new primitive common-field presentation, or prove
general frontend acceptance completeness. The ordinary base model and original
nonzero guards remain mathematical hypotheses of the progress theorem.
The existing full #10358 obligations remain open.

The initial context is source-scoped before the current-main merge at
f9f3b4d054. Its final nine-proof source remains available at its recorded commit.
The expanded current-main build passes 11,772 jobs; the revised acceptance
wrapper and ten actual gathering/source-binding bodies pass with the
[combined integration validation](data/hexrcf-algebraic-input-cells/review-context.json),
which checks 11,773 jobs and records the changed manual's separate render.
Earlier render/build records retain their original sources.
