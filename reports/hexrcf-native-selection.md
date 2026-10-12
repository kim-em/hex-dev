# Checked root constraints in the source schema

`NativeSelection.selection` translates the actual rational selected-root
owner's defining, derivative and strict finite endpoint constraints into the
existing integer `RealFormula.QF` syntax. `identity` identifies a selected root
at any source coefficient coordinate, using the owner's `constraints_iff`
count-one theorem. `selected` and `unique` provide its one-coordinate forms.
The adapter does not reconstruct a separate uniqueness proof or formula AST.

Each rational polynomial is multiplied by the existing strictly positive common
denominator. `polynomial_eval`, `cleared_eval` and `atom_correct` prove that this
translation preserves evaluation and all six comparisons. `signAtom_correct`
retains the exact requested ternary sign; a different integer translates to
false. `signs_correct` retains the complete ordered list. Unequal query/sign
lengths translate to false, rather than truncating a zip. A rejected literal
selection is not itself a production-handler diagnostic.

`translate` permits a proved zero-reflecting projection to rational
coefficients. `projected_real` and `translate_correct` establish its exact
polynomial/sign correspondence. The concrete fixture projects the stored values
of the actual wrapped rational predecessor; its descriptor and context remain
unchanged. This requires no field instance on raw representatives.

`relation` encodes the exact rational-polynomial value of a coefficient
coordinate in its selected generator. `relation_correct` proves the equation
using the same positive denominator clearing. This is a frontend relation in
the shared schema, not a replacement number-field arithmetic implementation or
a proof that an arbitrary source expression has those coordinates.

The [conformance fixture](../conformance/HexRCF/NativeSelectionConformance.lean)
consumes the existing frozen positive √2 descriptor and its actual ordered
constraints. The selected-value theorem and negative-conjugate refusal use
owner count-one semantics. A joint actual native row realizes that generated
selection and the further-root matrix at one reader through
`NativeSources.true_real`, proving `∃ x : ℝ, x² = Real.sqrt 2 ∧ 1<x ∧ x<2`.
Changing the coefficient to the negative conjugate falsifies the actual native
joint formula. Its row proof uses the actual conversion model and shared
specialization theorem. These results do not assume an inherited-base identity
for the selected algebraic suffix.

A separate derived-coordinate selection identifies α²−1 as 1 from positive
√2. The nontrivial-denominator relation `c₁=c₀²/3−1/5` is exactly the normalized
integer atom `15*c₁−5*c₀²+3=0`. This has both a kernel literal equality and a
value-equivalence proof; the compiled literal/row controls remain separate.

The generic API uses ordinary public module imports. Its eleven complete theorem
inventories and the fixture's twelve inventories contain exactly `propext`,
`Classical.choice`, `Quot.sound`. The concrete non-module fixture exposes private
import closures in the pinned toolchain; it does not attest public-only access
to the frozen construction. In-module proof markers consume owner uniqueness,
actual row conversion and finite-reader laws. A separate fresh module composes
the public selection and `NativeSources` APIs, with one complete inventory and
an uncached exact-target check. Imported declarations are not proof-body
rechecked by that target check. Seven compiled controls are separate from these
proof inventories. Literal shape proofs are ordinary-kernel equalities.

The optional umbrella and default adapter target include the API; the existing
conformance target includes its fixture. The existing rcf manual explains the
selection, rational projection, coordinate relation and limitations, with a
runnable unique-selection example. This is not an automatic source-syntax
translator, a frozen context/history decoder, a complete cell certificate or
a general `rcf` quotation path. Original division collection and guard checking
remain required, including cancelled operands; these formulas do not discharge
those obligations by construction.

Full #10358 acceptance still needs checked recursive context/provider-history,
root/sign and reached arithmetic assembly; complete root/cell coverage and
all-live transport; automatic common-field certificate coverage and accepted
algebraic completeness; final full-scope conformance/manual/evidence. Available
finite-joint realization and root/query laws are consumed here, not claimed as
missing prerequisites. Numerical runtime algorithms and nested exporter/checker
assembly remain with their existing family owners.

Lake adapter/conformance/manual integration passes 14,464 jobs. The affected DAG,
admission, copyright, line-limit, manual-split, literal and diff checks pass;
relative file targets resolve. These are operational checks, not performance
measurements or evidence of whole-issue completion.

The fresh public-module consumer and full manual renderer pass 14,161 Lake jobs.
Six desktop/narrow captures of the selector, runnable example and limitation
paragraph were inspected. Narrow code scrolls within its code block; this is
not a whole-page overflow audit. The
[source-bound records](data/hexrcf-native-selection/context.json) retain source
hashes, decoded/encoded record hashes, commands, observed exits and these
captures. No performance conclusion follows from these operational checks.
