# Native specialization at one ordinary reader

`NativeSpecialize.polynomial_read` and `eval_read` follow the existing shared
coefficient grouping, dense addition and Horner evaluation. Their partial-domain
laws require neither a global injective map to ℝ nor field instances on raw
syntax. `row_real` uses the actual stored provider realization and requests the
coefficient coordinates, sample, specialized atom values, leading coefficients
and supplied original divisor operands in one finite inventory. Leading signs
prove normalized size and degree preservation of the source polynomial at the
reader coordinates, including the zero polynomial, rather than assuming it. All atom occurrences retain their ordered source positions.

The reader exposes its domain-relative negation law so consumers can interpret
further source expressions. `true_real` consumes a computed true point row and
strict nonzero native signs
for every supplied divisor. Its conclusion retains the matrix, nonzero divisors
and explicitly inherited fixed coefficient identities at that one real reader.
It retains source sizes at the original coefficient coordinates.
`not_forall` uses a false point row for a universal counterexample. Original
source/guard collection and coefficient identity authentication remain caller
obligations; a bounded constant registration alone does not provide the actual
mathematical provider history required here.

The concrete conformance proofs consume computed native rows and the actual
realization laws for `0<x<1`, four affine inequalities together with `2-x ≠ 0`,
false universals with and without a fixed coefficient, and two successive native
infinitesimals satisfying
`0<b<a²` and `0<a<1` jointly. The private degree fixture specializes the fixed
coefficient 2 in `(c-2)*x²+x`, checks the native degree vector `[0,0,1]` for
constant/zero/remaining-linear polynomials, the size vector `[1,0,2]` distinguishing
the constant from zero, and consumes `true_real` and the computed true row to
retain those sizes and degrees at the authenticated original coordinates. A separate quadratic has an infinitesimal
leading coefficient; its source size 3 requires the realized nonzero leading
sign. It also retains domain membership, positivity and the actual negation of
that reader coordinate. Proof-marker guards prevent replacing these consumers
with unrelated easier proofs.

[Source-bound records](data/hexrcf-native-specialize/source-consumer-context.json) retain
source hashes and observed validation exits at the recorded implementation
commit. Twelve complete API/fixture axiom inventories contain exactly `propext`, `Classical.choice`, `Quot.sound`;
five fresh ordinary-import consumers repeat the full inventory and confirm each
re-exported theorem has its exact target through uncached base-checker checks.
Imported markers identify the theorem used; they do not inspect or recheck its
imported proof body. The in-module conformance markers check consumption of the
computed rows and realization laws. Lake validates the
fixture, optional adapter/conformance/manual integration, fresh ordinary imports
and rendered manual; exact operational job counts are recorded with each log.
These are build observations, not scientific performance evidence. The
[previous revised records](data/hexrcf-native-specialize/review-context.json)
retain twelve API/fixture and five ordinary-import inventories at their recorded
sources. The [original records](data/hexrcf-native-specialize/context.json) retain
ten API/fixture and four ordinary-import inventories. These historical sources
and failed drafts do not attest the current consumer tests.

DAG/umbrella checks, the admission audit (409 cones, 1,262 modules), copyright,
line limits, manual split and diff checks pass. All affected relative path
targets exist; anchor fragments were not checked. Six desktop/narrow captures
were inspected for the three new manual paragraphs; their measured paragraph
widths fit. This is not a whole-page overflow or code-snippet-fit audit.
The default optional adapter umbrella and existing conformance target include
this API. No phase advance, base umbrella family import or CI job is added.
This does not prove equivalence with the coefficient conversion used by
`Tower.Sample.signs`, cell membership or complete coverage, and it implements
neither frozen certificate replay nor general source-goal quotation. Those
integration obligations, automatic common-field certificate coverage, accepted
algebraic completeness and full-scope evidence remain open under #10358.
