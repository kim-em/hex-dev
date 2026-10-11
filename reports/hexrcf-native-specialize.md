# Native specialization at one ordinary reader

`NativeSpecialize.polynomial_read` and `eval_read` follow the existing shared
coefficient grouping, dense addition and Horner evaluation. Their partial-domain
laws require neither a global injective map to ℝ nor field instances on raw
syntax. `row_real` uses the actual stored provider realization and requests the
coefficient coordinates, sample, specialized atom values, leading coefficients
and supplied original divisor operands in one finite inventory. Leading signs
prove normalized degree preservation, including the zero polynomial, rather
than assuming it. All atom occurrences retain their ordered source positions.

`true_real` consumes a computed true point row and strict nonzero native signs
for every supplied divisor. Its conclusion retains the matrix, nonzero divisors
and explicitly inherited fixed coefficient identities at that one real reader.
`not_forall` uses a false point row for a universal counterexample. Original
source/guard collection and coefficient identity authentication remain caller
obligations; a bounded constant registration alone does not provide the actual
mathematical provider history required here.

The concrete conformance proofs consume computed native rows and the actual
realization laws for `0<x<1`, four affine inequalities together with `2-x ≠ 0`,
a false universal, and two successive native infinitesimals satisfying
`0<b<a²` and `0<a<1` jointly. The private degree fixture specializes the fixed
coefficient 2 in `(c-2)*x²+x`, checks the native degree vector `[0,0,1]` for
constant/zero/remaining-linear polynomials, and consumes `row_real` to retain
those degrees at the same real reader. Proof-marker guards prevent replacing
these consumers with unrelated easier proofs.

[Source-bound records](data/hexrcf-native-specialize/context.json) retain eleven
source hashes at the recorded implementation commit. Ten complete API/fixture
axiom inventories contain exactly `propext`, `Classical.choice`, `Quot.sound`;
four fresh ordinary-import consumers repeat the full inventory, base uncached
exact-target kernel checks and imported proof markers. Lake validates the
fixture (10,928 jobs), optional adapter/conformance/manual integration (14,454),
fresh ordinary imports (10,935) and rendered manual (14,153). These counts are
operational build observations, not scientific performance evidence. A failed
public statement referring to private fixture data is retained as a rejected
draft; the accepted degree test is private and audited directly.

DAG/umbrella checks, the admission audit (409 cones, 1,262 modules), copyright,
line limits, manual split and diff checks pass. All 142 affected relative path
targets exist; anchor fragments were not checked. Six desktop/narrow captures
were inspected for the three new manual paragraphs; their measured paragraph
widths fit. This is not a whole-page overflow or code-snippet-fit audit. The
historical wording in the browser driver's completion message does not name
the captures; the saved inspection metadata identifies the new paragraphs.

The default optional adapter umbrella and existing conformance target include
this API. No phase advance, base umbrella family import or CI job is added.
This does not prove equivalence with the coefficient conversion used by
`Tower.Sample.signs`, cell membership or complete coverage, and it implements
neither frozen certificate replay nor general source-goal quotation. Those
integration obligations, automatic common-field certificate coverage, accepted
algebraic completeness and full-scope evidence remain open under #10358.
