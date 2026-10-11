# Native sample coefficient conversion

`NativeSamples.row_converted` connects the actual `Tower.Sample.signs` conversion
with specialization of the existing shared formula at the converted coefficient
coordinates and sample. It consumes the owner's `Conversion.Model` in an ordered
model field; no ordinary-real interpretation of the whole parent context is
assumed. `RepresentationSpecialize.polynomial_eval₂` generalizes the existing
coefficient grouping and dense evaluation proof to that field, preserving the
existing real-valued API. Raw coefficient representations acquire no field
instances or new formula syntax.

`sign_converted` preserves every supplied original divisor's sign. In an infinite
model field, `polynomial_converted`, `degree_converted` and `size_converted`
preserve the interpreted polynomial, actual degree and normalized size. Zero
reflection distinguishes zero polynomials from nonzero constants without assuming
injectivity between distinct nonzero representations. `true_real` consumes a true
sample row, authenticated converted source coordinates, strict original parent
signs and the actual target provider realization. One ordinary reader retains the
matrix, source sizes equal to those of the original parent polynomials, original
divisor nonvanishing and inherited identities. `not_forall` uses a false point row
for a universal counterexample.

[Conformance](../conformance/HexRCF/NativeSamplesConformance.lean) uses the actual
selected positive root of X²−2 and its owner conversion. Six atom positions retain
zero and repeated-root atoms, leading cancellation and the (1,2] guard atoms.
Independent kernel row proofs and native guards check `[0,0,0,1,-1,-1]`; changing
the source coordinates from 2 to −2 at the same root changes the row to
`[1,1,0,1,-1,-1]`. Empty traversal stays empty. Size checks preserve
`[3,5,0,2,2,2]` and distinguish zero/constants with `[0,1,1]`.

A nested section uses the delivered selected root over the fixed √2 coefficient.
Kernel proofs preserve that selected coefficient's real identity and the complete
row and size conversion. The two native rows are `[0,1,-1]`; the nested kernel
proofs do not quote that computed sign word. In-module uncached target checks and
proof-body markers retain the actual conversion and selected embedding laws.
Seventeen complete API/fixture axiom inventories contain exactly `propext`,
`Classical.choice`, `Quot.sound`. Eight fresh ordinary-import consumers repeat
complete inventories and pass uncached base-checker checks at their exact targets.
Those imported checks confirm theorem targets and dependencies; they do not
recheck imported proof bodies. Eleven compiled guards are separate computational
observations.

The optional default adapter umbrella and existing conformance target include
this API. Lake validates conformance, optional adapter/conformance/manual
integration and fresh ordinary imports. The manual includes a runnable public
section-constructor example in the existing rcf chapter. Six desktop/narrow
captures cover the conversion paragraph, example and soundness boundary. Paragraph
widths fit; the narrow code example scrolls horizontally. These checks do not
establish whole-page overflow freedom. [Source-bound validation records](data/hexrcf-native-samples/context.json) retain
actual commands, observed exits, source hashes and capture metadata. DAG/umbrella,
admissions (410 cones, 1,263 modules), copyright, line limits, manual split, relative
path targets and diff checks pass; URL fragments are not checked. Operational
job counts are not scientific performance measurements.

The actual target provider history, source identity proofs and original guard
collection remain explicit caller obligations. The direct `true_real` and
`not_forall` APIs have complete axiom inventories; the concrete fixtures cover
conversion, not a newly assembled provider history or source-goal quotation.
Complete certificate assembly still needs checked cell membership and coverage,
frozen context/history and reached arithmetic records connected to the existing
joint realization laws. This tranche supplies none of those checks, nor accepted
algebraic completeness. #10358 remains open for that integration and full-scope
evidence; no phase, base-family import or CI job is added.
