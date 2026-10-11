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
sample row, inherited base/provider source identities, strict original parent
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
Kernel proofs preserve that selected coefficient’s value in the owner conversion
model and the complete row and size conversion. Separate kernel proofs check the
source and converted words `[0,1,-1]` using the actual selected-root facts. The
negative conjugate changes both words to `[1,1,-1]` at that same upper root.
The source size vectors have independent ordinary-kernel proofs. Actual point
consumers construct the rational provider history and inherited coordinate
identities for the X²−2 section, retaining a parent guard from a true row and
refuting `∀ x : ℝ, x² > 2` through the false-row API. In-module uncached target
checks and
proof-body markers retain the actual conversion and selected embedding laws.
Twenty-four complete API/fixture axiom inventories contain exactly `propext`,
`Classical.choice`, `Quot.sound`. Fifteen fresh ordinary-import consumers repeat
complete inventories and pass uncached base-checker checks at their exact targets.
Imported reexports confirm theorem targets and dependencies; they do not
recheck imported proof bodies. Two fresh size-word consumers additionally compose
the imported conversion equality with the kernel-checked source vector. Thirteen
compiled guards are separate computational
observations.

[Infinitesimal-parent conformance](../conformance/HexRCF/NativeSampleModelConformance.lean)
additionally constructs the owner's ordered real-closed reference model from an
actual staged infinitesimal history. A frozen descriptor
selects the positive root of X²−ε in (0,1); the ordinary-kernel descriptor check
and exact subject proof bind its polynomial, bounds and derivative slots. The
public `Tower.Sample.section_correct` supplies the actual extension conversion.
The test consumes `row_converted` and `true_real` for that selected-root sample,
with the original parent ε guard passing through the extension embedding. No
fixed coefficient identity specifies that guard's real value. One reader supplies
`0 < read(sample) < 1` and `read(embed ε) ≠ 0` together. Four complete in-module
inventories cover descriptor acceptance, exact subject, row truth and the reader
conclusion. Proof-body markers retain the actual reference and section factories,
row conversion and native guard input; in-module elaboration checks the proof
bodies, and uncached checks confirm their targets. A separate fresh ordinary-import
consumer checks the complete reader/domain/guard conclusion and its inventory;
it does not recheck the imported proof body. Two compiled guards are separate
computational observations. These checks
exercise the generic ambient-model API without adding infinitesimal source syntax.
The [model supplement](data/hexrcf-native-samples/model-context.json) records its
sources and checks separately from the earlier 24/15 validation snapshot.

The optional default adapter umbrella and existing conformance target include
this API. Lake validates conformance, optional adapter/conformance/manual
integration and fresh ordinary imports. The manual includes a runnable public
section-constructor example in the existing rcf chapter. Six desktop/narrow
captures cover the conversion paragraph, example and soundness boundary. Paragraph
widths fit; the narrow code example scrolls horizontally. These checks do not
establish whole-page overflow freedom.
[The selected-root and point-consumer validation snapshot](data/hexrcf-native-samples/review-context.json) retains
actual commands, observed exits, source hashes and capture metadata. DAG/umbrella,
admissions (410 cones, 1,263 modules), copyright, line limits, manual split, relative
path targets and diff checks pass; URL fragments are not checked. Operational
job counts are not scientific performance measurements.

`Origin.RealValue` fixes values inherited from the staged base/provider, not
arbitrary selected-root coordinates in an algebraic suffix. The nested √2 model
identity cannot satisfy the point APIs’ `fixed` premise. Real identity of those
source coordinates at the finite reader remains open. The false-row API takes no
original divisor guards.

The actual target provider history, inherited source identity proofs and original
guard
collection remain explicit caller obligations. The direct `true_real` and
`not_forall` APIs have complete axiom inventories; the concrete fixtures cover
conversion and point APIs with actual inherited
rational identities, not arbitrary selected-coordinate authentication or
source-goal quotation.
Complete certificate assembly still needs checked cell membership and coverage,
frozen context/history and reached arithmetic records connected to the existing
joint realization laws. This tranche supplies none of those checks, nor accepted
algebraic completeness. #10358 remains open for that integration and full-scope
evidence; no phase, base-family import or CI job is added. The
[original snapshot](data/hexrcf-native-samples/context.json) retains its seventeen
API/fixture and eight fresh ordinary-import checks at the recorded sources; it
does not attest these additional consumers or the clarified source-identity
boundary.
