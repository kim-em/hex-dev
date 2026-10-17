# Selected fixed-field source authentication

`FieldSelection.prepare` constructs a coefficient selector from an existing
checked rational root and the actual reduced coordinates of elements of its
`QAdjoin` field. The generator occupies coordinate zero; the original
coefficients follow in order. `authenticated` proves that the selector holds
at the original `Coefficients.ofField` interpretations, using the owner's
chosen-generator and coordinate interpretation laws. No new field
representation, minimal-polynomial search for each coordinate, or assumed
tuple identity is introduced.

`SourceSelection` represents inherited coordinates, checked rational roots and
rational polynomials in earlier coordinates. The earlier index has type
`Fin n` before a coordinate is appended, excluding forward references and
cycles. Its formula uses the shared integer schema. `real`, `formula_real`
and `formula_iff` reduce source authentication to coordinatewise real
equalities. `unique` identifies the whole tuple once the actual origin fixes
its inherited coordinates. A polynomial equation alone does not select a
conjugate.

The `exists_real` law composes this generated uniqueness proof with the existing
finite joint reader. Its conclusions retain coefficient identities, sample,
matrix, every supplied original nonzero divisor, negation closure, specialized
polynomial sizes and inherited-origin agreement. `not_forall` supplies the
universal counterexample route with the same source authentication and guards.
The adapter does not infer or discard source guards here: callers supply the
original list, whose signs are explicit checked hypotheses.

`FieldSelection.nativeValues` uses the actual owner's number-field presentation
to pack the coordinates. `nativeValues_real` and `native_authenticated` establish
their selected interpretation. `matrix_correct` shifts the original formula
past the prepended generator, preserving coefficient order, the last quantified
variable and every domain guard atom. Inputs to this builder already belong to
one selected primitive field; independent-field conversion remains with the
existing preparation and common-field owners.

The concrete native regression builds its selector from `-a`, `2`, and
`a*a-1` in the selected square-root field. It uses the existing native
square-root section and proves agreement with those source coordinates.
Both computed coordinates occur in the matrix. One real reader satisfies
the full matrix and the two original divisors `2-sqrt(2)` and `1+sqrt(2)`.
The exported witness uses that reader's matrix conclusion. A separately
evaluated row refutes `forall x : Real, x < 0`, retaining both guards at its
counterexample reader. Swapping the computed native coordinates fails the
selector alone, in an ordinary interpretation proof and a compiled row control.
An inherited native case consumes the actual origin identity for `2`.
Separate controls cover a wrong conjugate, an actual source-coordinate swap,
freely varying inherited values, a computed generator, non-integral rational
coordinates and an incorrect chained coordinate. Two-root position controls
are parametric in supplied checked roots and their distinctness proof.

The public `FieldSelectionConformance` module executes `NumberField.present?`
and `FieldSelection.nativeValues` on those actual `QAdjoin` coordinates. It
uses the packed point `1`, checks that it differs from the selected generator,
checks the shifted original matrix, and isolates selector-only swap rejection.
Its ordinary proof presentation is a successful result of the same factory by
the owner's existence law. `FieldSelection.true_real` composes its true row
with the original matrix interpretation to prove a real point theorem.
This law retains every supplied nonzero guard; the concrete factory point
theorem uses an empty guard list. The earlier finite-reader case separately
retains its two supplied guards. Neither case claims to collect divisions
from original source syntax. Public and public meta imports suffice for this
module, without `import all` or a legacy fixture import.

The rational source descriptor is reconstructed using `RootQuote` in an ordinary
public module. Its original reader equation is checked, not taken from a
compiled verdict. A separate quoted binding reader and the owner's
`Dag.descriptor_raw` law bind the exact supplied subject. The positive
square-root identity follows from that head and strict interval. This removes
the duplicate descriptor acceptance check from the older ordered-selection
fixture. The root and binding quotations charge 308,555 and 60 proof nodes,
respectively; these are syntax counts, not unique DAG-node or sharing results.

The fresh generic audit rechecks 14 exported theorem bodies. A separate audit
rechecks 218 reachable theorem bodies and 50 definitions from the six named
source-selection modules, including generated proof leaves; 244 checks have
nonempty reduction traces. It checks complete root axiom closures against
the standard three axioms and rejects the existing native-producer denylist
unchanged. Temporary checked copies are discarded. Legacy native fixture
construction is outside this six-module body scope and inside the complete
axiom closure. These checks do not claim a public frozen full-signature reader.

The [manual](../HexManual/Chapters/HexRCF/NativeSources.lean) includes checked
builder examples and the source-selection boundary. The
[evidence record](data/hexrcf-source-selection/context.json) binds the exact
sources, build logs, rendered-page inspection and retained scripts. Lean/Lake
and browser work runs serially under an aggregate 32 GiB limit with no swap;
Lean uses two threads. Reused-dependency build observations validate these
examples and do not establish a speedup, complexity ladder or physical sharing.
The final inspection opens eight captures and checks nine changed-section
targets at each of 1440 and 390 pixels. Their maximum measured overflow is
zero on desktop and one pixel in the first narrow code block; the wrapped
builder has none. This is local section evidence, not a zero-overflow claim
for the entire manual. The earlier five-pixel builder failure and its captures
are retained with the unchanged greater-than-one-pixel rejection threshold.

This is a partial integration under #10358. It does not discover arbitrary
original source coefficients, recursive provider/predecessor histories or a
frozen context, produce complete cell coverage, install a general tactic path,
or prove accepted algebraic completeness. The existing public full-signature
codec request remains with [the #10378 owner](https://github.com/kim-em/hex-dev/issues/10378#issuecomment-6230331731).
Strict compiled rejection of arbitrary missing arithmetic records, native
inverse/xgcd stress, remaining conversion/joint-realization integration and
the rest of the issue's conformance/manual evidence also remain. #10358 stays
open; the base umbrella still imports no real-closure family modules.
