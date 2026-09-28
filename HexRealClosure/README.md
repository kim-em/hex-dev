# Selected-root arithmetic and immutable bases

`Root.validate` checks a `Hex.SignDet.RawDescriptor Rat Nat` against its exact
version tag. The tag is a `Nat` and does not yet own a defining polynomial or
dependency graph. An `Expression d` stores a rational polynomial evaluated at the
real root selected by `d`. Its arithmetic is polynomial arithmetic; distinct
expressions can have the same value. `Expression.sign?` uses checked joint sign
determination. `Expression.inverse?` computes a gcd/cofactor split and a scaled
Bézout candidate, then checks its product at the selected root. A successful
inverse has a proof of its real value in
`adapters/HexRealClosureMathlib/SelectedRoot.lean`.
The companion also proves that the selected root lies in the computed cofactor
for a nonzero value, that squarefreeness makes this cofactor coprime to the
operand, and that the scaled Bézout candidate has product one. Once both sign queries
return, `inverse?` cannot fail its candidate check. The shared selected-sign producer
now has a success theorem under a lawful predecessor interpretation;
the generic arithmetic interface below uses it for total scalar sign.

```lean
let d ← Root.validate 7 raw
let a : Expression d := ⟨DensePoly.ofCoeffs #[0, 1]⟩
let sign ← a.sign?.toOption
let inverse ← a.inverse?.toOption
```

Both sign and inverse expose producer errors. `inverse?` returns `none` only
for a checked zero; a failed product check returns `InverseError.candidate`.
`Expression.transport` accepts checked `SignDet.Reencoding` evidence; its real
value is preserved. `Root.rebind?` revalidates the same root under a new context
version, and `Expression.rebind` transports a polynomial through that checked
conversion. `Expression.split?` combines cofactor re-encoding and rebinding;
`Expression.refine` transports stored values through both checks.
`Root.validate_context` rejects raw evidence from another context version.
The checked rebind preserves the selected value, but a version change alone
does not enforce context ownership or transport dependent objects. Full
context changes and nested transport remain separate. The `Expression` API
still exposes producer errors; `Element` below supplies a total rational-base
path.

Run `lake build HexRealClosure.Tests HexQuerySemantics` and
`python3 HexRealClosure/verify.py` from the repository root. The test uses
`(X²−2)(X−3)` with the root in `(1,2)`, plus a non-monic definition and a
checked factor split. The Python oracle computes exact arithmetic in ℚ(√2)
independently of Lean for 29 cases and is run manually; CI builds the Lean
`#guard` tests.
The companion proofs inherit the named #10389 admission in
`HexRealRootsMathlib.Tarski.check_rootSum`; no new admission is used here.

`adapters/HexRealClosureMathlib/Canonical.lean` uses the existing integer
root-list completeness theorem to show that every checked rational selected
root has a matching `RealAlgebraicNumber`, even when its defining polynomial
is reducible. `Expression.canonicalValue` evaluates the stored polynomial
using canonical real-algebraic arithmetic; its real value agrees with
`Expression.denote`; expression equality, addition, subtraction, negation,
multiplication, successful inversion, returned signs and checked refinement
agree. A checked zero inverse also has canonical value zero.

`Root.canonical?` clears denominators, enumerates the existing canonical real
roots and selects the entry matching the descriptor's interval and derivative
signs. `Root.toCanonical` returns that entry, and `Expression.toCanonical`
evaluates a stored polynomial using canonical arithmetic. The companion proves
the search always succeeds for a validated descriptor and that these
executable conversions equal the selected real value and the semantic
`canonicalValue`. The root-list search can be more expensive than local sign
queries; callers evaluating several expressions at one root can hoist
`Root.toCanonical`. The tests include a negative root with an unbounded lower
endpoint. This conversion does not replace the general tower representation.

`Element d` packs a rational polynomial with a canonical stored zero: a
polynomial that vanishes at the selected root is stored as `none`, and every
stored nonzero polynomial carries the result of that executable check. Ordinary
addition, negation, subtraction, multiplication, inversion and sign are total.
`Element.equal` packs the difference, so distinct stored polynomials can compare
equal; structural `==` only compares their stored forms. The companion proves
zero reflection, preservation of the arithmetic and sign, and value
preservation when an element is repacked through checked re-encoding, rebinding
or a factor split. The semantic `Value d` is the image subfield of the
canonical real algebraic numbers, and `Element.toValue` carries each total
operation to that lawful ordered field. For a literally monic, integral
defining polynomial, packing retains the remainder before
the selected-root zero check; the companion proves that this preserves the
selected value and integrality of clean inputs. Nonmonic definitions keep
their original representatives, as do monic definitions with fractional
coefficients. The retained remainder has degree below the defining polynomial.
Each uncached `Element.ofPoly` call searches the canonical root list, including
when the polynomial represents zero. On a stored nonzero element, uncached
`Element.value` and `Element.sign` also repeat the search. Use
`Root.Handle.Value` below for polynomial work that
reuses one selected-root search. The general tower's cost targets remain to be
implemented.

The companion's `polyValue` maps `DensePoly (Element d)` into polynomials over
the lawful `Value d` field. It reflects zero and preserves degree, coefficients,
arithmetic, derivative, evaluation, division and remainder, and supplies the
gcd association and extended-gcd Bézout identity. This uses the shared
noninjective polynomial interpretation rather than assuming raw coefficient
field laws. The runnable nested-coefficient example divides `Y²−2` by
`Y−α`; its remainder `α²−2` is semantically zero but not the zero rational
polynomial. It also checks extended gcd and differentiation.

`Element.transportPoly`, `rebindPoly` and `refinePoly` move every packed
coefficient through a checked root or context change. The companion proves
zero reflection, degree preservation and coefficientwise value preservation.
`polyDenote` maps `polyValue` into the shared canonical real-algebraic field.
All three transported polynomials have the same image there, even when their
stored coefficient representations differ. A runnable factor-split example
checks the three paths, including an interior zero coefficient and a square
coefficient that becomes constant after the split.

`Root.handle` searches for the checked descriptor's canonical selected root
once. `h.pack`, `h.add`, `h.mul`, `h.inv` and `h.value` reuse that root for
packed values. `h.equal` compares represented values by packing their
difference; structural `==` only compares stored representatives.
`Root.Handle.Value h` supplies ordinary arithmetic instances
for polynomial coefficients sharing the handle, so generic `DensePoly`
division also reuses it. Explicit target handles let polynomial transport
share one selected-root search across all transported coefficients. The
computational equalities to the original `Element` operations and the
companion's value theorems preserve their proved meaning. The handle is
indexed by its checked descriptor, so it cannot be used for a different
context version without a checked conversion. Bind it once as
`let h := d.handle` and pass `h` to cached values; writing `d.handle` afresh
at each call repeats the search.

`Yun.decompose` runs the specified finite recurrence over an executable
ordered field. `Yun.decomposeRaw` runs the same recurrence on packed tower
coefficients, where stored equality need not be value equality. The zero and
nonzero-constant cases, including acceptance by replay, have direct proofs.
For a positive-degree input whose monic gcd with its derivative is one,
the producer returns its leading coefficient and its monic associate with
multiplicity one, and this result is proved to pass replay. These squarefree
producer proofs use the same field instances as the executable API.
Runnable checks cover a
non-monic input, gaps in multiplicities, mixed zero and nonzero roots with a
fractional unit, a repeated irreducible quadratic, and coefficients in
`ℚ(√2)`.
The optional `Yun.check` recomputes the product and degree, checks positive
ordered multiplicities and nonconstant monic factors, and checks squarefree and
pairwise gcd conditions. Core lemmas extract those accepted conditions; the
Mathlib companion transports the product to mathematical polynomials and
proves that accepted rational factors are squarefree and pairwise coprime.
For every field embedding of ℚ, accepted factors cover exactly the roots of
the input, and each factor label is the multiplicity of its roots in the
input. This includes irrational real roots after mapping to ℝ.
`Yun.map_decomposeRaw` transports the raw recurrence through a zero-reflecting
coefficient map that preserves its arithmetic. The companion instantiates
this theorem for cached rational selected-root coefficients; their inverse
semantics retain the named `Tarski.check_rootSum` admission (#10389).
Arbitrary ordered coefficient towers still need their interpretation laws.
`Yun.Invariant.init`, `step` and `component` in the companion prove the
repeated-factor recurrence's pointwise root invariant over characteristic-zero
fields, including nonmonic inputs. Over an algebraically closed field, the
remaining-multiplicity weight decreases on every nonconstant round and starts
at the original degree. `Invariant.loop_weight` proves that any additional fuel
leaves the output unchanged; `initial_loop_bound` is its one-step corollary for
the initial state. The bound covers gaps with no emitted factor. These
proofs use ordinary kernel checking and have no admitted dependencies.
`decompose_bound` transports this result through an algebraic closure to every
characteristic-zero field. `ordered_bound` applies it to the public executable
field instances using a Mathlib field structure that preserves their arithmetic.
The public API requires `Std.LawfulOrderLT`; its natural casts are proved
injective, making the exclusion of positive characteristic explicit.
`decompose_root` proves that every input root appears in the actual producer
output with its original multiplicity, without a replay-acceptance premise.
`decompose_factor` proves monicity, positive degree and labels for every emitted
factor. `decompose_reconstruct` proves that their powered product reconstructs
the input, and `decompose_degree` proves exact degree accounting.
`decompose_factor_gcd` and `decompose_coprime` prove the executable squarefreeness
and distinct-label coprimality checks over every characteristic-zero field.
The raw recurrence also has strictly increasing labels and retains the input's
leading coefficient
without requiring field laws on stored syntax.
`decompose_sound` combines these results to prove that every public
ordered-field `decompose` result passes `check`, including repeated factors.
The generic producer proofs have no admitted dependencies and retain the field
operations used by the executable API. `decompose_packed` applies them to the
actual cached packed recurrence after coefficient interpretation; this
selected-root instantiation inherits the named #10389 inverse dependency.

`Bounds.find?` supplies the finite dyadic search for root isolation. It computes
coefficient absolute values once, then tries
`2^j` for `1 ≤ j ≤ 2 * (degree p + 1)` and checks the strict Cauchy coefficient
inequalities without coefficient division. `find?_exponent` records the finite
range of every returned value; `find?_eq` proves agreement with separate
candidate checks. `find?_none` records rejection of all candidates.
`find?_dyadic` interprets them as dyadic powers when natural casts are preserved.
The companion's `Bounds.check_sound` and `Bound.roots` prove that accepted
values give strict open endpoints for all roots in any ordered field. These
proofs reflect zero and preserve the actual coefficient arithmetic; they need
neither injective coefficient representations nor an Archimedean assumption.
`Bound.domain` supplies the shared Sturm domain from an accepted bound and
squarefreeness, including ordered root-free finite endpoints.
The 13 exact oracle fixtures include nonmonic and fractional inputs, strict
thresholds, inverse infinitesimals at two levels and close infinitesimal roots.
Run `lake build hexrealclosure_bounds_conformance`, then
`.lake/build/bin/hexrealclosure_bounds_conformance | python3 scripts/oracle/real_closure_bounds.py`.

A failed bound search is a request for whole-line BKR completion. It never
means that the polynomial has no roots. The bounded bisection and complete
isolation driver, general contexts and recursive transport remain unimplemented.

`deflate? p a` removes the factor `X-a` with the shared monic polynomial division.
`linearFactor a` stores the literal leading coefficient one, and the constructor
checks monicity before dividing. The coefficient interpretation proves this
finite check succeeds. The operation needs no coefficient division or inverse;
the shared monic kernel and its correspondence proofs preserve the input's
leading scalar even when the input polynomial is nonmonic.
It returns an opaque `Deflation p a` only for a nonzero input with zero
remainder and retains the computed quotient, including its leading scalar.
The companion proves success exactly when `a` denotes a root of a nonzero
input, exact factorization, a degree drop of one, and preservation of all other
roots. For squarefree inputs the quotient is squarefree and no longer vanishes
at `a`. `Deflation.domains` then supplies the two open Sturm domains after an
interior split; previous root-free endpoints remain valid. It does not reuse
old descriptors or counts. The driver still needs their checked transport or
recomputation and must retain the original multiplicities.

The generic deflation proofs use zero-reflecting coefficient interpretation
into a field and introduce no admissions. Packed selected-root execution tests
check cancellation of structurally different coefficient values. Thirteen
independent exact fixtures include nonmonic and repeated inputs, nonroot
rejection, inverse infinitesimals and removal at either of two infinitesimal
levels. Their SymPy oracle uses synthetic division in `QQ(epsilon, delta)`.
Run `lake build hexrealclosure_deflation_conformance`, then
`.lake/build/bin/hexrealclosure_deflation_conformance | python3 scripts/oracle/real_closure_deflation.py`.

For existing canonical number-field arithmetic and conversions, see the
[number-field chapter](../HexManual/Chapters/HexNumberField.lean) and
[real-algebraic chapter](../HexManual/Chapters/HexRealAlgebraic.lean).

## Ordered bases and checked value readers

`BaseContext.RealContext` constructs a real-constant prefix, starting at ℚ.
`RealContext.constant` looks up a name/version key in one fixed immutable
`Registry`. It requires the key's presence and erased progress for the exact
source returned by `parent.source key present`: coefficient bounds come from
the predecessor and constant bounds come from that registry entry. The
Mathlib companion's `RealContext.register` derives this progress from the
existing containment, width and relative-transcendence hypotheses. Its sign,
containment and zero-reflection theorems concern the actual constructed child.
The companion explicitly relates the executable and Mathlib field dictionaries:
use `HexRationalFnMathlib.ratField_eq` at ℚ and
`HexPolyMathlib.toGrind_fieldOfGrind` for subsequent native fraction fields.
In Mathlib-side code, select the executable rational dictionary before naming
the rational context or its fraction carrier:

```lean
local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
```

`RealModel.evalHom` embeds the native canonical carrier into ℝ;
`RealModel.linearOrder` and `strictOrderedRing` give its induced order and
ordered-ring laws. The resulting order supports infinitesimals after real levels.
`InfinitesimalModel.embed`, `linearOrder` and `strictOrderedRing` provide the
corresponding native Hahn model. `Element.infinitesimal_orderSign` gives sign
agreement for the next step, so it can be repeated at arbitrary finite depth.
The new infinitesimal is positive and below every positive predecessor element.

`BaseContext.Context.real` finishes that prefix. `Context.infinitesimal` then
adds any number of successive positive infinitesimals. The types prevent
adding another real constant after this step. These carriers use the existing
canonical rational-function fields; no coefficient-operation record or field
instance on selected-root syntax is introduced. The companion ties the child's
actual infinitesimal sign to the shared Hahn-series interpretation under the
predecessor sign hypothesis.

`BaseContext.Element ctx` is a nominal wrapper indexed by the entire immutable
context. Equal carrier types do not permit implicit context changes. Ordinary
arithmetic stays in one context; `a.embed` includes a predecessor value in its
new infinitesimal child, and `Element.embedConstant` includes a real-prefix
value in its registered child. Both embeddings preserve zero, one, addition,
subtraction, multiplication, total inversion and canonical equality. Their
companion theorems preserve signs and every `compare` result, including strict
inequalities. `a.equal b` tests canonical equality, while `a.inv?` rejects zero.

`a.write` produces finite recursive rational/fraction syntax with the full
base signature: the real keys in predecessor order and the infinitesimal
count. `Element.read ctx raw` first checks that literal signature, then checks
every level and denominator before canonical fraction construction. Round-trip
preservation and stale-binding rejection have kernel proofs. Readers are
relative to the application's fixed registry; identical keys in unrelated
registries do not establish provider identity. This is a value reader in a
supplied context. The catalog below reconstructs base contexts before reading
values or polynomials.

Run `lake build HexRealClosure.BaseTests HexRealClosureMathlib.BaseTests`.
The compiled examples exercise successive infinitesimals, explicit embeddings,
inverse infinitesimals, fraction normalization, round trips, incompatible
bindings, malformed level shapes and zero denominators. Companion tests apply
the semantic theorems to an executable named constant and two successive
infinitesimals, including positivity and comparison with every positive
predecessor element. A conditional two-constant construction verifies progress
from the exact first-level bounds, relative transcendence over that whole field,
second-level sign/zero/order correspondence, embedding comparisons, key order
and reader round trips. These base contexts do not yet contain algebraic levels.
Integrating general selected-root storage,
full dependency transport, algebraic context reconstruction, isolation and
exploration remains part of the tower implementation.

### Polynomials in a base context

`BaseContext.Polynomial ctx` owns all its coefficients in one immutable base
context. `Polynomial.ofCoeffs` accepts only values of that context; `coeff` and
`eval` return values in it. Ordinary polynomial arithmetic delegates to
`DensePoly` on the existing canonical coefficient carrier.

`p.embed` and `p.embedConstant` include every coefficient in the corresponding
infinitesimal or real child. Kernel proofs preserve coefficients, evaluation,
zero, one, addition, subtraction, negation, multiplication, stored array length
and degree. The shared coefficient-map implementation retains normalization
without scanning again for trailing zero coefficients.

`p.write` records a full base signature and a finite coefficient list.
`Polynomial.read ctx raw` checks that signature and every coefficient using
the context's scalar reader before constructing the polynomial. Round trips
and rejection of stale signatures have kernel proofs. Malformed fractions and
level shapes are rejected; valid trailing zero coefficients are normalized.
These are polynomials over the real/infinitesimal base, before algebraic levels.

Run `lake build HexRealClosure.BasePolynomialTests HexRealClosureMathlibTests`.
The tests include two infinitesimal levels, inverse-infinitesimal coefficients,
evaluation and coefficient transport, incompatible operand types, stale data,
malformed coefficients and a polynomial embedded into a named real context.

### Reconstructing base contexts

`BaseContext.Catalog registry` is an immutable catalog of real prefixes already
constructed against that fixed registry. Wrap a prefix with `RealPrefix.pack`
and install it using `Catalog.insert`. Insertion returns a new catalog and
rejects a path already installed; the rational prefix is always present.
Existing catalogs and their values remain valid. Kernel proofs show that
insertion preserves every other lookup.

`Catalog.read signature` resolves the complete ordered list of provider names
and versions, reuses the installed prefix, and constructs the specified number
of infinitesimal stages. It retrieves the progress premises already stored in
the prefix, rather than deciding convergence or relative transcendence from
serialized data. A provider present in the underlying registry is insufficient
until its full prefix has been installed. No lookup uses a shortened name or a
hash, and reconstruction stays relative to the same immutable registry.

`Catalog.readElement raw` and `Catalog.readPolynomial raw` reconstruct the
context first, then use its checked scalar or polynomial reader.
`PackedContext.readElement` also checks bindings when reusing a supplied packed
context; `readPayload` explicitly accepts unbound coefficient syntax. Their packed
results retain that context and a value indexed by it. `PackedElement.sign`
uses its own context's native sign. Malformed recursive coefficients, missing
paths and changed provider versions are rejected. Kernel round-trip proofs
return the original context and value whenever that exact prefix is installed.
`PackedContext.reconstruct` decomposes every ordinary native context into its
actual real prefix and depth. `Catalog.read_self` therefore needs only the
installed-prefix lookup, without a caller-provided reconstruction equality.
`insert_isSome_iff` and `lookup_of_insert` describe the concrete catalog returned
by insertion. The compiled stage constructor uses a proved tail-recursive loop.
Proofs are not serialized.

Run `lake build HexRealClosure.BaseCatalogTests HexRealClosureMathlibTests`.
The examples exercise rational reconstruction, two infinitesimal levels, an
actual named real followed by two infinitesimals, immutable catalog extension,
duplicate paths, changed versions, missing registrations, malformed fractions,
and kernel round trips for a concrete installed named-real catalog. These
readers cover the real and
infinitesimal base stages. Algebraic descriptors, dependency transport and
complete algebraic context reconstruction remain part of the tower work.

### Arithmetic over general selected-root predecessors

`BaseContext.Context.adjoin descriptor` adjoins a root over an exact immutable
real/infinitesimal base. `Algebraic.Context.extend descriptor` adjoins another
root over the preceding algebraic context. Both derive the storage predicate
from their predecessor. The general backend
`Algebraic.Context.adjoin descriptor cleanCoeff` also supports ordinary
coefficient carriers with an explicit storage predicate.

`Algebraic.Element ctx` owns its complete extension context and stores a unique
zero or a nonzero polynomial with its checked sign. The context computes its
literal-monic/clean reduction decision once. Packing retains the actual monic
remainder when eligible, then performs one shared selected-root sign query for
nonconstant polynomials; constants use the predecessor sign directly. Reading
a stored sign reuses its result. Nonmonic or unclean definitions retain the raw
representative. A leading coefficient that denotes one but differs structurally
from literal one does not enable monic storage.

Ordinary addition, subtraction, negation, multiplication, inversion and
division operate on these values. Inversion computes the defining polynomial's
local gcd with the operand, takes the complementary factor, and scales the
actual one-sided Bézout coefficient. `ofCoeff` explicitly includes a predecessor
value. `equal` and `compare` use the selected value; structural equality compares
stored forms. `inv?` rejects canonical zero.

The companion `adapters/HexRealClosureMathlib/Algebraic.lean` proves zero
reflection, sign, comparison and arithmetic preservation for a zero-reflecting
predecessor interpretation into an ordered real closed field that preserves
the relevant ordinary operations. Injectivity is unnecessary. Producer success
proves the scalar adapter's explicit internal-error branch unreachable under
these hypotheses. Inverse correctness derives the cofactor root and constant
gcd properties of the actual computation. `AlgebraicTower.lean` instantiates the
second level's interpretation using the first level's proved operations,
including zero reflection, sign and gcd/cofactor inversion.

`AlgebraicValue.lean` defines the image subfield `Value ctx`, with lawful field
and order instances inherited from the ambient field. `Element.toValue`
preserves arithmetic and sign, is surjective, and identifies exactly the
representatives accepted by executable `equal`. `Context.quotientEquiv`
identifies the semantic quotient of storage with this field.
`quotientField`, `quotientOrder` and `quotientOrdered` transfer lawful field and
order structures to that quotient; `quotient_compare` ties the executable
comparison to its order. The `quotient_add`, `quotient_mul`,
`quotient_inv` and related equations prove descent of the actual packed operations. Stored
representatives have no asserted field instance.

`BaseContext.Element.isClean` checks integral rational coefficients and
recursively denominator-one polynomials through every real and infinitesimal
stage. `Algebraic.Element.isClean` checks its stored polynomial's predecessor
coefficients. `BaseClean.lean` proves closure of the actual recursive base
predicate under zero, one, addition, subtraction and multiplication, and derives
clean packing for the native base constructor. `AlgebraicClean.lean` proves that
these closure properties preserve coefficients through actual polynomial
arithmetic and monic division, retained reduction and packed arithmetic. `Context.extend_clean`
proves clean packing at the next algebraic level from those preceding-operation
closure theorems; `extend_closed` retains all five closure facts for further levels. They
need no field laws on stored syntax and have no admitted dependencies.

Run `lake build HexRealClosure.AlgebraicTests HexQuerySemantics` and
`python3 HexRealClosure/verify_algebraic.py`. Executable examples cover reducible
monic and nonmonic definitions, noncanonical equal values, local splitting
inversion and cancellation, square roots of infinitesimals, and two reducible
algebraic levels with ordinary coefficient operations. The independent exact
oracle computes arithmetic and polynomial remainders in a quartic field and
checks the positive selected infinitesimal root in Laurent germs. It runs in
the existing CI job. The Mathlib-free `hexrealclosure_bench` includes a functional
`runGeneral` timing anchor for validation, packing, cancellation and inversion;
it makes no scaling claim.

The semantic sign, inverse and quotient proofs inherit only the existing named
`HexRealRootsMathlib.Tarski.check_rootSum` admission owned by #10389. Constructors,
cleanliness and the core introduce no admission. These interpretations are
conditional on an ambient ordered real closed field, not an existence proof.

The remaining tower work includes the recursive algebraic dependency catalog,
context enlargement and transport, general root isolation and multiplicities,
rational delegation agreement and a compatible real-closed union construction.
Repeated nonconstant queries still rebuild the shared prepared domain and BKR
table; a reusable selected-sign handle is requested from #10377. Formal tower
performance evaluation, including nested sign/zero counts and coefficient
growth, remains open.

### Recursive tower contexts and checked readers

`Tower.Chain` completes the staged base before adjoining algebraic roots. Each
root is validated over the entire predecessor carrier using its actual sign
and full signature. The constructors derive ordinary coefficient operations,
recursive cleanliness and the coefficient codec; raw algebraic carriers have
no ring or field instance.

`Tower.Context` packages such a chain with its value type. `Context.adjoin?`
accepts the exact context-bound descriptor and returns an `Extension` containing
the new context, its selected generator and the actual constant-polynomial
embedding. Old values keep their owning context. The optional failure checks
structured serialization shape; descriptor acceptance is already established.
The returned extension retains its literal frame, the proof of its complete
binding, and `Context.adjoin_spec` identifies the native child, embedding and
generator without unfolding the private constructor.
These context packages live in `Type 1`; `Option.bind` can connect their results
to ordinary scalar computations across universe levels.

A `Tower.Signature` contains the complete base signature and every ordered
algebraic frame. Each frame retains the literal head, interval, Thom slots and
shared replay graph, including all witnesses. References to the exact parent
are encoded relative to the enclosing full signature. Hashing only indexes the
shared graph's exact node comparisons. Identity uses structured data and does
not depend on JSON printing, byte parsing, short names or hashes.
Signature and relative context-reference codecs have proved structured
roundtrips. Parsing a signature supplies an identity, not a validated root.
Exact equality uses the core pointer shortcut for shared immutable signatures;
context hashes are constant when indexing replay nodes with one predecessor.
Literal arrays are emitted by an accumulator with `Array.push`.

`Tower.Catalog` is an immutable catalog of caller-constructed validated prefixes.
Insertion rejects rebinding. Its separate base catalog supplies real search
progress and reconstructs infinitesimal stages. Unknown algebraic signatures
are rejected until their native prefix is installed. Readers retrieve the full
context first, then decode a scalar or polynomial in that context; returned
packed values retain their owning context.

The structured codecs have proved literal write/read roundtrips. Nonzero
algebraic payloads retain both the polynomial and cached sign; their reader
checks predecessor coefficients and recomputes the sign in the exact context.
It restores the stored polynomial without arithmetic repacking, preserving
literal certificate coefficients that are semantically equal but structurally
different. Arithmetic still uses `Element.ofPoly` and retains its computed
monic clean remainder. Polynomial readers reject trailing literal zeros.

Run `lake build HexRealClosure.TowerTests HexRealClosureTests`. The examples build
three actual algebraic levels, use their explicit embeddings, read old values
after extensions, restore a noncanonical coefficient, and reject stale or
unknown bindings, forged signs, zero claims, trailing zeros and malformed base
payloads. The core roundtrip proofs introduce no admission. General persistent
refinement, transport of later descriptors, interpretation of arbitrary towers,
complete isolation and the real-closed union remain open.
Reconstructing new validated algebraic levels from serialized frames and
proving that native frame serialization always succeeds (so the optional
adjoin facade can become total) also remain open.
