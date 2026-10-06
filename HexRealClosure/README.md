# Selected-root arithmetic and immutable bases

The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-real-closure)
explains the public computation and its mathematical hypotheses with checked
examples. This is an unreleased development library in `hex-dev`.

`Root.validate` checks a `Hex.SignDet.RawDescriptor Rat Nat` against its exact
version tag. The tag is a `Nat` and does not yet own a defining polynomial or
dependency graph. An `Expression d` stores a rational polynomial evaluated at the
real root selected by `d`. Its arithmetic is polynomial arithmetic; distinct
expressions can have the same value. `Expression.sign?` uses checked joint sign
determination. `Expression.inverse?` computes a gcd/cofactor split and a scaled
Bézout candidate, then checks its product at the selected root. A successful
inverse has a proof of its real value in
`adapters/HexRealClosureTheory/SelectedRoot.lean`.
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
The companion proofs use the shared theorem
`HexRealRootsTheory.Tarski.check_rootSum` and only Lean’s standard logical axioms.

`adapters/HexRealClosureTheory/Canonical.lean` uses the existing integer
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

`h.packQAdjoin` accepts exact `QAdjoin h.canonical.toAlgebraic` coordinates
and packs them using the cached selected root. The generator in the input type
prevents coordinates for a different algebraic root from being used with this
handle. `h.packQAdjoinOf` accepts coordinates for a generator proved equal
to the selected one. The Mathlib-free `h.packQAdjoin?` checks generator
identity before packing externally held coordinates. The companion proves
that it accepts exactly the selected generator and returns the same packed
result as `packQAdjoinOf` with the corresponding equality proof. Accepted
results preserve the selected value and pass the checked real conversion. It also
proves preservation of addition and multiplication at the represented value.
A runnable example distinguishes the selected √2 from the other roots of a
reducible descriptor, compares field and packed multiplication with different
stored polynomials, checks the field result through its own isolation, and
checks rejection of a conjugate and a shifted generator, zero packing, and
the rational selected root. A separate
cubic regression constructs `∛2` from its own isolation, checks that its
fixed-field coordinate is accepted by the independently validated real-closure
handle, and compares exact division and multiplication with the selected
real-algebraic value.

### Roots over an existing real number field

`NumberField.roots generator context p` uses the complete HexRealClosure
producer directly on `QAdjoin generator.toAlgebraic` coefficients, with the
existing interval sign operation for that selected embedding. It retains the
zero polynomial's `all` case, ordered point/descriptor roots and their original
positive multiplicities. `NumberField.roots?` exposes producer diagnostics.
The input generator is a checked `RealAlgebraicNumber`; an external
`AlgebraicNumber` first enters through `RealAlgebraicNumber.ofAlgebraic?`.

For example, with a checked positive cubic generator `a = ∛2`:

```lean
let alpha := a.toAlgebraic.toQAdjoin
let y : DensePoly (QAdjoin a.toAlgebraic) := DensePoly.ofList [0, 1]
let quadratic := y*y - DensePoly.C alpha
let result := NumberField.roots a 10378 (quadratic*quadratic*(y-1))
```

The roots are `-2^(1/6), 1, 2^(1/6)` with multiplicities `2,1,2`.
Selected entries support the existing `descriptor.buildSigns` and
`Algebraic.Context.adjoin` arithmetic; comparison uses `entry.root.compare`.
The companion's `NumberField.value_complex` retains the entire selected
complex value in ℝ, and `roots_success`, `roots_all`, `roots_spec` and
`roots_sorted` prove totality, the zero case, exact multiplicities and ordering
for every polynomial in the actual field coordinates. The public
`value_add/sub/mul/div/neg/inv/nat` laws support further selected-entry proofs.

Run `lake build hexrealclosure_number_field_conformance` followed by
`.lake/build/bin/hexrealclosure_number_field_conformance`. Its compiled cubic
fixture exercises the zero case, repeated roots and a negative nonmonic input,
selected signs, strict comparison and inversion at the returned roots. The
independent FLINT qqbar oracle reconstructs the selected cubic embedding and
checks the original polynomials, all roots, labels, intervals, derivative words
and query signs. A second cubic fixture selects the middle root of
`X³−3X+1`, which has three real embeddings including two positive ones.
Each generator carries its actual isolating bounds, so the oracle and
conjugate-swap mutations distinguish embeddings with the same sign.

The same executable computes a common field for the selected positive values
`a = √2` and `b = √3` using `QAdjoin.common`, then runs `NumberField.roots`
on `Y³(Y²−b)²(Y−a)` in the returned coordinates. It returns
`−3^(1/4), 0, 3^(1/4), √2` with multiplicities `2,3,2,1`.
The zero entry uses the point-root branch. FLINT independently checks the
selected primitive quartic generator, both original inputs and their coordinates before
checking the input polynomial and its complete root list. All fixtures' selected
entries also record the sign of `(root−3)⁻¹ + 1/2`, which varies across the roots;
the oracle computes this value independently.
The companion's `NumberField.common_value` proves that every returned common-field coordinate
retains the corresponding input's entire complex value when the computed
common generator passes the real check.

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
Theory companion transports the product to mathematical polynomials and
proves that accepted factors over an ordered field are squarefree and pairwise
coprime. After any field map, accepted factors cover exactly the roots of the
input, and each factor label is the multiplicity of its roots in the input.
This includes irrational real roots of rational inputs after mapping to ℝ.
`Yun.map_decomposeRaw` transports the raw recurrence through a zero-reflecting
coefficient map that preserves its arithmetic. The companion instantiates
this theorem for cached rational selected-root coefficients; their inverse
semantics use the proved `Tarski.check_rootSum` theorem.
`Tower.Model` below propagates these interpretation laws through finite native
root towers over a supplied ordered real-closed ambient field.
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
selected-root instantiation uses the proved root-sum theorem through
inverse soundness.

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
means that the polynomial has no roots. Bounded bisection and complete isolation
are described elsewhere in this README. Assembly of the full requested live
dependency closure remains open; checked conversion through a finite suffix
and `Context.origin` extraction of one context’s stored base and root suffix
are available. Selecting the dependency closure from requested expressions
remains open.

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
Theory companion's `RealContext.register` derives this progress from the
existing containment, width and relative-transcendence hypotheses. Its sign,
containment and zero-reflection theorems concern the actual constructed child.
The companion explicitly relates the executable and Mathlib field dictionaries:
use `HexRationalFnTheory.ratField_eq` at ℚ and
`HexPolyTheory.toGrind_fieldOfGrind` for subsequent native fraction fields.
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

The companion's `RealContext.Interpretation` binds a real embedding, computed
signs and coefficient containment to one actual native prefix.
`Interpretation.rational` initializes it; `Interpretation.register` derives the
new prefix's search progress and coefficient agreement from the parent model
and the new provider's containment, width and relative transcendence.
`Interpretation.hom_unique` proves that the prefix's shrinking native bounds
determine the embedding uniquely.

`RealPrefix.Model` retains the actual native chain together with all its
provider-derived predecessor interpretations. Start with `Model.rational`
and extend through `Model.register`. The registration requires the new
provider's analytic premises; it derives predecessor agreement and progress.
`Model.register_map` proves that the actual native predecessor-inclusion
producer succeeds and preserves every coefficient's real value.
The development adapter `HexRealClosureTheory.BaseModel` packages the same
prefix interpretation as a `Tower.Model`; its `towerModel_value` theorem
identifies every stored base coefficient with the original real embedding.
`RealChain.Realization.embedding` follows that producer's actual maps through
all stored real steps. `Chain.Realization.embedding_sign` adds the staged
infinitesimals, preserving each old formal variable and every native sign.

The standalone `Tower.BaseInclusion.make?` caches a native coefficient map
when the source's real keys form a subsequence of the target's path and
its infinitesimal depth is no greater. It preserves and reflects canonical
zero and preserves the native field operations, including total inversion.
Its companion `BaseInclusion.sign` derives sign preservation from the two
provider-derived staged realizations. This includes proper non-prefix subsequences,
which the shared tower assembly also accepts through `Inclusion.base?`.
The shared-assembly section below describes this transport and the remaining
coherent owner and cache factory.

`RealChain.subsequence?` and the packed `RealPrefix.subsequence?` accept a
source whose keys occur in order within an already constructed target chain.
They preserve matching formal variables and include omitted target constants
without polynomial gcd work. For example, the independently registered path
`[β]` enters `[α, β]`. `subsequence?_isSome` proves the exact key check;
`subsequence?_self` proves that a self map is the identity.
The companion `RealPrefix.Model.subsequence_map` derives preservation of every
real coefficient from both registered models. `RealChain.Realization.subsequence_sign`
derives agreement of their actual native signs. `RealContext.provider_unique`
uses stored approximation progress to prove that a registered provider has at
most one real value relative to its interpreted predecessor. The build-only
`SubsequenceTests.insert_before` constructs the target
with `Model.register`, checks this non-prefix inclusion and proves that the
prefix-only producer rejects it.

The target retains its own relative-transcendence premises and progress proofs
for each exact predecessor. The subsequence factory does not construct a joint
target from separately supplied providers, or permute a real-key path.

`Chain.subsequence?` and `PackedContext.subsequence?` retain successive
infinitesimals in their original order while admitting the real-key subsequence.
`Tower.BaseInclusion.make?` uses this broader native check. The companion
derives the source realization from the target provider values and the source
chain's stored progress proofs, so canonical owner lookup and shared gathering
accept these inclusions without a separate source interpretation or agreement
premise. `BaseTests` executes empty, self, incompatible-version and decreasing
key checks, plus preservation of the real variable and an old infinitesimal
when another target infinitesimal is added. Successful non-prefix gathering
is checked by `SubsequenceTests.gather_insert_before` for a complete algebraic
suffix under its explicit provider premises; it is not an instantiated pair of
independent providers.

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

Run `lake build HexRealClosure.BaseTests HexRealClosureTheory.BaseTests`.
The compiled examples exercise successive infinitesimals, explicit embeddings,
inverse infinitesimals, fraction normalization, round trips, incompatible
bindings, malformed level shapes and zero denominators. Companion tests apply
the semantic theorems to an executable named constant and two successive
infinitesimals, including positivity and comparison with every positive
predecessor element. A conditional two-constant construction verifies progress
from the exact first-level bounds, relative transcendence over that whole field,
second-level sign/zero/order correspondence, embedding comparisons, key order
and reader round trips. These base contexts do not yet contain algebraic levels.
Selected-root storage and checked reconstruction of algebraic prefixes are
provided below, together with complete isolation. Full dependency transport
and exploration remain part of the tower implementation.

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

Run `lake build HexRealClosure.BasePolynomialTests HexRealClosureTheoryTests`.
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

Run `lake build HexRealClosure.BaseCatalogTests HexRealClosureTheoryTests`.
The examples exercise rational reconstruction, two infinitesimal levels, an
actual named real followed by two infinitesimals, immutable catalog extension,
duplicate paths, changed versions, missing registrations, malformed fractions,
and kernel round trips for a concrete installed named-real catalog. These
readers cover the real and infinitesimal base stages. The algebraic prefix
reader below reconstructs validated root levels; transport across multiple
live contexts remains part of the tower work.

## Capped isolation and root assembly

### Finite bisection nodes

`Bisection.bisect? sign p lower upper` uses the deterministic arithmetic
midpoint of a finite interval. A nonroot cut retains the original polynomial.
A root cut performs checked exact linear deflation and retains its computed
quotient. Both open subintervals are freshly prepared
against that active head. Cuts at or beyond an endpoint are rejected by
`Bisection.split?`.

The companion proves native midpoint interpretation, success for every
admissible finite interval and validity of both returned prepared domains. These results
use only the standard three axioms and ordinary coefficient interpretations;
no field instance on raw syntax is required. Native examples exercise regular
and root cuts, nonmonic and fractional heads, root-free deflated endpoints,
root counts and invalid inputs.

The capped frontier below composes these finite nodes and recomputes pending
evidence after deflation. Descriptor completion and factor assembly are described below.

`Mode.removed` returns the emitted coefficient point or `none`. The companion
`BisectionRoots` proves that roots in the original interval are exactly the
removed point and roots in the two actual returned open intervals. Neither
interval includes the cut. It also proves equality of the interpreted leading
coefficients, without asserting raw equality of noncanonical representatives.
The RationalFn fixtures use normalized coefficients; packed deflation tests
separately exercise structurally different representatives.

The existing deflation conformance driver also emits 21 bisection cases,
including nonmonic and fractional rational heads, zero/repeated inputs,
constants, roots on both sides of regular and root cuts, negative lower
endpoints, a linear root cut with constant quotient, close infinitesimal roots,
inverse infinitesimals and two successive
infinitesimal levels. FLINT exact algebraic roots independently check rational
counts. SymPy factorization over `QQ(epsilon, delta)` and the successive positive
infinitesimal order check the linear-factor cases. The oracle checks the
midpoint, exact removed value, active and returned heads, returned endpoints
and independently computed counts; their sum also satisfies root coverage. Its rejection tests detect stale heads, scalar loss, missing or
invented cut roots, incorrect nested ordering and invalid input acceptance.
These cases exercise one bisection node; the complete isolation API is described
below. Simultaneous ordinary-real realization remains a separate requirement.

### Capped bisection frontier

`Bisection.Frontier.prepare?` checks a finite input interval.
`Frontier.refine?` then spends at most `2 * (degree p + 1)` nodes, choosing the
first retained cell whose checked count exceeds one. The policy is depth-first:
new halves precede pending cells, so an inseparable cluster can spend the
allowance before another cluster is refined. Call `refine?` once after
`prepare?`; repeating it grants a new allowance. It returns the current
head, emitted coefficient roots and every remaining open cell. Count-zero and
count-one cells remain available; unresolved cells request BKR completion.
This frontier is an intermediate result, not a complete `RootSet`.

Each cell retains a count computed once from its actual prepared domain, with
an equality proof tying that count to the shared query. A regular cut retains
unchanged pending cells. A root cut recomputes every pending domain and count
against the quotient, including previously retained count-one cells. All cells
are bound to one current head. `Cell.bisect?` uses `splitPrepared?` on the
selected cell's actual domain. A regular cut retains its validated derivative
chain in both halves and checks their new endpoints through the shared
`PreparedDomain.withEndpoints?` API. A root cut prepares the changed quotient
head afresh. `splitPrepared?_eq` and `Cell.bisect_eq` prove equality with the
complete results of fresh splitting, including the returned domains.

The companion proves construction success under coefficient interpretation,
the node bound, exact root coverage, disjoint retained intervals, distinct
emitted values and exclusion of emitted roots from every later active head.
The capped entry theorem also proves that traversal stops only when every
cell has count at most one or the node allowance has been spent. These
structural proofs use only the standard three axioms.
`BisectionCounts` proves that retained counts plus emitted roots equal the
original interval's root count, under an exact three-valued sign interpretation.
This count theorem uses the proved shared query-soundness theorem and only
the standard three axioms.

Fifty-eight native checks cover later root cuts with earlier count-one and
count-zero and multi-root cells, two emitted roots,
positive/negative/fractional scalars,
early stopping and close infinitesimal roots retained after the node allowance.
Fifteen additional exact conformance rows check whole frontiers. The existing
FLINT/SymPy oracle verifies scalar-preserving deflation, actual pending heads,
root counts, emitted roots, the internal node allowance and the retained
intervals' lack of gaps or overlaps. It independently reproduces the prescribed
cell selection and cuts. Rejection tests cover stale heads, missing cells,
wrong counts, gaps, overlaps, duplicated or invented roots, premature stopping
and spending the allowance on the wrong cell.

Regular cuts avoid fresh derivative-chain preparations for both halves and
compute their root counts using `countPrepared` on those retained chains.
`countPrepared_eq` ties every stored count to the ordinary query-one result.
Root cuts
still prepare both quotient domains and recompute every pending domain and
count, including count-zero cells. No timing improvement is claimed.

The frontier feeds descriptor completion and the complete generic root producer
below. Native root entries, their coefficient embeddings and the compatible
presentation quotient are described below. Automatic dependency transport and
simultaneous ordinary-real realization remain requirements of the full tower.

### Complete roots with finite isolation choices

`Isolation.Policy` offers `standard`, `bounded` and `whole`. The standard
choice uses the finite bound search and bisection cap. The bounded choice
omits bisection; the whole-line choice omits both optimizations. Each choice
completes every retained cell with the existing BKR descriptor producer.
No choice asks for a coefficient precision threshold.

`Roots.Policy.roots policy sign context p` applies the choice to every actual
Yun factor, restores extracted zero with its original multiplicity and sorts
all roots with their attached labels. Its diagnostic form is `roots?`.
`RootPolicy` proves total success, the separate zero `all` case, exact root
coverage and multiplicities, strict ordering and equality of the interpreted
ordered value and multiplicity lists between policies. The standard policy is exactly the existing default
API, including checked diagnostics.

For native context-indexed values, use `context.rootsWith policy p` or
`context.rootsWith? policy p`. Every selected entry retains its actual child
context, root value and predecessor coefficient embedding. `TowerRootPolicy`
proves the same complete RootSet contract under the context's ambient model.

`RootPolicyConformance` exports 33 exact outputs covering all three policies,
zero, constants, nonmonic repeated factors, zero extraction, root-free
factors, cut points, an inverse infinitesimal, distinct-label close roots in
separate Yun factors, and squarefree and equal-label close pairs within one
factor. The independent Z3 oracle checks complete ordered root sets and
original multiplicities. It independently decomposes the input over Z3's
exact real-closed field and identifies every selected head with its labelled
monic Yun factor after zero extraction and coefficient-point deflation,
including any nonreal factors of that labelled factor. Rational decomposition cases also agree
with FLINT's independent squarefree factorization. The oracle checks whole-line
endpoints, the first accepted Cauchy bound and its fallback, and the permitted
point and subdivision behavior. Mutations reject extra complex factors,
incorrect leading scalars and omitted roots of the same multiplicity even
when root selection and the first bound remain valid.
`RootPolicyTests` checks native root equations,
exact ownership, order, labels and policy agreement over rational and already
adjoined algebraic parents through both native materialization APIs.

### Bound selection and whole-line dispatch

`Isolation.search? sign p` follows the fixed finite dyadic bound policy. On an
accepted bound it prepares `(-B, B)` and calls capped refinement once. If every
bound candidate fails, it prepares the shared Sturm producer on the whole line.
The private `Search` constructor retains the actual dispatch trace; its bounded
route contains the accepted bound and actual returned frontier, and its whole
route contains a domain bound to the exact input head, sign and infinite
endpoints. Domain failure remains explicit and never means an empty root set.

Under a zero-reflecting coefficient interpretation preserving arithmetic and
three-valued signs, every nonzero squarefree input has a successful search.
The returned route retains exactly all original roots, and whole-line domains
are admissible for their exact input. Coverage is stated using the actual stored
whole-line head and endpoints. `Search.bounded_spec` exposes bound selection,
node allowance, disjoint cells, distinct emitted values excluded from the active
head and the stopping condition. These proofs use only the standard three
axioms. The result is prepared input for descriptor completion, rather than an
executable complete root set; it does not assert mathematical root ordering,
general descriptor-producer success or restoration of multiplicities.

Native checks cover positive, negative and fractional scalar inputs,
a large rational root beyond every bound candidate, inverse infinitesimal roots
at two levels, root-free whole-line input and rejection of zero or repeated
roots on both routes. Independent exact fixtures check dispatch and the full
bounded frontier or whole-line
domain. The FLINT/SymPy oracle recomputes the first accepted bound, checks the
selected route, and verifies actual head/endpoints and root counts. It also
checks that the accepted bound contains every real root. Its rejection
tests detect wrong routes, later bounds, stale heads, finite whole-line endpoints,
wrong counts and failure on valid input. Native root-count correspondence consumes the proved
root-sum theorem.

### Exact deflation provenance

`BisectionFactor` proves that the original polynomial is exactly the product
of the emitted linear factors and the actual returned active head. The proof
uses each actual cut's stored quotient and the traversal's returned-head and
emitted-list equations. It preserves the original leading coefficient without
monicizing the input or asserting equality of coefficient representations.
`IsolationFactor` exposes this identity for a checked bounded search, together
with leading-coefficient preservation and the degree identity: original degree
is active-head degree plus emitted-root count. The degree identity requires a
nonzero active head, supplied by the existing domain companion.

These algebraic proofs need a zero-reflecting field interpretation preserving
one, subtraction and multiplication. They need no root-count theorem, root
ordering, squarefreeness or sign interpretation, and their axiom guards use only
the standard three axioms. They provide factor provenance for descriptor
completion and multiplicity restoration, rather than a complete root set.

### Descriptor completion of capped isolation

`Isolation.complete? sign context p` runs the actual finite bound search,
capped bisection and shared descriptor enumeration. It returns a checked
`Completion` containing the search trace, every emitted cut point and the
actual descriptor list from each retained cell. Count-zero cells emit nothing.
Count-one cells use their stored prepared domain with no derivative queries;
only unresolved cells invoke all-derivative enumeration. The shared singleton
query still constructs a query-one remainder certificate and checks its replay;
this does not claim elimination of all chain or replay work. Whole-line fallback enumerates
its stored domain. A rejected initial search domain stays `none`; if an
accepted finite bound and prepared initial domain fail during capped
refinement, the result is an explicit internal error. Other producer failures
also remain errors and cannot become empty root sets. The companion proves an
absent completed domain implies a zero or non-squarefree interpreted input.

`Completion.coverage` proves that these actual output values are exactly all
roots of the original input. `Completion.nodup` proves each root appears once,
using distinct emitted points, their exclusion from the remaining head,
disjoint retained cells and the shared enumeration's coverage theorem. The
proofs apply to raw coefficients through a zero-reflecting interpretation in
an ordered real closed field, and use only the standard three axioms.

`complete?_success` proves actual producer success for every nonzero squarefree
input, including singleton retained cells and whole-line enumeration. This
intermediate output is not globally sorted; the complete root operation below
orders entries, restores Yun multiplicities and handles the zero-polynomial case.
Unresolved and whole-line enumeration currently prepare the retained domains
again; the requested upstream prepared-root enumeration API remains a subsequent
integration. `cell_enumeration_present` and `Whole.enumeration_present` prove
that these retained valid domains cannot return the absent-domain result. That
branch remains a diagnostic guard, using the internal system error rather than
a descriptor-replay error.

`hexrealclosure_isolation_conformance` emits twenty actual executions. The pinned
Z3 RCF oracle independently checks inputs, finite-bound policy, node caps,
scalar-preserving deflation, cell counts, selected derivative words, literal
descriptor contexts, complete root coverage and absence of duplicates. Cases include nonmonic input,
negative leading scalar with an emitted zero, a nonquadratic generator,
four real roots, a whole-line inverse infinitesimal, close infinitesimal roots
requiring completion after the rational bisection cap, and invalid domains.
The nested isolation case finds both roots of `Y²−√2` using a coefficient selected
from the reducible definition `(X²−2)(X−3)`. The fixture includes that first
descriptor; the oracle checks its head, interval and context before evaluating
stored coefficient polynomials at its selected root. The nested isolation cells
are singletons, while the other fixtures exercise derivative-sign descriptors.
The nested assembly case
checks all three roots and their multiplicities in `(Y²−√2)²(Y−1)`, including
noncanonical stored coefficient polynomials in the expanded input.
Six further cases independently check Yun assembly against exact Z3 roots and
derivative-derived multiplicities, including zero, constants, a pure power,
distinct multiplicity labels, a root-free factor and a simple restored zero.
The oracle does not replay descriptor proof graphs or prove producer totality.

`Isolation.Root` retains both emitted coefficient points and selected-root
descriptors in one context. `Root.compare` uses coefficient differences for
points, the shared selected-sign query for mixed pairs, and the checked
common-product comparison for descriptor pairs. Comparison failures propagate;
invalid sign codes and encountered equal roots are internal errors. Finite insertion
sorting preserves the actual input roots and their mathematical values.
The companion's `Root.compare_correct` proves that every comparison succeeds
and agrees with mathematical order in a common ordered real closed field,
including descriptor pairs on different defining polynomials. It consumes the
upstream selected-sign and common-polynomial comparison producer theorems.
`Root.sort_success` proves successful strict sorting for lists of distinct
mathematical values. `Root.sortBy` carries an arbitrary payload with each root;
its success, permutation and strict-order proofs preserve that payload exactly.
The complete root operation uses this sorter to retain multiplicities.
`hexrealclosure_root_order_tests` also belongs to the default
`HexRealClosureTests` build. It exercises distinct roots on one head and on
different heads, exact mixed output, actual completion with both points and
descriptors, duplicate rejection and comparison-error propagation.
## Zero-root multiplicity

`ZeroFactor.remove p` removes the complete power of `X` by scanning the literal
zero coefficients once and copying the remaining coefficient slice. It performs
no coefficient arithmetic. The coefficient scan and copy use linear work in
the input's stored size; costs of the supplied zero-equality operation remain
part of the coefficient representation. The returned quotient keeps the original
leading scalar. The companion proves exact factorization, that a nonzero input's
quotient has no zero root, and that the extracted exponent is the original
zero-root multiplicity. Every nonzero root retains its exact multiplicity.
These proofs require only a zero-reflecting coefficient interpretation; they
impose no field laws on raw storage and use no root-count admission.

A zero polynomial returns `(0, 0)`. `Roots.assemble` below returns `all`
for that case and restores the extracted multiplicity when merging other roots. The exact deflation
fixture driver also covers constants, a pure power, mixed nonzero roots,
fractional and negative scalars, and one and two infinitesimal levels. Its
independent SymPy oracle determines the zero multiplicity from the first
nonzero coefficient and checks the entire returned quotient.
`Roots.assemble` composes literal zero extraction, the actual raw Yun
recurrence and complete isolation of each returned factor. Its intermediate
`Output` retains `all` for the zero polynomial and positive multiplicities
for finite entries. It restores an extracted zero exactly once. Failed factor
completion and absent factor domains remain explicit internal errors.
`factorEntries_cons` exposes the actual completion of the first factor and the
actual recursive output for all remaining factors. No companion theorem is a
constructor argument. The default native tests exercise zero, positive and
negative constants, a pure power and mixed roots with multiplicity gaps and a
negative leading scalar. They also exercise positive-degree root-free factors,
a simple zero mixed with a repeated nonzero root, and a polynomial over cached
selected-root values without field laws. Root checks do not depend on the
intermediate emission order.

The companion's `factorEntries_spec` ties every emitted root and label to the
actual factor input. `factorEntries_multiplicity` and `factorEntries_complete`
transport the actual raw Yun result into a characteristic-zero field and prove
exact labels and coverage. They require coefficient-operation preservation, zero reflection and agreement
of the computed signs with a common ordered real-closed field; the executable
coefficient type needs no field instance.
`assemble_spec` composes these results with zero extraction: a successful finite
output represents exactly the original polynomial's roots with their original
positive multiplicities. `assemble_nodup` proves each mathematical value occurs
once. `assemble_all` proves the separate all-roots result occurs exactly for
semantic zero.

`Roots.roots sign context p` is the ordinary complete root operation over the
supplied coefficient carrier. It returns `all` for zero or a strictly increasing
finite list of roots with their original positive multiplicities. It runs the
actual assembly and globally sorts the retained entries. `Roots.roots?` exposes
the internal diagnostic result. An invariant failure in the total wrapper
prints a panic and falls back to `all`, so it cannot resemble a root-free
answer for a nonzero polynomial. The companion's `assemble_success` and
`roots_success` exclude these diagnostics under the coefficient interpretation
laws, including successful completion of every retained cell and actual Yun
factor. No producer output is assumed. `roots_all`, `roots_spec` and
`roots_sorted` prove the total operation's zero case, exact coverage and labels,
and strict mathematical order over arbitrary ordered real closed fields. These
laws allow raw coefficient representations without a field instance or an
injective interpretation, provided zero is reflected and operations and signs
are preserved.

The compiled isolation fixture exercises the complete checked producer on repeated
factors and over a selected algebraic coefficient. Its independent exact Z3 RCF
oracle checks coverage, multiplicities and strict order; mutation tests reject
reversed outputs. The emitter preserves explicit error rows for any internal
failure, which the oracle rejects.
The native tests exercise the total wrapper's zero case and check the ordered labels
`[3, 2, 3, 5]` for `-3 X² (X²-2)³ (X-3)⁵`.
Trivial-base agreement is a separate requirement of the full `RootSet` interface.
`runRoots` times the actual total operation, including global ordering, on this
repeated-factor input; `runAssembly` retains the intermediate timing anchor.
The current global insertion sort uses at most quadratically many comparisons,
with common-polynomial re-encoding for descriptor pairs. These fixed anchors
make no scaling claim and do not complete the required Phase-4 evaluation.

### Rational generic-route agreement

`Trivial.Rational.polynomial` converts a rational dense polynomial to the existing
`RealAlgebraicPoly` coefficient representation. `Trivial.Rational.roots` runs the
complete generic producer and converts each actual root through the existing
selected-root canonical conversion; point roots retain their rational value.
It preserves `RealRootSet.all`, root order and positive multiplicities.
The companion module `HexRealClosureTheory.Trivial` proves
`Trivial.Rational.roots_eq`: the entire converted result equals
`(Trivial.Rational.polynomial p).roots`, including the zero case and exact labels.
`Trivial.Rational.compare` delegates comparison of converted roots to
`RealAlgebraicNumber.compare`; `compare_eq` proves the checked generic
comparison succeeds and returns that same order.

Run `lake build HexRealClosure.TrivialTests` for executable differential
checks of zero, constants, empty nonconstant root sets, zero multiplicity,
irrational pairs, repeated Yun
factors, negative nonmonic definitions and non-dyadic rational roots. All pairs
of returned roots are compared through both routes. Checked descriptors also
exercise equality of √2 through different quadratic/quartic heads and of
a rational point with a selected cubic root in both comparison directions,
and strict comparisons of √2 with ∛3 through different selected heads.
Run `lake build HexRealClosureTheory.Trivial` for the companion proofs.
The conversion still
performs canonical root selection for each selected generic descriptor;
this agreement is not a claim of equal runtime cost or generic-path scaling.

`Trivial.Map.ofSuffix suffix` converts an entire validated algebraic tower over
`BaseContext.rational registry`. Each selected canonical generator is found
once through the independent `RealAlgebraicPoly.roots` API and retained in the
conversion closure; all later coefficients use canonical Horner arithmetic.
This factory is defined only for the rational base and its root suffixes.
It does not specialize real constants or infinitesimals.

`HexRealClosureTheory.TrivialTower` proves success of every selected-root
search from the actual validated descriptor and derives agreement through
all levels of that factory. `Map.ofSuffix_roots` identifies the entire converted
native root set with the existing backend result, including `all`, increasing
roots and exact positive multiplicities, for arbitrary stored tower
coefficients. Companion theorems preserve zero, one, natural casts, addition,
subtraction, multiplication, negation, total inversion, division, native
semantic equality, comparison and signs. Raw nonzero expressions can have
different literal representations; the conversion identifies their values.

Run `lake exe hexrealclosure_trivial_tests` for compiled executable comparisons
using a nonmonic reducible defining polynomial selecting a cubic irrational,
a dependent quadratic root selected by a Thom sign, nonlinear
algebraic-coefficient polynomials, nonreal conjugates, point roots and repeated
roots. The nonmonic reducible predecessor is a separate native check;
the qqbar fixtures use the monic cubic/quadratic tower. The full native
comparison also runs the canonical backend's common-field presentation, whose
checked containing-field attempt and primitive-search fallback are described
in the [number-field SPEC](../HexNumberField/SPEC/hex-number-field.md).
The six nonzero fixtures use the containing-field branch. Separate number-field
checks cover rejected membership and fallback. CI applies a one-hour
operational limit to this driver. Manual execution has no such limit, and
these checks do not constitute the required scientific performance evaluation.
Run `lake build HexRealClosureTheory.TrivialTowerTests` for ordinary-import
consumers and kernel axiom guards. The native example also checks a value
read/write round trip and stale-context rejection. The shared driver feeds
`hexrealclosure_trivial_conformance`, which exports the actual generic roots
after conversion; `scripts/oracle/real_closure_trivial.py` checks them against
independent exact python-flint qqbar arithmetic: factor division and
quadratic/cubic binomial root formulas give complete roots and multiplicities
for the seven committed inputs. Other residuals use the general qqbar root finder. The committed
seven-case fixture covers zero, a constant, a dependent linear polynomial,
mixed coefficients with repeated roots, nonlinear heads, nonreal conjugates
and a point root. The emitted root kinds check actual point and selected-root
production. The oracle independently reconstructs both selected generators and
evaluates every original recursive coefficient, including its cached sign,
before checking the converted root output. Twenty-two tests cover valid output
and mutations; parser checks still run when optional FLINT support is absent.
It does not replay native certificate graphs.
`Map.ofSuffix` caches the generators of the input tower. Individual
`Map.root` conversions and `compareRoots` searches still enumerate the
converted head's roots per requested handle; `Map.output` does not yet share
those searches between entries with the same factor. The required performance
evaluation must account for that cost. The remaining whole-family independent
coverage audit, and conversion back into native presentations with proved
round trips, stay in
[#10378](https://github.com/kim-em/hex-dev/issues/10378).

### Native complete roots

`Tower.Context.roots p` materializes the complete producer's output as a native
`Tower.RootSet ctx`. Zero retains `all`; finite entries preserve the original
order and multiplicities. Each `entry.root` carries a `context`, its native
`value`, and an explicit `embed` from the input context. A coefficient point
retains the input context. A selected descriptor caches the actual extension
returned by `ctx.adjoin`, including its generator and predecessor embedding.
The old contexts and values remain valid.

`root.conversion` packages the coefficient inclusion as a native `Conversion`,
retaining the cached child and composing with later transports.
`Root.conversionModel` proves preservation in the same ambient field.
`conversion_spec` identifies its coefficient map with `embed`,
`conversionModel_target` identifies its child interpretation with `model`, and
`convertedValue` supplies the selected value with the ownership expected by
later conversions. `convertedValue_value` proves its interpretation.

`root.embedPoly p` enters every coefficient into the root's context, and
`root.signAt p` evaluates there using ordinary native arithmetic.
`root.compare other` is a total comparison through the compatible selections
over the shared input context; `compare?` exposes its internal diagnostics.
Comparing values owned by different child contexts does not identify their
raw types.

The companion interprets every actual root context in the same ambient ordered
real closed field as the input. `Root.embed_value`, `embedPoly_value`,
`signAt_value`, and `compare_correct` prove coefficient preservation, polynomial
signs and comparison. `Context.roots_all`, `roots_spec` and `roots_sorted` prove
the native output's zero case, exact coverage and multiplicities, and strict
order. No semantic model is an argument to the executable root construction.
`Context.roots?` retains the generic producer's internal diagnostics;
`roots?_success` proves it succeeds and agrees with ordinary roots.
The default native tests execute root finding, polynomial signs and inversion
in these actual child contexts on the repeated-factor rational case and on
`(Y²-α)²(Y-1)` over the selected `α=√2` of `(X²-2)(X-3)`.

Materialization eagerly constructs every selected child, including its literal
descriptor encoding and prepared query domain. `runNativeRoots` measures this
complete operation on the same repeated-factor input as `runRoots`, with input
construction outside the timed call. These are fixed functional anchors; the
required tower scaling evaluation remains separate.

`ctx.collect roots` gathers any finite list of root handles over `ctx` into one
actual native context. Its `input` maps every original coefficient value into
that context; `entries` retains the root handles in input order and a conversion
for every value in each original root context. Each entry supplies `value`
for its selected root and `apply` for an arbitrary old root-context value.
`collect?` exposes revalidation failure; the companion proves it succeeds and
agrees with ordinary collection under the input model laws.

Collection revalidates each next root over the converted coefficient context
and includes all previously collected contexts into its new child. Old handles
stay valid in their own contexts. `Root.move?_success` proves preservation of
both the converted coefficient context and the complete old root context;
`RootMap.Model.value` and `Collection.Model.values` identify all transported
values and the ordered root list in one shared ambient model.
`Context.roots_collected_sorted` specializes this agreement to the strictly
ordered output of complete root finding for every compatible collection model.
`Context.roots_collected_ordered` gives the native all-pairs sign comparisons
for that output, given a `Tower.Model` of the input context, without
a caller-supplied collection model.
Entries retain input order, so callers can zip them with the original positive
multiplicity labels. Collection retains each selected root’s descriptor head.
For complete root output, that head is a Yun squarefree factor, possibly
deflated by exactly hit points. Under the input model laws, the formal tower
degree over the input context is the product of these defining degrees.
Point roots (zero and exactly hit cut points) add no level; rational roots
that remain selected handles add their descriptor level. For r distinct
real roots of a degree-n input, this is at most n^r, with worst case n^n.
This is representation size, not the degree of the denoted field extension.
Arithmetic in reducible levels uses zero-divisor splitting. The constructor
currently does not deflate by previously collected roots; assessing this
growth belongs to the required tower scaling evaluation.

Run `lake build HexRealClosure.RootCollectionTests` for a runnable mixed-field
example: √2 and the positive root of `3(X²-3)` enter one context, where their
sum satisfies `s⁴-10s²+1=0`. The example checks inversion, nonlinear transport,
old-handle validity, and stale-context reader rejection. The isolation
conformance driver exports the actual recursive stored values and root frames;
the independent Z3 oracle checks selected roots, cached signs, coefficient
inclusions and arithmetic. Its embedded replay graphs are retained data and
are not replayed by that oracle. Automatic dependency-closed collection of
live contexts uses real-key subsequence inclusions into an already validated
shared base, including keys in other positions. Constructing that joint base
from separately supplied paths and transporting reordered real paths remain
required; separate constant laws do not supply a joint realization.

`TowerCoverage.lean` connects the native producer to the relative algebraic
union. `Model.nativePoly` lifts coefficients from the input's mathematical
field to stored representatives for the semantic existence proof.
`Model.algebraic_root` then invokes the complete native producer and identifies
an actual returned root value with any element algebraic over that field.
`Model.roots_iff_union` proves that these native root presentations describe
exactly the algebraic union. Conversely, `Root.values_algebraic` places every
value of an actual root context in that union, and `Root.unionModel` interprets
the entire context there with its arithmetic and sign laws. The existing
`Union.realClosed` supplies real-closedness of this same field. The coefficient
lift is noncomputable proof infrastructure; executable callers supply their
native polynomial, and root production uses the ordinary total API.

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
remainder when eligible. Independently of storage, `Context.queryPoly` performs
positive pseudo-reduction before submitting a scalar query to the shared
selected-root sign producer. It skips the unused multiplier power and quotient
sign correction. The producer already reduces its operands; this step moves
the first reduction outside its replay certificate. The producer's matching
reduction is then trivial, avoiding replay of the original
high-degree identity. The actual remainder has smaller degree and the same
sign at the selected root, including negative leading coefficients. Constants
and smaller queries take a direct path. Reading a stored sign reuses its result.
Nonmonic or unclean definitions retain the raw representative. A leading
coefficient that denotes one but differs structurally
from literal one does not enable monic storage.

`Element.restore p sign proof nonzero` retains an exact nonzero stored
representative using a proof of `Context.signPoly p = sign`. It performs no
sign query or normalization. `restore?_eq` proves equality with the existing
independent executable check; canonical zero remains separate. `ofPoly_restore`
and `ofPoly_eq_zero` identify the actual packing result from a proved sign of its
retained remainder. The companion's
`Context.signPoly_checked` obtains that proof from supplied, accepted
`SelectedSigns` evidence for the actual reduced query in this exact context.
The ordinary-kernel example uses a degree-two stored representative whose
query has degree one. Evidence for a wrong sign, a different query or a
mismatched context key rejects; the certificate type fixes the actual reduced
query. The examples also check rejected restoration, packing to the actual
remainder, and packing a vanishing input to canonical zero. The byte coefficient
decoder continues to use `restore?`.

The module `HexRealClosure.SignFacts` provides finite,
proof-bearing sign facts. Each fact fixes the exact polynomial representation
and its algebraic context. `SignFact.read` restores a nonzero literal only when
its key and claimed sign match a supplied fact; absent keys, zero claims and
wrong signs return `none`. Its `read_sound` theorem identifies the result of
the ordinary executable decoder.

`Element.pack` uses a proved copy of the actual reduction function and supplied
sign facts for the exact retained remainders, including constants. When no
constant fact is supplied, it uses the predecessor's ordinary sign operation.
Supplied constant facts allow kernel checking when that operation depends on an
opaque termination proof. Both paths preserve canonical zero. `cachedAdd`, `cachedSub`,
`cachedMul`, `cachedNeg`, `cachedOne` and `cachedNatCast` supply ordinary operations
proved exactly equal to the existing operations. These equalities let a caller
check a literal certificate using the supplied facts and transfer the resulting
acceptance proof to the existing checker. Each list-based lookup scans the
supplied facts, including for constants; its cost grows with that list.

`PackingConformance.constant_cached` checks this path with an executable
predecessor sign function that is opaque to kernel reduction and proved equal
to rational sign. Emptying the fact list blocks kernel evaluation of constant
packing. Subtraction with supplied facts produces canonical zero.
`NestedSignsConformance.graph_checked` checks a two-entry graph with lower-root
facts; `graph_memo` derives preservation of its literal memo indices.
`graph_selections` selects two different query lists from one validated memo.
The graph probes reject an unreachable entry with a corrupted moment, a
foreign context, a self reference, an absent root index, changed endpoints and a wrong selected
query list. They use ordinary
kernel checking and the existing cache-agreement theorems.

An absent nonconstant fact reaches an opaque packing function. This prevents
ordinary-kernel evaluation from completing that branch. Compiled evaluation of
that function runs the existing sign producer. Accordingly, these APIs support
kernel proof assembly; they do not provide a strict compiled checker for
untrusted cross-level certificates. `SignFact.read` itself has no such fallback.
The equality proofs cover only the listed operations. Numerals, inversion,
division, `ofCoeff`, equality and comparison retain their existing implementation,
which may invoke a sign producer during kernel evaluation. Installing
`cachedNatCast` controls explicit natural-number casts, not numeral instances.
The examples use `import all HexRealClosure.Algebraic` to make the stored
constructors available for `decide +kernel`. The public equality and restoration
lemmas can be applied without that implementation import.

`Element.signCodec value facts` retains the existing stored-value wire format
and reads nonzero coefficients from exact sign facts in this context. Missing
or mismatched facts reject instead of recomputing this context's sign. The
supplied predecessor codec governs lower-level decoding; composing strict
readers makes each covered level avoid sign production. Zero needs no fact.
A finite reader is partial, so its roundtrip proof requires only the actual
stored coefficients to roundtrip through the predecessor reader and the
nonzero stored literal to occur in the facts. `SignFact.read_of_key` derives
that coverage from list membership and equality of the exact polynomial key. The corresponding byte theorem
uses the shared parser/printer and its existing lexical limits. Successful
reads agree literally with the independent native coefficient decoder.
`Element.signCodec_refines` composes that agreement through predecessor readers;
`SignCodecConformance.nested_sound` applies it to two successive extension levels.
`SignCodecConformance` checks two successive strict readers, retained
representatives, missing lower-level facts, altered signs and truncated bytes.
These coefficient readers do not encode or validate a dependency graph.

`Context.readSigns?` performs memo selection in the Mathlib-free core, with no
interpretation arguments. `HexRealClosureTheory.SignFacts` connects its result
to the proved sign facts consumed by coefficient readers.
`Context.readSignFact?` selects the row for the context's actual reduced query,
checks the claimed sign, and returns a proved sign fact keyed by the original
stored polynomial. It checks the literal head and interval before selecting
the row; a missing index or mismatched query/sign returns `none`. The companion's
coefficient interpretation proves agreement with the native scalar sign.
The function is inlined so that the interpretation and field instances occur
only in erased proofs, including when the ambient field is noncomputable.
Computing the reduced query uses ordinary predecessor arithmetic. The core
coefficient reader still takes only supplied sign facts.

`SignFactsConformance` uses one checked graph row to restore both `X²−1+2X`
and `2X` at the selected root `X=1`, retaining their distinct stored forms.
The compiled example checks the actual graph and strict coefficient decoder;
ordinary-kernel proofs check the supplied row, its sign correspondence and
the stored polynomial and sign fields. A whole-line example shares a memo
between the positive and negative roots, including their derivative prefixes.
A second extension obtains its own fact from a checked graph and decodes
through both coefficient readers; removing a required lower-level fact rejects.
Wrong signs, unrelated queries, domains and absent indices reject.
This connection does not itself serialize dependencies between field levels.

`HexRealClosure.SignRequests` serializes ordered polynomial/sign references to
entries in an already checked graph. Its versioned byte format binds the full
selected-root description: context value, defining polynomial, both endpoints,
derivative indices and derivative signs. Changing any part rejects. Roundtrip
proofs use the shared byte parser and the predecessor reader's coverage of the
actual stored coefficients.

`Context.readRequest?` selects the original stored query directly, without
computing a native query reduction. The graph must contain the original stored
queries; a graph containing only their reduced representatives is a different
input. Several requests can reference one joint table entry, including a
nonempty derivative prefix. The reader extracts its unique count-one row and
checks each requested supplementary query slot. The companion proves agreement with the
total scalar sign using the selected-sign and scalar-sign correspondence
theorems. `Context.decodeRequests` decodes the bytes and resolves every ordered
reference against one memo; any missing entry or wrong sign rejects the whole
list. Derivative-prefix slots alone are not supplementary query requests.
A pointwise theorem preserves the request order and each literal
polynomial/sign pair. The reader's interpretation arguments occur only in erased proofs. The core
`SignRequest.signs?` reader has no interpretation arguments.

`SignRequestsConformance` restores two different stored polynomials, rejects
stale root bindings and bad references, and chains request packets through two
coefficient levels. The upper packet needs a nonconstant lower-level sign fact
to decode its own defining polynomial and query; removing that fact rejects.
The graphs are produced outside replay. This format references one supplied
memo at a time. It does not implement a global graph of field levels or make
graph validation avoid the predecessor arithmetic's native sign production.

`HexRealClosure.SignEvidence` supplies a whole child packet instead of
requiring callers to assemble a graph and sign references separately.
`Context.buildEvidence keys` runs the existing prepared BKR producer on that
exact ordered list of polynomial keys, then encodes its checked tree as one
shared graph. Repeated requests retain separate sign slots; repeated literal
nodes share an entry. Zero and empty request lists are supported.
`SignEvidence.check?` independently checks the graph and its selected row,
requiring the caller's complete key list. Missing, extra, reordered or
substituted keys reject, even if substituted polynomials have equal values.
The generic `check_ofSigns` theorem proves that checking a produced packet
returns the original joint signs exactly.

`SignEvidence.codec value ctx raw` stores the full selected-root binding,
ordered keys, sign vector and shared graph in one versioned byte packet.
`Context.decodeEvidence` in the companion decodes and checks those bytes, then
returns a proved sign fact for every key, in order. Its semantic arguments occur
only in erased proofs. The reader does not run this packet's producer to fill missing evidence.
`Element.signCodec` can use the returned facts at the next coefficient level
when they cover every nonzero coefficient literal in that packet, including
those created by its producer's arithmetic.
Graph checking uses the supplied coefficient arithmetic; avoiding searches
inside that arithmetic requires separate coverage of its packing operations.

Run `lake build HexRealClosureTheory.SignEvidenceConformance` for direct
rational sign comparisons, shared repeated queries, zero and empty cases,
changed header, node and moment bindings, cycles, and corrupt unselected
entries. Compiled decoding also erases a deliberately noncomputable semantic
interpretation. A fixture second-level graph decodes through proved facts
obtained by checking a first-level packet;
removing a lower literal, an endpoint fact or an upper key rejects. The ordinary
kernel probes use literal child certificates and the general correspondence
proofs. `upper_roundtrip` proves a structured JSON roundtrip for a single-leaf
fixture with assembled lower facts and a strict finite predecessor reader;
coverage of every stored literal is proved by ordinary kernel computation.
The compiled `producedNestedPass` instead builds both
levels with the actual producer. It automatically collects the upper packet's
coefficient keys, builds and checks the lower packet, and decodes the upper
packet through its finite facts, including nonempty preparation and reduction
steps. Removing each required nonzero child fact rejects.
Axiom audits include the actual producer success theorem, scalar
fact construction, the finite-reader roundtrip and the theorem connecting
acceptance to the actual decoded bytes.

This API takes an explicit key list. It does not yet collect all intermediate
packing keys automatically, rebuild algebraic contexts from child packets or
supply a single graph of dependencies between field levels.
`SignEvidence.coefficients` and `SignEvidence.contexts` collect the finite
literal support of a packet, including its full root binding and every stored
node. `Element.signKeys` retains distinct polynomial keys in first-occurrence
order, and `Element.predecessors` collects their stored predecessor coefficients.
`Context.signFacts_covers` derives finite algebraic-reader coverage from a
checked child joint table. `codec_ofSigns_covered`, `bytes_ofSigns_covered` and
`Context.decodeEvidence_covered` prove exact producer/reader correspondence
under finite literal coverage. `Context.decodeEvidence_nested` composes the
checked lower joint table with the actual upper byte decoder, deriving the
upper reader's coverage from the lower facts. The child table may contain
additional keys for other packets at the same level. Its predecessor reader also
needs only finite coverage, so the theorem can be applied across further
levels. Complete readers may still use their global
laws. Byte roundtrips additionally require the printed packet to pass
`Codec.checkBytes limits`, including its syntax prechecks. The actual encoder's root and backward-reference bounds,
node dimensions, reduction indices and literal node/moment bindings are
proved. `Context.decodeEvidence_ofSigns` proves that printing, parsing and
checking such a packet returns exactly its scalar facts. `Element.codec`
provides its global roundtrip law by recomputing stored signs; the finite-reader
theorems permit `Element.signCodec` without that recomputation during literal
decoding. Graph arithmetic retains its ordinary coefficient operations.
A general proof that sufficiently large lexical limits accept every
printed packet is also separate; the concrete kernel fixture passes the
compiled precheck. Semantic
acceptance of arbitrary bytes is independent of that roundtrip. Collection,
context rebuilding and kernel assembly costs need their own measurements.

`PackingConformance` checks literal restoration, exact keys, context types and
canonical zero in the ordinary kernel. `NestedSignsConformance` checks a second
root defined by `a * Y - 1`, where `a` is stored as `X² - 1 + 2X` at the first
selected root `X = 1`. Supplied child evidence establishes the coefficient and
endpoint signs. The second root is `1/2`; its descriptor and the positive sign
of `Y` are checked using those facts, then transferred to the actual native
operations. Wrong signs, context identifiers and intervals reject. Removing a
needed child fact prevents kernel evaluation. Compiled checks independently
confirm descriptor and selected-sign acceptance. These small examples exercise
nested proof assembly. `Hex.SignDet.Dependencies.Graph` serializes and routes
shared cross-level packets with full subjects and earlier/lower references.
Automatic intermediate arithmetic evidence, context reconstruction, strict
compiled replay and complete cost reporting remain required.

Ordinary addition, subtraction, negation, multiplication, inversion and
division operate on these values. Inversion computes the defining polynomial's
local gcd with the operand, takes the complementary factor, and scales the
actual one-sided Bézout coefficient. `ofCoeff` explicitly includes a predecessor
value. `equal` and `compare` use the selected value; structural equality compares
stored forms. `inv?` rejects canonical zero.

The companion `adapters/HexRealClosureTheory/Algebraic.lean` proves zero
reflection, sign, comparison and arithmetic preservation for a zero-reflecting
predecessor interpretation into an ordered real closed field that preserves
the relevant ordinary operations. Injectivity is unnecessary. Producer success
proves the scalar adapter's explicit internal-error branch unreachable under
these hypotheses. Inverse correctness derives the cofactor root and constant
gcd properties of the actual computation. `AlgebraicTower.lean` instantiates the
second level's interpretation using the first level's proved operations,
including zero reflection, sign and gcd/cofactor inversion.

`AlgebraicTransport.lean` connects the actual `Element.denote` interpretation
to finite Tarski queries and full BKR replay. For an accepted native replay over
one algebraic level, its count for each ordered sign condition equals the
cardinality of the corresponding ambient root set. The proof supplies all
coefficient, sign, preprocessing, reduction, and moment interpretation facts
from the level’s existing semantic theorems. Positive and count-one results
supply existence and uniqueness in the ambient field. The replay context-key
type can differ from the current level’s key type. A validated next-level
descriptor obtains its finite interpretation package directly from the current
level and can be checked over the ambient field with its literal replay. The
root used by the next level realizes additional query signs in their original order;
certificate acceptance remains an explicit premise.

`AlgebraicYun.lean` specializes the coefficient interpretation to Yun's
actual raw recurrence over an algebraic level. Mapping its factors into the
ambient field gives the same Yun recurrence there, and the mapped result
passes Yun's exact factorization replay. For nonzero output, its emitted
factors cover exactly the ambient roots of the input, and each root has the factor's labelled
multiplicity in the original polynomial. The proof uses the level's verified
division and inverse, which require the predecessor interpretation to preserve
division. It assumes no field laws on stored representatives.

`AlgebraicReencode.lean` changes one level's defining polynomial through a
checked `SignDet.Reencoding` of the same selected root. `Element.reencode`
repacks an old value under the new immutable context, and
`Element.reencodePoly` converts the coefficients of a dependent polynomial.
The companion proves preservation of the selected root, value and interpreted
dependent polynomial, with zero reflection for converted values. Old values
remain typed by their original context. `Context.reencode_adjoin` identifies
the target context with adjoining the new descriptor under the same cleanliness
rule. Repacking may canonicalize a literal representative because evidence
from the old context cannot be reused in the new one. The native tests include
a restored high-degree representative and a nonmonic target that keeps its
unreduced polynomial. Each converted nonzero coefficient currently runs its
own sign query; reusable sign handles are a later cost improvement. This
conversion keeps the predecessor fixed. `Tower.Refinement` below converts an
immediate later descriptor, and `Tower.Conversion` converts an explicitly
supplied finite suffix. Automatic dependency-closure selection remains separate.

`AlgebraicRoots.lean` applies the successful root-assembly theorems to actual
`Algebraic.Element` coefficients. Given a zero-reflecting predecessor interpretation into an ordered real closed
field that preserves arithmetic, negation, inverse, division and sign, the
level's selected-value interpretation supplies every coefficient premise. A
successful finite assembly therefore covers exactly the ambient roots of the
interpreted input with original multiplicities and no duplicate values; `all`
is equivalent to semantic zero. The generic complete-root success and strict-order
theorems can also be instantiated with this interpretation. The native tower
wrapper above supplies the complete root operation and its extension embeddings
for context-indexed values.

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

`HexRealClosureTheory.BaseTests` also executes all three stages together: a
registered Liouville real constant, a positive infinitesimal, and a selected
root of `Y²−(τ−5/4+ε+2)` in `(1,2)`. It checks the root's equation, interval
signs and inverse in the constructed context.

The semantic sign, inverse and quotient proofs consume the proved shared
Tarski foundation. Their axiom guards contain only the three standard kernel
axioms, and the audited import cones contain no admissions. These interpretations are
conditional on an ambient ordered real closed field, not an existence proof.

The remaining tower work includes dependency-closed enlargement and transport
across multiple live contexts and full algebraic-coefficient rational delegation
agreement. Complete ordered roots and multiplicities, the checked
`Context.enlarge?` producer for one context, and identification of native
presentations with the compatible real-closed union are described elsewhere
in this README.
Each native algebraic context prepares and retains the shared selected-root
query domain once, eagerly during context construction. `Context.buildSigns`
reuses it for singleton and joint queries; `buildSigns_eq` proves exact
agreement with the original producer,
including its certificates and errors. The BKR table and certificate replay
still run for each query list. Under the companion coefficient interpretation,
`Context.handle_success` proves that preparation succeeds using the
proved root-sum theorem. Arbitrary coefficient operations retain the
original producer when preparation fails. Formal tower performance evaluation,
including nested sign/zero counts and coefficient growth, remains open; no
measured speedup is claimed for this domain reuse.

## Recursive tower contexts and checked readers

`Tower.Chain` completes the staged base before adjoining algebraic roots. Each
root is validated over the entire predecessor carrier using its actual sign
and full signature. The constructors derive ordinary coefficient operations,
recursive cleanliness and the coefficient codec; raw algebraic carriers have
no ring or field instance.

`Tower.Context` packages such a chain with its value type. `Context.adjoin`
accepts the exact context-bound descriptor and returns an `Extension` containing
the new context, its selected generator and the actual constant-polynomial
embedding. Old values keep their owning context. The compatibility operation
`Context.adjoin?` has an optional serialization-shape result, but
`Context.adjoin_isSome` proves that failure unreachable for a validated
descriptor; `Context.adjoin_some` relates it to the total operation.
The returned extension retains its literal frame, the proof of its complete
binding, and `Context.adjoin_native` identifies the native child, embedding and
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
The relative context reader rejects a full duplicate of its parent reference.
Literal arrays are emitted by an accumulator with `Array.push`.

`Tower.Catalog` is an immutable catalog of caller-constructed validated prefixes.
Insertion rejects rebinding. Its separate base catalog supplies real search
progress and reconstructs infinitesimal stages. An algebraic signature is
accepted only when that exact native context is installed; inserting a shorter
prefix does not install its successors. Readers retrieve the full context first,
then decode a scalar or polynomial in that context; returned packed values
retain their owning context. A cached signature hash filters catalog entries,
and exact equality confirms a match. The successful lookup supplies the binding
proof, so the payload decoder does not compare that signature a second time.

The structured codecs have proved literal write/read roundtrips. Nonzero
algebraic payloads retain both the polynomial and cached sign; their reader
checks predecessor coefficients and recomputes the sign in the exact context.
It restores the stored polynomial without arithmetic repacking, preserving
literal certificate coefficients that are semantically equal but structurally
different. A correctly signed external payload may have arbitrarily high
degree, so its sign check and later arithmetic have costs that depend on that
degree. Arithmetic uses `Element.ofPoly` and retains the computed remainder
when the definition is monic and clean; other definitions remain unreduced.
Polynomial readers reject trailing literal zeros.

Run `lake build HexRealClosure.TowerTests HexRealClosureTests`. The examples build
three actual algebraic levels, use their explicit embeddings, read old values
after extensions, restore an unreduced noncanonical coefficient, and reject
stale or unknown bindings, forged signs, zero claims, trailing zeros and
malformed base payloads. The core roundtrip proofs introduce no admission.
Automatic discovery of a dependent suffix remains open. Complete isolation,
checked suffix conversion and identification with the real-closed union are
described elsewhere in this README.

Run `lake build HexRealClosure.FrameFormatTests` for total construction over a
non-monic reducible rational definition, followed by a definition with
noncanonical predecessor coefficients. The frame-format axiom guards use only
the standard three axioms. Native frame-format totality is independent of
graph decoding and byte-parser completeness.

### Reconstruction from algebraic frames

`Context.readDescriptor` reads the exact seven-field descriptor frame and
independently replays its supplied graph over the native predecessor. Its
formal derivatives, count-one condition, context and root-domain bindings are
checked by the shared descriptor checker. `Context.readFrame` then constructs
the native extension and checks that it re-encodes to the exact requested
frame. A replay with extra unused entries may be mathematically accepted but
has a different full identity and is rejected by this last check.

`Catalog.reconstruct` recovers an entire context from its structured signature.
It retrieves the validated real base and its actual erased search progress,
then visits algebraic frames in predecessor order. It can reuse installed
prefixes and checks each missing one. Its returned context carries a proof of the
requested full signature. Unknown validated bases and false or differently
encoded frames produce errors. Catalog insertion remains an explicit operation.

`Catalog.restoreElement` and `restorePolynomial` reconstruct the native context
before decoding the payload; the returned packed value retains that context.
The existing `readElement` and `readPolynomial` use only installed algebraic
prefixes. Successful restoration has proved binding preservation, and
write-read roundtrips are proved for installed contexts. `RestoredRoot.frame_data`
proves exact re-encoding of every successful root-frame reconstruction.

Run `lake build HexRealClosure.RootFrameTests`. The examples reconstruct two
successive roots, restore generator payloads and polynomials, work with a cached
prefix, and reject an explicit stale full predecessor reference, misplaced
frames, false graph versions and matrix certificates, unknown real providers,
malformed frames and extra unreachable graph entries. These are structured JSON
APIs; the `TowerBytes` interface below proves shared parser/printer laws and
exact byte/text roundtrips for known contexts. A roundtrip theorem for every
freshly encoded tower with an uninstalled suffix still requires graph-shape
completeness.
Batch callers can reconstruct once, insert the returned context, and then use
the installed-prefix readers to avoid replaying each missing frame per value.
The root reader's remaining graph-shape obligation also applies after refinement.

### Interpretation, algebraicity and order of native towers

`Tower.Model context K` interprets the exact native context in an ordered field.
It is a companion result carrying zero reflection and arithmetic/sign
correspondence; executable constructors do not accept this record. `Model.base`
uses an embedding of the canonical base carrier and its actual sign theorem.
The existing `fieldOfGrind` bridge preserves the native coefficient operations.
For a real-closed ambient field, `Model.adjoin` derives the child interpretation
from the predecessor model and the validated descriptor. It uses the actual
public extension: `adjoin_embed` preserves predecessor values and
`adjoin_generator` identifies the selected generator with the descriptor's root.
`root_value` and `adjoin_denote` connect those models to the selected-root
interpretation of the actual stored algebraic representative. These steps can
be repeated at arbitrary finite depth.

`Model.field` is the image subfield of the ambient field. Its values have genuine
field and order instances, while raw native expressions retain their ordinary
operations. `Model.toValue` is surjective and identifies expressions with the
same mathematical value. `adjoin_mono` includes the whole predecessor field.
Every child expression has a polynomial representative evaluated at the
selected generator (`adjoin_polynomial`). The companion proves that generator,
every child expression, and every element of the child image field are
algebraic over the predecessor's entire image field. Reducible and nonmonic
squarefree definitions are allowed; no minimal polynomial or representation
degree bound is assumed.

`Context.equal` and `Context.compare` execute the native sign check on a
difference. `Model.equal_spec` and `compare_spec` prove that they compare the
interpreted values. `adjoin_equal` and `adjoin_compare` preserve these exact
results under the public embedding. Values must belong to the same context;
structural equality of nonzero representatives has a different meaning.

Run `lake build HexRealClosure.TowerOrderTests HexRealClosureTheory.TowerModelTests`.
Executable checks use a nonmonic reducible definition for √2 and a second root
with noncanonical predecessor coefficients. They cover semantically equal
but literally different nonzero expressions, all three comparison results,
canonical zero and embedded comparisons. Kernel examples propagate a rational
model through three arbitrary validated root levels, including the algebraicity
and image-field inclusions. The semantic root results use the proved
`Tarski.check_rootSum` theorem and only the standard three axioms. They are
relative to a supplied real-closed
ambient field and base embedding. The companions below prove compatibility for
a checked final-root change and conversion through a validated finite suffix.
The presentation quotient below identifies all finite native towers with the
real-closed algebraic union. No tower performance claim is made.

### Yun decomposition over native tower coefficients

`Model.decompose_map` identifies the actual `Yun.decomposeRaw` result over
native coefficients with the lawful field recurrence on their interpreted
values. `Model.decompose_sound` proves full replay acceptance of that mapped
output. The raw coefficients keep ordinary operations and canonical zero;
the model supplies the arithmetic correspondence without assigning field
laws to stored expressions.

For positive-degree inputs, `Model.decompose_factor` gives each interpreted
output factor's monicity, positive degree, simplicity, and exact root
multiplicity. `decompose_root` covers every root of a nonzero input in the
ambient field, with its original multiplicity and membership in the native
output array. `decompose_complete` applies this coverage to a known result.
`decompose_squarefree` and `decompose_coprime` establish constant degrees for
the gcds actually computed on native factors.

Run `lake build HexRealClosure.TowerYunTests HexRealClosureTheory.TowerModelTests`.
The executable examples decompose a repeated nonmonic cubic over two selected
root levels, including a noncanonical coefficient representing one, and check
a gap between multiplicity labels 1 and 3, including their computed gcd.
Kernel examples apply replay, squarefreeness and completeness at three
arbitrary validated root levels.
The proofs use only the standard three axioms. Complete root isolation is
available; the remaining conformance and performance evaluation remain open.

### Checked persistent root refinement

`Context.refine` takes a checked upstream `Reencoding` of the final root over
an unchanged predecessor. It creates a new immutable context and transports
each old value by reading its actual stored polynomial and packing it at the
same selected root in the new definition. The old context and its values stay
valid. `Context.polynomial` and `Context.ofPoly` expose these native operations
without imposing a degree bound on general representatives.
This tower conversion uses the cached target extension for repeated values;
`AlgebraicReencode.lean` supplies the corresponding one-level element API.

`Model.refine_value`, `refine_zero`, `refine_equal` and `refine_compare` prove
value preservation, canonical zero preservation and reflection, and preservation
of actual native comparison results. `refine_field` identifies the whole image
field before and after refinement. `Refinement.mapPoly` converts native
coefficients; `refine_degree` and `refine_poly` prove exact degree and ambient
polynomial preservation.

`Model.adjoin_value` and `adjoin_ofPoly` interpret the public child's actual
stored polynomial and packing operation. `Refinement.mapDescriptor?` transports
a later root's head and endpoints and rebuilds its evidence against the new
predecessor signature. Given a real-closed predecessor model,
`refine_descriptor` proves success for every validated later descriptor;
`refine_root` proves it selects the same ambient root. `Refinement.later?`
packages that revalidation with its cached extension and transport closure.
`Later.transport` converts values using their actual stored polynomial;
`refine_later` proves preservation without a caller-supplied descriptor match.
`refine_later_exists` proves bundle construction succeeds under the same model.
Constructing `Later` adjoins the old level once; retain the bundle and use
`Extension.pack` for repeated packing with its captured prepared state. When
the root frame changes, old context bindings are rejected by the new reader.

Run `lake build HexRealClosure.TowerRefinementTests HexRealClosureTheory.TowerModelTests`.
Native checks refine a nonmonic reducible definition over an algebraic
predecessor and directly over the rational base, including canonical zero, a
noncanonical one, inverses, polynomial transport, stale packets, and a third
root with a transported inverse. A fractional nonmonic target checks stored
polynomials and a retained representative of degree seven. Kernel examples
apply the preservation results to arbitrary validated three-level towers.
The companion proofs use the proved root-sum theorem and only the standard
three axioms. This API covers a final root change and its immediate later
level. The recursive conversion below handles an explicitly supplied suffix;
automatic dependency-closure selection and base enlargement remain open. No
performance result is claimed here.

### Recursive conversion through later root levels

`Conversion.identity` retains the original context and values.
`Conversion.includeRoot` retains the actual cached root child and coefficient inclusion.
`Conversion.refine` starts at a checked final-root refinement.
`Conversion.adjoin?` rebuilds a later descriptor with converted coefficients,
endpoints and fresh context-bound evidence. It stores the new extension's
packing closure for all subsequent value conversions. The private constructor
retains an erased derivation of these native operations, with no semantic law
record as an executable argument. `Conversion.comp` composes two actual
conversions, retaining both closures. `Conversion.cast` reconciles source
ownership using a proved context equality. Together these support consecutive
changes at the starting root before extending the suffix, without discarding
the actual conversion closures.

`Suffix` represents a finite sequence of validated later root levels. Its
`context` is the original final context. `Suffix.embed` includes each original
value through the actual root extensions while retaining its old owner;
bind `let include := suffix.embed` to reuse the extension chain for many values.
`Tower.Model.extend_embed` proves value preservation. `extend_base_agree`
propagates agreement with any supplied base-field embedding, and
`extend_base_embed` supplies it for the canonical base model.
`Conversion.extend?` rebuilds every level in order and returns the conversion
into the new immutable final context. `Conversion.rebuild?` additionally returns
a `Rebuilt` result with
the converted validated descriptors as a new `Suffix`. Its context equality
binds that suffix to the final conversion, and `rebuild_result` proves it
returns the same conversion as `extend?`. A caller can select the first descriptor
in the rebuilt suffix for a further checked refinement and compose the resulting
native conversions. Each returned `Rebuilt` value carries a derivation of the
exact validated steps. Automatic selection and conversion of arbitrary dependent
expressions remain open. Every original context and value remains valid
independently.

The companion `Conversion.Model` relates the native conversion to the original
model and supplies the actual target model. Its `identity` and `comp` interpret
identity and composition; `cast` reconciles the source model with its proved
context equality. `refine` establishes this relation for the starting
refinement; `adjoin` preserves it after every successful extension.
`adjoin_exists` proves each revalidation and conversion succeeds.
`extend_exists` proves success and interpretation preservation for an arbitrary
finite suffix, without caller-supplied replay evidence. `Conversion.Model.extend`
interprets a particular result returned by the executable and `extend_target`
identifies its target with the checked rebuilt suffix. `rebuild_exists`
proves the descriptor-retaining traversal succeeds, and `Model.rebuild`
interprets its final conversion. `rebuild_target` identifies its target model
with the interpretation of the returned suffix, while `rebuildComp` composes
a subsequent semantic conversion and reconciles context ownership. Further
refinement uses `rebuild?` and its aligned `Model.rebuild` witness.
The generic
`zero`, `degree`, `polynomial`, `equal`, `compare` and `mono` results preserve
canonical zero, dense-polynomial degree and interpretation, actual native
comparison results, and inclusion of the whole original image field.

`Tower.Shared base owners` assembles an immutable shared target while retaining
all original owner contexts. Use `Shared.gather?` with the actual validated
context handles, then `Shared.value index value` or
`Shared.polynomial index polynomial` to enter that target. The owner index
keeps the original value or polynomial type. The shared assembly's base check
accepts an original real-key subsequence in the target and nondecreasing
infinitesimal depth; unrelated paths and decreasing depth are rejected.
`Inclusion.base?` uses the cached native `BaseInclusion` coefficient map for this
check, so the same conversion rebuilds dependent roots over a proper real-prefix
enlargement. Earlier infinitesimals retain their positions before any new ones.

`Shared.register? source` returns a `Registration` packet containing the new
shared collection, the actual checked inclusion of the previous shared target,
and the new owner's inclusion. Its `previous.value` transports values already
computed from several owners, and its coefficient map transports their
polynomials. `maps_eq` binds all retained owner maps to that same inclusion.
`Shared.Model.register?` proves interpretation by the returned canonical model;
`register?_union` preserves the union image of every previously computed value.
The existing `add?` surface returns the same shared collection.

The development companion `BaseOrder` derives an ordered coefficient field
from a provider-derived `Chain.Realization`, then constructs its real-closed
ambient and base tower model. `BaseInclusion.Model.ofTarget` in `BaseMapModel`
extracts an existing target model's coefficient homomorphism and composes the
checked native map. It derives the source model, sign preservation, conversion
model and fixed-owner inclusion model without a caller-supplied coefficient
agreement. The development adapter `CacheGather` extends these factories
through the actual shared registration and collection producers.

`RealPrefix.Model.submodel?` derives the interpretation of an actual validated
real subsequence using the target's provider values and the source chain's
stored progress proofs. It succeeds exactly on ordered key subsequences and
returns the requested native handle. A `PackedContext.Realization` retains the
provider interpretation through the actual infinitesimal stages.
`RealPrefix.Model.staged` constructs such a realization, and
`following.restrict? source` derives a compatible source realization from the
target alone. Its success condition is the same real-key subsequence and
nondecreasing-depth check as the native coefficient inclusion. The older
`prefix?` and `embedding?` APIs retain their literal-prefix checks.

The development adapter `BaseFactory` packages this path as
`BaseInclusion.Model.derive following inclusion targetModel`: callers supply
the target realization, checked inclusion and target model; the factory derives
the source realization, coefficient homomorphism, sign preservation and value
agreement. `owner.model? following targetModel` extends that source base model
through the owner's actual stored descriptors into the same target field. It
succeeds exactly when the owner's base passes the native compatibility check.
`following.reference` constructs an ordered real-closed reference field and
base model directly from the staged realization; the owner factory accepts
`following.reference.model`.
`Context.model?_adjoin` and `model?_embed` identify the parent and child results
and prove agreement on the native parent embedding.

`Shared.gather?_models following reference owners compatible` proves that
compatible gathering succeeds. Its returned `Shared.Model` interprets the actual
shared target, preserves the supplied base values, and certifies every returned
owner inclusion and predecessor cache entry in that same field. Its
`canonicalOwners` field identifies every retained owner with its `Context.model?`
factory result, including through `Shared.Model.ofGather`. The target and
cached original models are constructed through `Context.model?`; cache hits
therefore agree semantically with the incoming original predecessor without a separate
coefficient-agreement hypothesis. `Shared.Model.ofGather` packages the model
for an already returned native result. Callers supply the declared base's
provider realization, a model in an ordered real closed field, and the
actual successful gathering result. The producer's success derives the
subsequence/depth compatibility condition for every owner.
`Shared.Model.value`, `polynomial`, `sign`, and `compare` preserve the original
owners' values, coefficients, and native order results. `value_of_model` also
identifies the transported value with a separately retrieved canonical owner model.

`Shared.Model.enlarge ambient` proves the existence of a complete `Shared.Model` for the
actual returned enlargement. `Model.next` constructs its new declared base
interpretation, preserving old constants through the ambient coefficient
embedding. `Model.nextBase_parameter` identifies the new base parameter with
its prescribed ambient infinitesimal. The same returned shared target model
interprets the enlargement's cached parameter as that infinitesimal.
The enlarged target and every retained owner are the new canonical
`Context.model?` results; the rebuilt native predecessor cache and transported
old cache are coherent with that same target. The returned checked inclusion
identifies the old shared interpretation with the new target. This complete
model supports `add?`, `collect?`, and further `enlarge` calls. These agreements
are derived from the original factory model and provider history.

`Shared.presentation index value` packages the actual checked owner value as a
finite native presentation over the shared collection's declared base. The
`SharedPresentation` development adapter proves that its denotation is the
canonical original owner's value. `Shared.Model.toUnion` then enters that
value into the prescribed relative algebraic union, preserving canonical zero,
one, arithmetic, total inversion, mathematical equality and comparison.
`Shared.targetPresentation` and `Shared.targetToUnion` also cover arbitrary
computed target values, including arithmetic combining different owners. Their
operation and sign theorems use the fixed canonical target interpretation.
`Shared.Model.toUnion_coherent` identifies an original value across differently
ordered gatherings, and `algEquiv_toValue` connects its map to the mathematical
presentation quotient. A Liouville-prefix example combines nested rational-root
owners after proper real-prefix enlargement.
`Shared.union_coverage` proves that every element of that union has an actual
native root-producer entry and a successful shared gathering whose inclusion
represents it. `Shared.Model.union_extend` instead appends such an actual
producer owner to an existing gathering and preserves every retained owner's
union image. Target equality, zero, one and the base-embedding law are explicit.
`toUnion_embed` preserves a parent's image through a selected child, including
in the Liouville-prefix client. Together with `Presentation.algEquiv` and `Presentation.realClosed`,
this identifies these compatible native values with the algebraic real closed
union under the supplied base embedding. This construction uses the native
subsequence/depth compatibility check; it does not deduplicate differently encoded
equivalent roots or supply joint ordinary-real specialization.

Registration caches checked inclusions for every original algebraic predecessor.
Parent/child registration, sibling branches, and repeated owners reuse their
common roots. Exact native provenance is checked first. For a new owner,
registration validates its converted descriptor and prepares its constraints
once. It visits the images of cached generators and their negatives on demand,
including previously reused values, and skips structurally repeated candidates.
Insertion computes an original generator's image once and retains it in the
immutable cache. Extension maps these retained values once, and cache append
removes structurally repeated images.
Each candidate is tested against the defining
equation first, followed by derivative signs and strict interval bounds; the
check stops at the first mismatch and the search stops at the first full match.
A matching value becomes the owner's generator
through a proved polynomial evaluation map, retaining the exact shared target
and all existing owner/cache interpretations. A linear converted head supplies
a coefficient-field candidate, subject to the same complete constraint check.
Otherwise registration appends a selected-root level and transports the cache.
This reuses equivalent roots across different intervals, nonmonic reducible
heads, reordered chains, and independently enlarged staged owners. It does not
search arbitrary expressions of several generators for roots.
`Shared.add?_maps` describes the returned old-owner inclusions and
the appended original-owner map. A new target updates the predecessor cache
through the same sequence of root inclusions used for retained owners.

`shared.enlarge?` returns a new shared target, a checked inclusion `previous`
from the old shared target, and its cached positive `parameter`. All retained
owner maps use this one inclusion, and accessing the parameter rebuilds no root.
`Shared.enlarge?_models` carries an existing coherent collection of owner
models into one common ambient and identifies its actual infinitesimal and every
input owner's interpreted values. The result includes a coherent family whose
original models are exactly the prescribed lifts of the input family. The
`owners` field of the `Shared.Model` produced by `gather?_models` supplies this
coherent collection. `Shared.enlarge?_ordered` gives positivity and comparison
against every old positive value. Existing serialized values and polynomials
must pass the returned target's checked readers; old packets with a different
literal binding are rejected.

Run `lake build HexRealClosure.LiveContextTests HexRealClosureTheory.LiveContext HexRealClosureTheory.BaseTests HexRealClosureTheory.BaseFactoryTests HexRealClosureTheory.BaseMapModel HexRealClosureTheory.GatherTests`
for staged value transport, mixed-depth reuse in both registration orders,
alternative intervals and defining polynomials, conjugate selection, linear
roots, reordered chains, unrelated-root
position, parent/child and sibling registration, repeated owners, root-level
counts, original equations,
owner-map agreement, polynomial transport, parameter order and stale packets.
The checked inclusions also have ordinary-kernel value, polynomial and comparison
proofs; the all-owner enlargement proof uses the actual cached checked packet.

Run `lake build HexRealClosure.TowerConversionTests HexRealClosure.TowerTransportTests HexRealClosureTheory.TowerTransportTests`.
The routine native fixture checks a changed nonmonic reducible definition, a
later linear root, identity, two successive definition changes composed with
proved context reconciliation, equations and packet ownership. It also
re-encodes a descriptor from the rebuilt suffix, composes that second native
refinement, and checks its converted root equation.
`TowerTransportTests` also executes its base and one-root `#guard` checks in
routine CI, including literal serialized agreement of `Suffix.embed` with the
native root inclusion. The explicit four-level native driver is built with
`lake build hexrealclosure_transport_tests` and run with
`.lake/build/bin/hexrealclosure_transport_tests`. Routine CI type-checks this
fixture but does not execute the deep calculation.
This deeper fixture changes a nonmonic reducible first definition and rebuilds
three later square roots. It checks the sixteenth-power equation, the final
root equation, ordering, literal suffix inclusion across three roots, embedded
noncanonical one and inverse values, and old
and new packet ownership. Kernel examples cover arbitrary finite suffixes over
a validated rational-root context. Generic coefficient and comparison transfer
and root construction use the proved root-sum theorem and only the standard
three axioms. General base enlargement is itemized below. Automatic extraction
of a suffix from requested expressions or a catalog, uncached reader
completeness and full dependency-closed enlargement remain open. The presentation
quotient below identifies finite native values with the real-closed algebraic
union. No performance result is claimed.

### Infinitesimal base conversion

`Conversion.infinitesimal` maps a completed native base into a new base with
one positive infinitesimal, using the existing constant-rational-function
embedding. The conversion keeps the old base and its values valid. A native
check compares an embedded rational value and rejects a packet from the new
base in the old context. The routine native checks live in
`HexRealClosure.TowerTransportTests`; they also compare ε with zero and an
embedded positive rational, then rebuild √2 and compare expressions involving
its new generator and ε.

`Conversion.Model.infinitesimal` relates the conversion to old and new models
in one ambient field when their interpretations agree on the native embedding.
`infinitesimalHom` obtains that agreement from compatible coefficient and
rational-function homomorphisms. Under those premises, `rebuild_infinitesimal`
proves that the checked descriptor-retaining traversal succeeds for every
finite algebraic suffix. `rebuild_rational` supplies these premises for every
finite suffix over ℚ using the ordered algebraic real closure of ℚ(ε), and a
native check rebuilds a selected square root there. `rebuild_mapped` proves the
same success for any native base admitting a sign-compatible ring homomorphism
into an ordered field; it constructs the enlarged ambient internally. The
rational case is an instance of this theorem.

`Context.enlarge?` extracts a context's stored staged base and validated root
suffix, adds one positive infinitesimal to that base, and runs the checked
suffix conversion. It returns a `Conversion` from the original context when
every descriptor validates in its new predecessor. The core
`Context.enlarge?_eq` theorem identifies the exact checked suffix traversal.
In the theory companion, `Context.enlarge?_model` preserves the interpretation
`old.extend suffix` of every value through the returned conversion, and hence
its equality and order. `Context.enlarge?_exists` proves conversion success
when the extracted base admits a sign-compatible map into an ordered field.
`Context.origin_adjoin` tracks every appended descriptor in the stored origin.
`Suffix.origin_exact` proves that extraction after any validated suffix over
a staged base recovers the same descriptors in predecessor order. Consequently,
given a compatible model of the infinitesimal base conversion into a real
closed ordered field, `Context.enlarge?_suffix_model` interprets every converted
value against the canonical extension `old.extend suffix` of the supplied base
model at arbitrary finite depth. `Context.enlarge?_suffix` proves conversion
success when the staged base has
a sign-compatible ordered-field map. `Model.adjoin_unique` identifies any
compatible child model with the actual descriptor-based interpretation;
`extend_unique` propagates this identification through an entire finite suffix.
`Context.enlarge?_preserves` consequently preserves an arbitrary old model
in a real closed field from agreement on the initial base and a compatible
new-base conversion,
without further agreement premises at the root levels. Extraction performs
quadratically many old-descriptor adjoins, each preparing its Sturm domain
and encoding/parsing its frame, as described under `Context.origin` below.

`Context.enlarge?_aligned` accepts a proved equality between a stored context
and the suffix target, then identifies the returned target model with the
extension of the supplied enlarged base model through the actual rebuilt
descriptors. `Tower.Model.extend_embed` proves that this extended model agrees
with the supplied enlarged base model on embedded base values; the theorem
expresses the target alignment up to the context casts.
`Context.enlarge?_interpreted` supplies that same descriptor and target-model
alignment for an arbitrary old model from its initial-base agreement and
compatible new-base conversion. `Suffix.restrict` names the actual restriction
of an arbitrary old suffix model through the native inclusion.
`Context.enlarge?_constructed` exposes the exact rebuilt suffix and its target
interpretation through `infinitesimalMapped`, using that restriction.
`enlarge?_ambient` is its simpler existence corollary.

General `Context.enlarge` still requires assembling the algebraic restriction
and staged-order results with dependency closure. The interpretation ingredients are:

1. Relating an arbitrary old model to a chosen `B`-algebra map, proving
   agreement on its base coefficients and algebraicity of every value. For a
   canonical base model extended through a validated finite suffix,
   `Tower.Model.baseRestrict` constructs the restriction and proves value and
   base-map agreement. `Context.origin` supplies the suffix presentation of
   each packed context up to equality with that context; identifying an
   arbitrary old model follows from `Model.extend_unique` after restricting
   it to the base through `Suffix.restrict`, using a reference interpretation
   in an independent real closed field. `Suffix.restrict_eq` proves independence
   from that reference. `Model.baseHom` extracts the actual coefficient
   homomorphism, and `Model.base_baseHom` reconstructs its entire base model.
   `Model.suffix_algebraic` proves every value of an arbitrary old model in a
   real closed field is algebraic over this extracted map. A sign-compatible
   base map remains an explicit semantic premise: raw base contexts do not
   carry ordered-field laws for their sign function. `enlarge?_hom` constructs
   the reference from such a map through `Ambient.ofField`.
   Packaging the union with `Ambient.ofUnion` also requires an order-preserving
   base map and a real-closed old ambient; its current API places both fields
   in the same universe.
2. Constructing a coefficient map for the restricted old tower model and
   proving its `Tower.Model.liftInfinitesimal` interpretation agrees on base
   values with the base model supplied by `infinitesimalMapped`. Their later
   root extensions are identified by `Model.extend_unique`; `map_extend`
   separately characterizes the ordered ambient embedding through a suffix.
   `Ambient.mappedNativeHom` interprets `B(ε)` in the enlarged ambient field,
   preserving coefficients, `X` and signs. The semantic `mappedHom` also
   preserves order for an ordered coefficient-field embedding.
3. Proving agreement of mapped towers with descriptor-based re-extension at
   every root level. `Descriptor.root_map` and `Descriptor.root_comp` in
   `HexSignDetTheory.Embedding` supply selected-root correspondence through
   ordered field embeddings. `Context.enlarge?_aligned` identifies the
   executable re-extension target with its supplied enlarged base model.
   `Model.map_adjoin` and `map_extend` prove that the actual stored child
   values and every validated finite suffix commute with that ordered ambient
   embedding. `Context.enlarge?_mapped` preserves an arbitrary compatible old
   model through the ordered embedding when supplied a compatible new-base
   conversion. `enlarge?_ambient` extracts its initial
   base interpretation and constructs the actual new-base model in an ordered
   algebraic ambient over `R(ε)`, without a caller-supplied agreement at later
   roots or a compatible new-base model. It requires a reference base model
   in an independent real closed field for the restriction proof;
   `enlarge?_hom` supplies this reference from a sign-compatible base map.
   The old model can live in any ordered field and determines the resulting
   coefficient homomorphism. `Model.suffixRestrict` constructs the actual
   relative algebraic-union model of an arbitrary old model in a real closed
   field. Inclusion preserves every old value; `suffixRestrict_baseHom`
   identifies its initial coefficient map, and `suffixRestrict_algebraic`
   proves the resulting infinitesimal ambient is algebraic over the mapped
   native `B(ε)` field, without requiring the whole old ambient to be
   algebraic over `B`.
4. `Context.enlargeWithParameter?` returns both the actual conversion and its
   parameter from one reconstruction. Its conversion projection agrees with
   `Context.enlarge?`; reading the parameter never reruns root validation.
   `Context.enlargeWithParameter?_ordered` proves this returned parameter
   positive and below every positive old value carried through its conversion,
   using only a lawful reference model of the initial base.
   `Conversion.parameter` supplies the new base parameter,
   and `Rebuilt.parameter` uses the cached initial inclusion carried by
   `rebuild?` through every actual child. It reuses each child’s native
   embedding without encoding or parsing that converted child’s descriptor
   frame again. `Context.origin` appends each descriptor by traversing every
   existing prefix: at depth n, this makes n(n+1)/2 old-descriptor adjoins,
   each encoding/parsing its frame and preparing its Sturm domain again.
   Recursive source indices in `rebuild?` add one further old-descriptor
   adjoin per level. These costs remain in the producer as a whole.
   `infinitesimalMapped_parameter` and `Rebuilt.parameter_value`
   identify that stored value with the same ambient indeterminate used by
   the sign-preserving new-base interpretation. `enlargeWithParameter?_model`
   carries an arbitrary old ordered-field model, the exact target alignment
   and the parameter’s ambient value. `enlargeWithParameter?_algebraic`
   combines preservation through the old model’s union restriction,
   algebraicity of any enlarged ambient over the same native new-base map,
   that target alignment and the returned parameter’s value and order.
   Native order follows from the model over the entire restricted old
   field’s infinitesimal extension. `Model.suffix_infinitesimal` also applies
   the local algebraic bound when a parameter is only known smaller than
   positive values of the initial base map; this supports comparisons in
   other compatible ambient interpretations for dependency closure.
5. `Shared.gather?_models` constructs coherent original-owner interpretations
   and predecessor-cache models for compatible live contexts. Its factory
   derives source coefficient agreement from the target provider history;
   `Shared.Model.enlarge` constructs the whole enlarged factory model,
   including canonical owner interpretations and coherent predecessor caches,
   through one actual shared enlargement. `Context.origin` extracts each
   exact base and validated root suffix. Reuse recognizes exact native
   predecessors and checks cached generator images, their negatives and linear
   coefficient-field roots against the full converted descriptor. Covered
   equivalent intervals and reordered algebraic chains add no root level;
   arbitrary expressions in several generators are not searched. Compatible
   real-key permutations remain outside the subsequence check.
   `Shared.Model.enlarge` re-establishes the canonical model, original owner
   interpretations and predecessor cache against the next staged realization
   and lifted reference. Finite operand requests use the interface below.

### Finite live requests

`Tower.Live.Frame owner` retains values, polynomials and checked descriptors
in their immutable owner. A `Request` is an ordered finite list of these
frames. `rootRequest` retains a selected root's defining descriptor in its
predecessor and its actual cached child generator. Each owner supplies its
validated coefficient ancestry through `Context.origin`.

`Request.gather?` gathers that complete ancestry once, using the shared
predecessor cache, and transports every frame through its retained inclusion.
It validates every descriptor again against the actual common target.
`Collection.enlarge?` rebuilds that shared suffix once after adding an
infinitesimal, then transports the current frames through the previous target's
inclusion and refreshes their descriptors. The proved transport composition
retains the original producer certificate without recomputing its historical
maps. This incremental branch checks that the predecessor inclusion maps
zero to zero; otherwise the producer retains a full transport fallback.
The semantic inclusion proves zero preservation, and native tests check the
incremental branch at both enlargements. The enlargement retains
one map for the previous shared target and maps for all original owners;
`Enlargement.maps` identifies their compositions. `Enlargement.collection`
retains the original request for further enlargement.

The companion proves gathering success from the canonical staged base
factory and native subsequence compatibility. It proves enlargement success with
a complete canonical model of the returned collection. At every original
frame position, the actual produced values, polynomial coefficients and
selected roots retain their interpreted lists in one common model.
`Collection.model` interprets an actual gathered result through that factory.
`Collection.enlarge?_models` retains the new parameter identity and the
checked predecessor model; `Enlargement.semantics` preserves the ordered
frame lists across that enlargement in the lifted old model.
`Collection.root_agreement` identifies the actual child value of a root pair
in a request equal to `pre ++ rootRequest root ++ post` with the root selected by its refreshed predecessor
descriptor. Both interpretations come from the collection's canonical factory;
no root-agreement premise is supplied. The theorem also retains the parent model from the canonical factory at the
current reference and equality with the original selected descriptor root. It also applies to the collection
returned by enlargement. `Enlargement.model` retrieves that new canonical
model through the public collection interface for the next enlargement.
`model_parameter` identifies its new parameter and `model_previous` retains
the checked old-target inclusion aligned with that same returned model.
`Enlargement.preserve` states complete frame-list preservation using those
public accessors; `Enlargement.root_agreement` identifies a selected root
inside a composite request through the returned canonical model. A request
split equation locates either root pair without casting the collection or
its enlargement. `Collection.roots_twice` starts with a gathered composite
request, obtains each public returned model, and proves that both final selected
roots equal their starting interpretations through the two actual coefficient
embeddings. It retains the starting factory equations as conclusions.
`Collection.frame` provides total access by an original request index, with
`frame_eq` identifying it with the returned frame list. Public projection
equations identify the enlargement's collection frames, previous map and
parameter with its checked packet.
Native tests gather a selected parent and dependent child in reverse order,
transport computed values and coefficients, perform two enlargements, check
fresh descriptor bindings and reject stale descriptors and serialized values
and polynomials. The original contexts remain usable.

The native `gather?` compatibility check requires each owner's constants to
form a subsequence of the shared base and its infinitesimal depth to fit.
Paths such as `[a]` and `[b]` can both enter an already validated `[a,b]` base.
Constructing a joint target from incomparable key sets, and transporting
permutations such as `[a,b]` and `[b,a]`, remain required. Separately,
simultaneous finite sign realization at an ordinary real point through
arbitrarily interleaved algebraic and infinitesimal stages remains an issue-wide
requirement; the ambient `Model.next` interpretations here do not assert that
ordinary-real conclusion.


The companion module `HexRealClosureTheory.SharedRealization` specializes
actual shared collections at one ordinary-real interpretation.
`Shared.realize_values` takes the successful native gather, the target's
provider history and finite requests indexed by their original owners. It
constructs one target reader and closed arithmetic domains pulled back through
all retained inclusions, preserves every requested sign and inherited real
coefficient, reflects zero on the requested operands, and identifies reads of
values equal in the shared context. A direct base-coefficient clause fixes
`shared.input.value b` at its prescribed real value without an origin cast.
Optional finite target requests also retain signs, domain and zero reflection.
The result uses `Shared.Realized` with named fields for arithmetic, inventories,
coherence and fixed coefficients. `Enlargement.Realized` extends the returned
collection’s `Shared.Realized`, retaining all owner arithmetic and replay laws;
its model form adds `ModelRealized.representativeFixed` for carrying arbitrary
representatives through successive factory models. Consumers use these fields
without depending on the order of the contracts.
The owner coefficient clause fixes values inherited from each original owner's
provider history through `shared.value index a`. Checked base subsequences
preserve the prescribed values even when the prefixes were validated separately.
No ambient model or separate source-agreement premise is supplied.

`Live.Collection.realize` collects each original frame's values, stored
polynomial coefficients and actual finite descriptor/replay inventory. Its
zero-reflection clause supplies the inventory agreement required by
`Transport.Inventory.descriptor_data`.
`Live.Enlargement.realize` covers requested old computed target values,
caller-requested fresh expressions involving the new parameter, and the
parameter itself after checked enlargement. The parameter has a positive
ordinary value; every requested fresh sign is preserved, including finite
inequalities between the parameter and old values. The old reader is the
pullback through the returned predecessor inclusion, so its arithmetic on the
domain and requested signs remain coherent with the enlarged reader. The same
reader fixes every original provider coefficient through
`previous.value (original.shared.input.value b)` at its prescribed real value,
without an origin cast or a native equality premise. It also retains the
enlarged origin's inherited real coefficients and identifies any values equal
in the enlarged context. `Enlargement.realize_model` uses the previous
canonical factory model and applies again after any earlier enlargement.
Its coefficient clause accepts any old operand whose canonical semantic value
is the inherited constant. `Enlargement.model_constant` identifies a carried
coefficient with the next base constant. `Enlargement.model_previous_value`
relates every carried operand to its preceding model, so the fixed-coefficient
clause composes through any number of successive predecessor maps.
`Enlargement.realValue_step` carries both the prescribed value and canonical
model agreement into the next base in one call. The new base input and original owner coefficients
also retain their prescribed values. `Model.read_eq_zero_iff` supplies zero reflection
from domain membership and native sign agreement for model-level consumers.
`Inclusion.Model.fieldHom` and `read_comap` expose the underlying semantic-field
inclusion and reader law; native expressions themselves acquire no field instance.

Each specialization chooses a new ordinary reader for the complete requested
finite inventory. Callers retain earlier sign constraints by including their
old computed operands in `values`; an already chosen ordinary reader is not
extended. `Collection.inventory` gathers refreshed target-side replay operands
for the optional `extra` or `fresh` requests.

These are relative semantic theorems. They internally construct symbolic
ordered real-closed references from provider histories. The direct accepted
finite-replay `Sample.realizeReplay` theorem, general interleaved export
assembly and construction of arbitrary jointly compatible real bases remain
required work. These theorems do not replace those contracts.

Run `lake build HexRealClosureTheory.SharedRealizationTests` for public
consumers deriving old sum/product and fresh parameter-expression signs,
usable descriptor transport premises before and after enlargement, and
specialization after two actual enlargements without a new gather.
`separate_providers` registers a second constant after a different prefix and
gathers an independently validated single-constant owner, with aligned
infinitesimal stages. `target_replay` derives descriptor transport premises
from every refreshed frame using the target-side inventory.
`lake build HexRealClosureTheory.NativeRealizationTests` additionally checks
an actual gather and enlargement over a registered Liouville coefficient,
recovering its prescribed value under the same positive-parameter reader,
through three successive predecessor maps with a fresh cross-term sign, and
through a nonempty gathered owner with a producer-built algebraic suffix.
The owner is gathered through a nonidentity base inclusion; a nonempty frame
then requests its coefficient and a polynomial through another enlargement.

When the old coefficient field `R` is algebraic over `B`, `Ambient.mapped_algebraic`
proves that its ordered algebraic real closure of `R(ε)` is algebraic over the
mapped `B(ε)`. The proof combines Mathlib's algebraic polynomial-extension
and fraction-field theorems, transports them through the executable equivalence,
then uses transitivity of algebraicity. It applies after restricting a merely
real-closed old ambient to its relative algebraic union.
`Ambient.mappedNative_algebraic` states the same result with the native field
dictionaries used by checked tower conversion. `Ambient.nativeHom_algebraic`
transports the old ambient's algebraicity across the native rational-function
field-dictionary cast.
`exists_base_lower` proves that every positive element of an ordered algebraic
extension has a smaller positive element from the base, using an ordered-field
polynomial root bound without an Archimedean assumption.
`exists_mapped_lower` gives the corresponding conclusion when the coefficient
field has no separate Mathlib order. `infinitesimal_lt_algebraic` then shows
that a parameter smaller than every positive base image stays below every
positive element of the old algebraic field. Kernel examples instantiate
algebraicity with actual ordered algebraic ambient models, including the native
ℚ(ε) dictionary cast, and derive the bound inside a relative algebraic closure
from inequalities known only over its base.
The returned native parameter’s interpretation and order are identified by
`Context.enlargeWithParameter?_model`; the cross-context assembly remains.

`Context.origin` recursively follows a packed tower's stored predecessor
chain and returns its staged base, the ordered validated root suffix, and an
equality with the original context. The suffix retains the stored descriptors,
but extraction itself rebuilds old prefixes while appending them, with
quadratically many old-descriptor adjoins; each prepares a Sturm domain and
encodes/parses its frame. The erased equality proof shows that each stored
frame equals the frame returned by total adjoin. No signature or serialized
payload is trusted as a root.
Executable guards count the extracted levels in the base and a one-root
context and rebuild the extracted one-root suffix. The existing four-root
transport fixture includes a deeper count check and runs outside routine CI.

### Sections and sectors

`Tower.Sample.section` constructs a section from a validated descriptor and
retains its cached root context, ordinary native value and coefficient
conversion. `Sample.signs` evaluates a polynomial family through that actual
conversion. `Cell.contains` checks section equality or strict sector membership
using native comparison.

`Sample.family context polynomials` obtains the complete roots of each nonzero
polynomial. It sorts and deduplicates their native root handles before
constructing any shared arithmetic context. Zero polynomials contribute no
boundary. `Family.sections` reuses each root's cached context. `Family.sectors`
constructs the two exterior rays and each intervening bounded sector in their
own immutable contexts: a ray needs one boundary root, and a bounded sector
collects exactly its two boundary roots. Midpoints of adjacent native values
handle bounded sectors; offsets by one handle rays; zero handles the root-free
whole line. Infinitesimally close roots need no separating rational.

`Family.sector?_eq` identifies an indexed result with its original region.
`Family.mem_cells` connects original boundary and sector labels to the complete
cell list, and `Region.sample_section` identifies the cached section sample.
`Context.Poly` is a reducible alias of `DensePoly context.Value`, allowing its
existing polynomial operations through the public interface.

`Family.sector?` selects a cell label before constructing its sample and rejects
indices beyond the complete family. `Family.sectorBetween?` compares requested
root handles with the adjacent complete boundary list, then constructs only
the accepted sector. It accepts semantically equal endpoints represented by
different valid descriptors and rejects reversed, missing and non-adjacent
boundaries. Finite endpoints remain owned by their original root contexts.
`Region.sample` constructs a candidate for an explicitly supplied region; its
bounded-sector membership requires strictly ordered endpoints. `Family`
producers discharge this condition. `Region.endpoints?` exposes a sector's original endpoints; `Family.cells`
describes exactly the returned section and sector samples.

`HexRealClosureTheory.LocalSample` proves complete boundary coverage, strict
ordering and unique cell membership for every point of any compatible real
closed ordered field. Each actual local sample has a coefficient-preserving
interpretation, passes native cell membership and computes the sign of every
input polynomial throughout its entire sector, including zero polynomials.
The proofs use the actual complete root producers and local conversions;
callers supply no root-coverage or sign-agreement hypotheses. Checked endpoint
requests retain the exact interpreted requested interval, and every actual
adjacent sector succeeds. `Family.cell_signs` states the computed signs directly
in terms of original-model cell membership; `Family.sectorBetween?_signs` does
the same for requested intervals. These compose with unique cell coverage
without identifying separate existential interpretations. `Family.sections_correct`
retains each actual section boundary and its computed signs. Public membership
lemmas cover bounded sectors, both
rays and the whole line. Ordinary-import consumer tests exercise these APIs.

Native tests cover irrational duplicate roots, the three real roots of an
irreducible cubic, a mixed quadratic/quartic family, zero and constant
polynomials, invalid boundary requests and an infinitesimal gap. The local
contexts include at most two added root levels. Sorting uses native root
comparison over the original predecessor; reverse insertion takes linearly
many comparisons on ascending input and quadratically many in the worst case.
An indexed request traverses the region list. Endpoint requests search that
list using native root comparisons; requesting every sector by endpoints can
repeat quadratically many comparisons, but constructs each accepted midpoint
only when it is requested.

`Sample.partition` provides a separate complete partition for callers needing
one common arithmetic context for all roots. Its `Partition` samples and
checked requests have the same membership and constant-sign guarantees in
`HexRealClosureTheory.Sample`. It collects all roots before deduplication,
which can increase depth and extension degrees; duplicate descriptors are not
shared. Its boundary requests construct all sector midpoints before searching.
The local `Family` interface avoids collecting unrelated roots for a sample.

`hexrealclosure_sample_conformance` exports six actual families with their
complete contexts, converted input coefficients, sample values, cells and sign
vectors. The independent pinned Z3 RCF oracle checks the complete distinct
boundary lists, every section and sector, strict membership and computed signs.
It includes an infinitesimal gap over a selected algebraic predecessor.
Twenty-three oracle tests check valid fixtures and reject changes to boundaries,
points, contexts, transported coefficients and signs. The emitter also rebuilds
every local context and reads each stored point through the checked native reader.
Run `lake build hexrealclosure_sample_conformance`, then
`.lake/build/bin/hexrealclosure_sample_conformance | python3 scripts/oracle/real_closure_samples.py`.
The oracle checks exact semantics; it does not independently replay polynomial
certificate graphs or certify canonical fraction syntax.

Joint specialization of nested selected roots and successive infinitesimals
to one ordinary real assignment and the full performance evaluation remain
separate obligations.

## Native scalar signs and nested replay

Native selected-root arithmetic reduces high-degree sign queries by the existing
positive pseudo-remainder while retaining the clean-storage policy. Constant
queries use the predecessor sign directly. A linear query can use its finite
endpoint signs when they agree strictly or one endpoint value is zero. If the
prepared interval contains exactly one head root, one prepared Sturm query gives
the scalar sign. The prepared root count is cached when the immutable context
is constructed; a constant or zero reduced query uses its predecessor sign.
Intervals with several roots retain the existing selected-sign
BKR producer and Thom constraints. Companion proofs preserve the same
selected-root interpretation over arbitrary ordered real closed fields.

The isolation conformance emitter includes an actual two-level algebraic tower
over two successive infinitesimals: α² = 2 + ε₁ and β² = α + ε₂, with both roots
selected in (1, 2). It exports checked selected-sign certificates for each query
as separate per-query certificates at each common selected root, byte-replays them through the native DAG reader,
and reconstructs every stored value from the empty catalog. It checks inverses,
a defining-equation zero, and rejection of stale contexts, false consumer signs,
cycles and false integer denominators. A query crossing the second root interval
checks the scalar Sturm shortcut over the actual infinitesimal coefficients. The independent pinned Z3 real-closed-field
checker verifies the selected roots, signs, context equations and integer table
identities. The native checker replays the complete polynomial certificates;
the Python checker does not independently replay every pseudo-remainder step.
This fixture establishes exporter/checker integration; it does not prove the
general simultaneous ordinary-real realization theorem or Phase-4 performance.

## Ordered algebraic ambient models

`Ambient.ofField K` in the companion consumes Tau Ceti's proved ordered
real-closure existence theorem. Its carrier is real closed and algebraic over
the actual strictly monotone inclusion of `K`. Every ambient element comes
with a nonzero polynomial over that embedded base that vanishes at the element.
The inclusion preserves zero, arithmetic, order and signs. This is a semantic
construction and supplies no executable field instance on raw selected-root
representations.

`Ambient.infinitesimal K` applies this construction to the canonical ordered
rational-function field. The companion proves existence of a positive square
root of the new infinitesimal strictly above it and below every positive
embedded predecessor coefficient. Its reciprocal exceeds every embedded
integer. The checked construction examples use one and two infinitesimal
levels, including a square root of the second infinitesimal below every power
of the first. All these statements consume the actual chosen ambient model.
`Ambient.nativeHom compatible model` interprets one executable fraction level
through its proved field-dictionary equality. It preserves arithmetic, zero
and the native infinitesimal sign; the separate caller test uses the actual
core rational dictionary without changing caller instance priorities. The two-level
construction examples use the semantic coefficient dictionaries.

`Tower.Model.map` carries an interpreted native tower through a strictly
increasing field homomorphism, preserving its values and sign law.
`Ambient.coefficientHom` includes any ordered field as constants in a supplied
ordered algebraic real closure of its infinitesimal extension.
`Ambient.mappedHom` maps a smaller ordered coefficient field's rational
functions into that same closure. It agrees with `coefficientHom` on constants,
sends the native `X` to the semantic infinitesimal, and preserves signs and
strict order; a kernel example uses ℚ(δ) inside the real closure of ℚ(ε)(δ).
`Ambient.mappedNativeHom` transports this map to the executable carrier using
the proved field-dictionary equality. `Conversion.Model.infinitesimalMapped`
uses its constant and sign laws to interpret the native base conversion in
that common ambient field from any matching base coefficient map.
`Tower.Model.liftInfinitesimal` uses `coefficientHom` to interpret the whole old tower
in any supplied ordered algebraic real closure of `R(ε)`; `Ambient.infinitesimal R`
supplies one such choice. `Ambient.X_pos` and `X_lt_coefficient` prove
the semantic ε is positive and below every positive old coefficient, while
`liftInfinitesimal_X_lt` applies that bound to interpreted tower values. The
remaining dependency-closed transport obligations are listed above.

The native presentation quotient below identifies finite native tower values
with the algebraic union; item 1 above restricts the semantic ambient field.
Simultaneous realization through arbitrary interleaved algebraic and
infinitesimal stages remains open.

### Two infinitesimals with native selected-root evidence

`Specialize.Native.nested_selected` composes native coefficient dictionary
transport, an ordered embedding of the base field into ℝ, and both
infinitesimal specializations. It constructs one checked real descriptor and
replay for the actual native descriptor and its ordered query list. The same
positive parameters preserve every recorded selected query sign and the
complete sign list of any requested finite coefficient set. The second
parameter is smaller than the first, and the first can be chosen below any
positive cap.

`CoefficientEmbeddingTests.ordinary_selected` applies this public theorem to
all head and query coefficients of a checked descriptor over two native
rational-function levels. General realization through arbitrarily interleaved
algebraic and infinitesimal stages remains open.

### Finite signs at an ordinary real parameter

`Specialize.polynomial_sign` proves that a real polynomial near zero on the
positive side has the sign of its lowest nonzero coefficient. The zero
polynomial retains zero sign. `finite_signs` supplies one positive neighborhood
for any finite family, and `exists_parameter` chooses one ordinary parameter
below a prescribed positive cap satisfying all those signs together.

For semantic fraction data with real coefficients, `fraction_sign` connects
evaluation of the actual native numerator and denominator to
`Hex.OrderedFn.Infinitesimal.sign`. It also preserves the nonzero denominator.
`finite_fractions` collects all these signs and denominator guards into one
neighborhood. `exists_fraction_parameter` chooses one ordinary real parameter
for the whole finite collection. The external square-root example uses that
same parameter for a positive square root whose square is the parameter and
which lies strictly between it and one.

For any coefficient field with a prescribed strictly increasing embedding into
ℝ, `polynomial_sign_map` preserves the lowest-coefficient sign after mapping
the polynomial's coefficients. `fraction_sign_map`, `finite_fractions_map` and
`exists_mapped_parameter` apply this to the actual native fraction data over
that field. All signs and denominator guards hold at one common parameter.
The rational-base consumer uses the actual rational cast and combines those
same guards with the positive-square-root equation and strict inequalities.
`evalMapped_add` and `evalMapped_mul` preserve actual native sums and products
under the two operand denominator guards. `evalMapped_eq_eval` identifies
the helper with Mathlib’s rational-function evaluation. `evalMapped_neg`, `evalMapped_sub`,
`evalMapped_inv` and `evalMapped_div` cover the remaining field operations,
including the native zero-input inverse. Polynomial fractions, coefficient
constants, the indeterminate, zero, one and natural/integer casts specialize
through their actual native definitions. Inversion and powers commute with
evaluation at every parameter, including poles; their identities need no
denominator guards. Division needs guards for its first operand and the
inverse of its second operand.
Finite-family consumers collect operands and results before choosing their
parameter, so arithmetic identities, all recorded signs and all denominator
guards hold at the same point.

`fraction_sign_with`, `finite_fractions_with` and `exists_parameter_with` use
the actual predecessor sign function, given its agreement with the prescribed
coefficient embedding into ℝ; this does not provide an embedding for an
infinitesimal predecessor field. A native rational infinitesimal-context consumer reads
its stored fraction through the existing proof of equality of the complete
native and semantic coefficient dictionaries, and preserves that element's
actual stored sign at an ordinary real parameter.

Evaluation of polynomial representatives at an algebraic root, recursive
algebraic replay specialization and successive infinitesimal parameter choices
remain required finite-sign realization work. These helpers
operate on coefficient data with a supplied ordered embedding into ℝ in the
companion; they add no native constructor or runtime field instance for formal
real expressions.

`Specialize.polynomial` substitutes one parameter into an outer polynomial's
actual stored native fraction coefficients. `polynomial_coeff` includes
implicit zero coefficients outside the stored array. `polynomial_zero`,
`polynomial_degree` and `polynomial_leading` require zero reflection only on
that finite array. `polynomial_signs` derives these conditions from one common
neighborhood preserving its coefficient signs and denominator guards.
The signed-chain and Tarski-query transport theorems obtain their guards from
`finite_fractions_map` applied to each certificate's own finite inventory.
The complete replay transport below preserves its checker evidence.

`Specialize.regularRing` contains the native fractions whose canonical
denominators remain nonzero under one prescribed coefficient embedding and
parameter. `evaluation` is a proved ring homomorphism on that ring. The ring
can contain nonzero fractions whose evaluation is zero. Using the actual
native-to-polynomial correspondence, `polynomial_add`, `polynomial_mul`,
`polynomial_sub`, `polynomial_scale`, `polynomial_derivative` and
`polynomial_eval` specialize those operations under the finite input
coefficient guards; scaling also guards its scalar and endpoint evaluation
also guards its endpoint. Closure handles accumulations of ring operations.

`RemainderStep.specialize` substitutes the literal stored scales and quotient.
`check_specialize` proves that an accepted signed recurrence remains accepted
when its finite coefficients and scales are regular and both scale signs are
preserved. `SignedRemainderChain.specialize` substitutes the stored entries
while retaining degree data for validation; its `fractions` family collects
the literal coefficients and scales. Its `check_specialize` preserves the
complete checker, including initial and terminal identities, nonzero entries,
degrees and strict descent. `specialize_near` supplies one common positive
neighborhood for all these conditions.

`TarskiCertificate.specialize` maps literal polynomial and endpoint data while
retaining context, sign arrays, variations and the integer query value.
Its `fractions` includes the two chain inventories, endpoint differences,
endpoint polynomial evaluations and infinite-endpoint leading coefficients.
`check_specialize` preserves all literal bindings, endpoint nonroot/order
guards, the squarefree check, both chain replays and recorded signs and
variations. `specialize_near` preserves the complete accepted certificate
throughout one positive neighborhood. These theorems use a prescribed ordered
embedding of the predecessor coefficient field; recursive algebraic replay and
successive infinitesimal specialization remain separate obligations.

`SignDet.ReductionStep.specialize` substitutes an indexed positive product
reduction's stored remainder, scales and quotient. Its finite inventory covers
the input head, previous representative, factor, next representative and
witness. `check_specialize` preserves the actual factor index, both positive
scales, the zero/degree bound and the product identity without guarding
intermediate products. `Reduction.check_specialize` preserves every matched
factor and step, the positive-degree/exponent guards and the final declared
query polynomial. `QueryReduction.check_specialize` preserves the original
ordered preprocessing slots, including duplicates. Each complete reduction
has one common positive specialization neighborhood.

`Specialize.polynomial_natPow` and `moment_specialize` preserve actual binary
powers and the moment product fold from only the input coefficient guards.
The regular ring contains every intermediate accumulator. `checkMoment_specialize`
preserves the actual direct or reduced query, complete Tarski evidence and
integer value.

`SignDet.Node.specialize` maps literal coefficients and endpoints while
retaining its integer system, rank evidence and moment positions.
`Node.check_specialize` preserves all bindings, matrix checks, shared
preprocessing and complete moment checks. `Replay.check_specialize` preserves
the entire supplied BKR tree with its exact child query slices, including
empty supports. Its extracted sparse rows and every condition's count stay
unchanged. `Replay.table_near` provides one positive neighborhood whose real
parameters all admit that same checked table. These theorems require the
prescribed ordered coefficient embedding into ℝ. Evaluation of polynomial
representatives at an algebraic root, DAG sharing, recursive algebraic replay
and successive infinitesimal specialization remain separate obligations.

`Specialize.counts_near` uses the proved root-count meaning of the specialized
BKR replay over ℝ. At every parameter in one positive neighborhood, the
actual real-root count equals the source table count for every ordered sign
condition. `exists_near` realizes each condition of positive source count at
some real root, with all its signs together.
`realizeReplay` gives uniqueness when the source table has count one for that
full condition. `realizeBelow` chooses a realizing parameter below any
prescribed positive cap. These theorems use the same parameter for every
polynomial and endpoint and require a prescribed ordered embedding of the
coefficient field into ℝ. They do not construct recursive algebraic samples or specialize an
infinitesimal predecessor field.

`Specialize.selected_near` consumes the existing checked `SelectedSigns`
evidence. All requested query signs hold at one ordinary real root, which is
unique among roots matching the descriptor's entire specialized query prefix.
The proof excludes other roots with that prefix even when their remaining
signs differ. It specializes the literal ordered query polynomials; it does
not rebuild the formal-derivative bindings itself; the descriptor construction
below supplies that step.

`derivativesFrom_specialize` and `derivatives_specialize` commute with the
actual native formal derivative sequence. Original head coefficient guards
suffice: every iterated derivative stays in the regular coefficient ring.
`RawDescriptor.specialize` retains context, derivative indices and signs while
substituting its head and endpoints. The recomputed queries match the mapped
original queries, including default zero reads at malformed indices.
`check_specialize` preserves the complete descriptor checker.

`Descriptor.specialize` constructs a validated real descriptor through the
existing `ofTable` API. `specialize_checked` proves that checking the exact
mapped raw descriptor and mapped replay returns this result. One positive
neighborhood supplies these validated descriptors and their actual recomputed
formal-derivative queries. `selected_root_near` proves that all signs returned
by source `SelectedSigns` hold at the root of the validated specialized
descriptor, using the same parameter for both evidence tables. These are
companion constructions over a prescribed ordered coefficient embedding into
ℝ; they do not rebuild a native tower context or specialize successive levels.
`specialize_evidence` proves that the returned descriptor's evidence field is
the entire mapped original replay, using the public `ofReplay_data` equation.

`Specialize.Native.evidence` transports the whole descriptor, query list and
checked selected-sign replay through equality of the predecessor coefficient
dictionaries. Public heterogeneous-equality equations identify its descriptor,
ordered queries and checked selected-sign certificate with their sources.
`Native.selected_root_near` then constructs the checked real
descriptor and proves its root signs. A consumer example uses the actual
native rational dictionary, its proved compatibility equation and
`Rat.castHom ℝ`, covering the first rational infinitesimal level.

### Finite coefficient interpretation

`Transport.polynomial` interprets and normalizes the literal coefficient array
without field or ring laws on its source expressions. Zero preservation handles
implicit coefficients, and interpreting `ofCoeffs` commutes with normalization
even when nonzero source coefficients denote zero. Nonvanishing of only the
interpreted top coefficient preserves stored size, degree, leading coefficient
and executable zero tests; interior noncanonical zeros are allowed.

The `Transport.Guarded` operation lemmas retain input sizes under these leading guards.
`Transport.Ring` instead assumes ring laws on the target coefficients and allows
input and intermediate arrays to shrink or become zero. Its addition,
subtraction, scaling, differentiation, multiplication and Horner proofs need finite
scalar equations only at actual coefficient positions and reached native
schoolbook accumulators. `productPrefix` and `hornerPrefix` record the precise
multiplication and descending Horner order. `PowerData` follows the native
binary-power recursion, recording each actual square and odd-exponent product.
Constants and the unit polynomial are also transported.

`Difference`, `Scaling`, `Product`, `Sum` and `Differentiation` package finite
arithmetic obligations without source or intermediate leading guards.
`Initial.zero`, `Recurrence.zero` and `Terminal.zero` transport the checker's
actual zero differences. `ChainData` requires leading guards only on the head
and stored chain entries, where nonzero and degree checks need them.
`chain_check` transports the complete signed-chain replay, including head
binding, serialized degrees, strict descent, every recurrence and the terminal
pair. No division or chain producer runs during transport.

`Closed` describes a domain containing zero, one and natural casts and closed
under addition, subtraction and multiplication, where interpretation preserves
those operations. Its coefficient membership lemmas and `ChainData.of_closed`
and `QueryData.of_closed` derive all intermediate and accumulator equations
from finite stored coefficient membership. `regular_closed` instantiates this
domain with `Specialize.Regular embedding t`; a full chain consumer and Horner
example use that partial specialization domain. `ReductionData.of_closed`
similarly derives every product reduction equation, and `reduction_check_regular`
applies it to regular fractions.
Interpretation need not preserve arithmetic outside it. Kernel-checked examples
include an interior raw representative of zero and a complete accepted
three-entry chain whose query and initial quotient lose their leading
coefficients under evaluation at two.

`query_check` transports the full Tarski certificate with an explicit context
map: all literal bindings, endpoint order and nonroot guards, both chain checks,
endpoint signs, stored variations and the integer value are retained. Each
endpoint uses its actual finite Horner arithmetic or leading coefficient sign.
Scalar sign agreement remains an explicit hypothesis at the literal scales,
finite Horner results and endpoint differences, and infinite endpoint leading
coefficients; arithmetic preservation alone does not supply these signs.
`reduction_check` also transports the complete native product reduction,
retaining literal factor indices, scales, quotients and final result. A result
may shrink or become zero; only the original head requires degree preservation.
`preparation_check` transports shared query preprocessing, keeping original
query positions and duplicate operands. `Closed.coeff_natPow` and
`PowerData.of_closed` follow the actual binary-power recursion. `moment_polynomial`
interprets its powers and product fold from finite query memberships, and
`moment_check` retains every direct or reduced moment clause.

`node_check` retains literal context and input bindings, shared preprocessing,
all indexed moments, the integer system, rank certificate and left-inverse
check. `replay_check` transports the supplied finite tree, both child checks and
their original positional query slices, product supports and retained rows.
`Transport.count_roots` composes this transport with the root model over a
real closed target field: the original sparse table count equals the number
of distinct roots of the interpreted head in the interpreted interval realizing
the entire ordered sign condition, including
conditions omitted from the table. Positive counts give existence through
`exists_root`, and count one gives uniqueness through `unique_root`. These
theorems consume a coefficient reader, its closed domain and the finite
`ReplayData` obligations; they do not construct an algebraic tower reader.
`derivatives_polynomial` derives the complete formal derivative sequence from
head coefficient membership, retaining its degree under the leading guard.
`checkedDescriptor` constructs a validated target descriptor with queries
recomputed from its interpreted head, the mapped immutable context, and the
entire mapped replay. Its public projection and validation equations retain
the literal raw input and evidence. `selected` transports checked joint signs
to this descriptor, retaining the sign vector and joint replay; `selected_signs`
proves all those signs at its selected root over a real closed target field.
Joint algebraic-root interpretation, recursive sample reconstruction, graph
sharing and successive infinitesimal levels remain separate obligations.
### Relative algebraic union

The companion's `Union.field B R` uses the prescribed base algebra map into a
supplied ambient field and consists of all its elements algebraic over `B`.
`inclusion_range` identifies that image exactly. Every element belongs to a
finite algebraic adjunction, and `common_extension` places two finite sets of
algebraic generators in one common finite extension inside the same ambient.
The inclusions inherit arithmetic and order from the ambient field.

`Union.square` and `Union.odd_root` prove closure under square roots of
nonnegative elements and roots of odd-degree polynomials.
`Union.realClosed` combines those conclusions into real-closedness when the
supplied ambient is real closed. `Ambient.ofUnion` restricts a supplied real closed ambient to its algebraic
union using a required strictly monotone base embedding for the planned base
enlargement. Its packaged `val` preserves order, and `lift` admits every supplied
ambient element algebraic over the base. `Ambient.union_eq_top` applies to the actual
base map of the proved algebraic ambient. Ordinary-kernel examples instantiate
the construction for the usual rational embedding into the real numbers and
place `sqrt(2)` and `sqrt(3)` in one finite compatible extension. A two-level
infinitesimal ambient is restricted over the first rational-function base;
its square root of the first infinitesimal is included back into that ambient.

`Tower.Model.restrictUnion` carries a native tower interpretation into this
union when every context value is algebraic over the chosen `B`-algebra map;
coercing the restricted values back gives the original interpretation exactly.
The map must agree with the model's base coefficients when used for base
enlargement. `Tower.Model.base_algebraic` proves algebraicity of the canonical
base model over the algebra map induced by its selected embedding.
`Tower.Model.adjoin_algebraic_over` propagates algebraicity through an actual
selected-root extension from algebraicity of every predecessor value; a
kernel example checks three successive root levels over ℚ. Kernel examples
also restrict the rational base model from ℝ, apply the constructor to any
tower model in an algebraic `Ambient Rat`, and check that its codomain agrees
with `Ambient.ofUnion` for any permitted ordered base embedding.
`Tower.Model.extend_algebraic_over` propagates the algebraicity premise through every
validated finite root suffix; `extend_field_algebraic_over` applies it to the
final image field. `extend_base_algebraic` and
`extend_base_field_algebraic` supply both conclusions for a canonical base
model. `Tower.Model.baseRestrict` combines this algebraicity proof with the
existing `restrictUnion` construction. For a canonical base model and any
validated finite suffix, it preserves every interpreted value after inclusion
and agrees with the prescribed base map at every suffix depth. An arbitrary
old model in a real closed field uses `Suffix.restrict` and `Model.baseHom` to
extract its base map, using a reference interpretation in a real closed field
for existence of the native inclusion laws;
`Model.base_baseHom` and `Model.suffix_algebraic` derive agreement and
algebraicity for that map. `Model.suffixRestrict` constructs its actual union
model, preserving every old value and identifying the coefficient map.
`suffixRestrict_algebraic` proves algebraicity of the next infinitesimal ambient
over the native new base. Packaging these results in the total
`Context.enlarge` constructor remains open.

For any supplied native input model, `Model.roots_iff_union` identifies the
actual complete-root presentations with the relative algebraic union of its
entire value field. `Root.unionModel` interprets every value of each returned
root context there, preserving its native operations and signs.
`Context.enlarge?_constructed` preserves the old model lifted into the
infinitesimal ambient and identifies the converted target with the new-base
model extended through the actual rebuilt suffix. The total `Context.enlarge` constructor must
still assemble the proved algebraic restriction and native parameter order
with all requested live contexts in one compatible native context.

Run `lake build HexRealClosure.TowerEnlargeOrderTests` for actual enlargement
through √2 and √√2. The test calls the public producer directly and compares its returned
parameter with old generators, tiny positive rationals, positive differences,
inverses and a preceding infinitesimal. It preserves negative and zero signs
as well, and checks that
the returned signature retains the old root depth and adds exactly one
infinitesimal level. The companion consumer tests use an arbitrary old
rational tower model inside ℝ, its relative algebraic restriction, and the
actual selected-root enlargement result.

### Native finite presentations

The Mathlib-free module `HexRealClosure.TowerPresentation` exposes the stored
presentation and its computable construction/refinement wrappers. The companion
`HexRealClosureTheory.Presentation` provides interpretation and quotient proofs.

`Tower.Presentation` retains a validated finite root suffix over one immutable
native input context and an actual stored value of its final context.
`Presentation.denote` uses the original coefficient model extended through
those exact selected descriptors. `toUnion_surjective` proves that these
presentations cover every element of the relative algebraic union of the input's
whole mathematical field. It consumes actual complete native root production;
no caller supplies root coverage or chooses a single chain to stand for all towers.

`Presentation.Quotient model` identifies exactly equal denotations. Its
`ringEquiv` and `algEquiv` identify it with the relative algebraic union, preserving
field operations and the prescribed base map. `inclusion_lt` and `toValue_lt`
prove agreement with ambient order. `value_algebraic`
proves algebraicity over that base, and `realClosed` proves real-closedness.
The native zero, one, natural-number casts, addition, subtraction, multiplication, negation,
total inversion and division agree with operations on classes. Signs agree with
the same order; raw nonzero representations acquire no literal field laws.
Native coefficient inclusion through any suffix preserves its class, and
`converted_value` proves coherence given an aligned checked conversion model.
`refined_value` and `refined_suffix` discharge that alignment for the actual
root-refinement producer, including reconstruction of every later root level.
`Presentation.refine` packages refinement given the preceding and later suffixes;
`refined_at` proves class preservation without exposing the ownership casts.
The caller supplies this decomposition rather than a numeric root position.
`prepend_embed` packages inclusion coherence from any intermediate root context.
`refine?` runs the checked later-level reconstruction, and `refine?_success`
proves that it returns a presentation with the same class on valid input.
`equal_spec` links executable equality in a common suffix to class equality.
When the ambient field is algebraic over the input field,
`denote_surjective` proves that presentations cover the whole ambient field,
and `ambientEquiv` gives the resulting equivalence with the prescribed base map.

`common_suffix` supplies one validated suffix and native representatives whose
classes match any finite list of original presentations in order. It uses
complete native root production at successive compatible predecessor fields.
The representatives support actual native arithmetic and equality in that suffix.

`common_values` also places any finite list of presentation values in one actual
native collection with a common ambient interpretation. It uses complete root
production followed by the checked root-collection producer, and retains the
values in input order, together with their original root-production witnesses.
These semantic finite-value constructions do not select
or transport the full requested live dependency DAG during general enlargement.
That executable assembly, joint ordinary-real realization and Phase-4 tower
performance remain separate obligations.

The quotient fixes one ambient model and its base embedding. It lives in
`Type 1`, since the native presentation stores a packed context;
`Union.Carrier model.field K` retains the ambient universe for consumers that
need a carrier in that universe. The algebra equivalence connects the two.

Ordinary-import consumers derive cancellation for actual stored multiplication
and inversion from a nonzero native sign, check total inversion of zero, and
identify equal values at different finite depths. Kernel axiom guards report
only the standard three axioms. The Mathlib-free `TowerPresentationTests`
refines the middle root of a three-level tower whose original defining
polynomial uses an algebraic predecessor coefficient. It rebuilds the later
level, checks the refined quadratic, order, inverse and prefix retention,
and rejects the old packet. Run
`lake build HexRealClosureTheory.PresentationTests` and
`lake build HexRealClosure.TowerPresentationTests`.

`Algebraic.Element.cachedInv` and `cachedDiv` pack reciprocal and quotient
results with supplied facts for the actual retained polynomial. They agree
literally with the ordinary total operations for every fact list. Inversion
retains the existing inverse-polynomial computation; its gcd and predecessor
arithmetic are unchanged. `Algebraic.Dag.validateCached?` validates an entire
supplied graph with coefficient operations using supplied facts, then transports
each entry's erased acceptance proof to the ordinary graph interface. The
literal memo remains reducible in the kernel. The exact acceptance, rejection,
literal entries and indices are preserved. Missing nonconstant facts block
ordinary-kernel reduction, but compiled evaluation retains the native fallback.
These interfaces support proof assembly; they do not establish a compiled
checker that avoids lower-level sign searches.

`Algebraic.Element.factOne`, `factAdd`, `factNeg`, `factSub`, `factMul`,
`factInv`, `factDiv` and `factNatCast` take explicit predecessor operations
proved equal to the ordinary ones. They preserve the original element carrier
and context while using supplied facts at successive coefficient levels.
Each operation equals its ordinary counterpart for every fact list.
`Algebraic.Context.factReduce` similarly applies the original monic-division
policy with supplied predecessor arithmetic. Passing it to packing keeps
intermediate reduction on that path; the stored policy can still evaluate
native constant one. These APIs are for ordinary-kernel proof assembly and
retain the compiled native fallback.

`Algebraic.RootReplay.readDescriptor` decodes the complete root subject with
`SignRequests.readRoot`, decodes every graph entry against its exact domain,
and validates a count-one descriptor through the shared checker.
`readDescriptor_subject` preserves the full decoded subject.
`RootReplay.decodeDescriptor` parses both the subject and graph byte records
through `Codec.decodePair` before applying that reader. This differs from
`SignDet.Dag.decodeDescriptor`, which receives a typed subject and graph bytes.
`decodeDescriptor_write` preserves the reader's full result or error under the
lexical limits; `decodeDescriptor_subject` retains the decoded subject for
arbitrary accepted bytes. `readContext`
uses supplied predecessor operations to construct a context and transports its
root, canonical prepared cache and reduction policy to the original operations.
`readContext_eq` proves exact agreement with native reconstruction, including
rejection. A strict predecessor codec can require supplied stored sign facts.
These readers support ordinary-kernel proof assembly; compiled coefficient
operations retain their native fallback. The kernel demo checks the root subject
and nonmonicity, but does not evaluate the prepared cache or its root count.

The companion's `Context.readEvidenceWith?` accepts equal supplied coefficient
operations, checks the existing joint packet once, and returns proved scalar
facts in the original immutable context. `readEvidenceWith_eq` preserves the
complete accepted result or rejection for every packet, without assuming finite
fact coverage. The supplied operations can use facts from earlier coefficient
levels; missing facts block ordinary-kernel evaluation. Compiled operations
retain their native fallback. This interface does not construct a tower or
collect its context catalog. `decodeEvidenceWith` first decodes the complete
context-bound packet with the supplied predecessor codec, then applies that
reader. `decodeEvidenceWith_eq` preserves acceptance and rejection for every
byte input, including when the coefficient codec is partial.

`Algebraic.Context.changeOps` retains an existing root context under proved
literal equalities of its coefficient operations. It preserves the descriptor,
optional canonical prepared cache, root count and reduction policy. Its
`changeOps_data` theorem preserves the literal subject, root count and reduction
policy; `changeOps_reduce` and `changeOps_signPoly` identify the actual reduction
and sign functions with the original functions. `changeOps_root` retains the
complete descriptor, and `changeOps_domains` preserves the prepared cache;
`changeOps_self` identifies transport with unchanged operations. Transport changes validity
proofs without executing domain preparation. It does not reconstruct a context
from untrusted bytes or collect missing arithmetic evidence.

`Algebraic.Context.ofChecked` requires the exact canonical-cache, root-count
and reduction-policy equations used by the ordinary constructor.
The restoring factories keep their constructors private. Public projection
laws expose their stored fields; direct kernel unfolding requires the owning
module imports used by the conformance fixture.


## Number-field coordinates in the shared sample context

Import `HexRealClosure.NumberFieldTower` to retain a checked
`RealAlgebraicNumber` generator in an immutable native context.
`NumberField.present? generator registry` enumerates the native roots of the
original minimal polynomial and checks the original selected embedding.
Its companion proves success for every such generator; arbitrary complex
algebraic numbers must first pass `RealAlgebraicNumber.ofAlgebraic?`.

The returned `NumberField.Presentation` owns a context indexed by that
selection. `source.pack a` evaluates the original
`QAdjoin generator.toAlgebraic` coordinates at its retained generator.
`source.polynomial p` packs every original coefficient. `source.roots p`
and `source.roots? p` run the shared complete producer in that same context.
Zero gives `all`; nonzero roots retain the original polynomial's exact
multiplicities and selected real embedding. `source.family polynomials`
uses the shared section and sector algorithm and its checked coefficient
conversions. It returns one section for each distinct root across the nonzero
inputs and one sector in each intervening or unbounded interval.

The companion `HexRealClosureTheory.NumberFieldTower` proves presentation
success, coefficient preservation, zero reflection, packed arithmetic and
sign agreement, exact root coverage and multiplicities, strict ordering,
strict boundary order, exactly one cell at every real point, original interval
agreement, section signs and signs at every real point in each sector.
Nonzero native representatives can have different storage; `pack_add`,
`pack_mul` and `pack_inv` therefore state that the native difference is zero.
Context and value packets are read through `Tower.Catalog.reconstruct` and
the reconstructed context's checked `read`.

Run the complete examples and independent exact checks from the repository root:

```sh
lake exe hexrealclosure_number_field_samples
python3 scripts/oracle/real_closure_number_field_samples.py \
  conformance-fixtures/HexRealClosure/number-field-samples.jsonl
```

The oracle requires python-flint 0.9.0 / FLINT 3.6.0. The executable covers
∛2, the middle root of `X³−3X+1`, the actual `QAdjoin.common` field generated
by √2 and √3, and a rational generator. It checks native arithmetic, original
zero output, every sample's strict membership, reconstructed contexts and
value roundtrips. FLINT independently recovers the original generators and
coordinates, checks all converted coefficients and sign vectors, all sections
and sectors, and roots of the repeated original polynomial with their exact
multiplicities. Its checks concern selected-root semantics; native replay
and byte-reader validation remain exercised by the executable.


`NumberField.roots` retains the direct fixed-field entry point for callers
using original coordinates and a caller's context tag. `Presentation.roots`
retains a persistent native tower context shared with subsequent roots and
samples. Both call the existing complete root algorithms and both have
original-polynomial correspondence theorems.

Presentation construction is separate from arithmetic. Its current exact
generator check converts each native candidate back through the rational-base
canonical map; this can repeat isolation while finding the selected embedding.
Retain the returned presentation for repeated operations. Even a rational
generator may currently receive a degree-one root frame. These construction
costs are not cached arithmetic costs or higher-degree performance evidence.

### Original packing equations

`Algebraic.Packing` retains the original polynomial, its actual reduced
representative, native packed value and cached sign. It also retains a checked
joint selected-sign replay for `[representative, original - representative]`
with signs `[cachedSign, 0]`. A value packed to canonical zero therefore keeps
its original equation. `make?` requires the exact representative's scalar fact,
including constants; `readMemo?` reads supplied checked graph entries, and
`build?` produces the joint replay using the context's cached prepared domain.

`Element.replayPack` looks up the original key. In ordinary-kernel assembly,
every absent key stops at `Element.missing`, including constants and successful
zero tests. A record for one polynomial cannot cover another polynomial that
reduces to the same representative. Compiled fallback remains native packing;
this boundary is not a strict checker for untrusted compiled replay.

`ReplayOperations` supplies addition, subtraction, multiplication, negation,
one, natural casts, inversion and division with complete packing records and
equal predecessor operations. Their equality laws preserve the original
context's native operations and local gcd/Bézout inversion. Collection resolves
packings inside a polynomial key before requesting the outer packing. This
retains division's inverse record before its multiplication record. Native
embedding, generator constructors and numeral instances do not enter this
boundary automatically; an exporter must route those constructions explicitly.

`HexRealClosureTheory.Packing.realize_many` chooses one checked selected root
for every record in a level. At that point the packed value equals evaluation
of its original polynomial and has its retained native sign, including zero
outputs. The theorem requires only the reached finite descriptor, replay and
coefficient-subtraction data of the predecessor reader. It assumes no supplied
ambient model or globally closed interpretation domain. Constructing those
finite premises recursively through all interleaved stages belongs to the
accepted tower-replay exporter.

`KernelReplay.PackingProbe` checks literal native-produced packets with the
ordinary kernel, cached replay without production, mixed scalar/packing
inventories, wrong inventory kinds, same-value raw-equation mutations and all
eight operation boundaries. Division records its exact inverse and product
keys and replays the resulting inventories without requesting another record.

The companion module `HexRealClosureTheory.KernelReplay` provides in-process
proof assembly and collection of intermediate sign facts. `collectMany` keeps
a typed finite inventory for each coefficient context and evidence kind, routes
supplied facts by their actual type, and checks every supplied scalar fact or packing record with
Lean's ordinary kernel before insertion. The final equation refers to the inventories actually
used. A request contains its context and polynomial, rather than an inventory
kind. The supplier must know which arithmetic boundary is in use. Supplying a
fact for an existing inventory of the other kind may consume fuel without
resolving the request. Replay can supply recorded certificates without calling the producer.
The caller retains the supplied-fact arithmetic boundary and supplies the
validated contexts; this interface does not reconstruct a tower catalog.

## Printed tower values, roots and polynomials

Import `HexRealClosure.TowerBytes` for the shared JSON text and byte format.
`context.writeText value` and `context.writePolyText polynomial` retain the
whole immutable binding and every stored coefficient. The binding includes
provider names and versions, the infinitesimal depth and each algebraic
frame's defining polynomial, interval, Thom word and replay graph.
`Root.writeValueText` prints only the native value in its actual owner.
Packed values and polynomials also provide explicit `writeText` methods.
For complete root presentation, import `HexRealClosure.RootBytes` and use
`Root.writeText` or `writeBytes`: their outer binding is the original
predecessor, and the payload retains the point/selected kind and full checked
descriptor. `RootSet.writeText` and `writeBytes` retain each root and its positive
multiplicity in literal order, or the universal `all` result. These JSON packets
are separate from the constructor-syntax `Repr` contract.

`context.readText` and `readPolyText` parse through the shared UTF-8/JSON
parser, require the exact supplied binding, and invoke the existing checked
value or polynomial reader. `Catalog.restoreElementText` and
`restorePolynomialText` retain the actual reconstructed context with the result.
Their byte counterparts accept the same packet as a `ByteArray`. Catalogs
retain caller-validated provider prefixes and their progress premises;
reading a provider name does not manufacture those premises. Unknown providers
and incompatible versions remain errors. Uninstalled algebraic suffixes use
the existing frame/replay reconstruction over a known base.

The byte and text roundtrip theorems return the exact original native value
or polynomial. `FrameRoundtrip` and `RootBytes` also prove fresh-context
roundtrips from a base-only catalog: supply the actual validated origin base,
without installing any algebraic suffix. This retains the exact context and
every original root descriptor, canonical child and predecessor embedding,
as well as root-set multiplicities, literal order and `all`. The result directly
preserves interpretation in every model of the original native context.
The unconditional shared-printer/parser
packet theorem also retains the complete structured JSON before semantic
reading. Lexical resource limits are an explicit reader policy: the typed
roundtrip theorems require `Codec.checkBytes` to accept the printed packet,
with no assumed parser success. Callers can supply larger limits for larger
native packets. Stale bindings, malformed stored values and trailing literal
polynomial zeros are rejected. These limits bound lexical input; they do not
bound certificate replay or coefficient-sign recomputation during uninstalled
context reconstruction.

Run the actual text and byte examples:

```sh
lake exe hexrealclosure_bytes_conformance
python3 scripts/oracle/real_closure_bytes.py \
  conformance-fixtures/HexRealClosure/bytes.jsonl
```

The native executable exercises rational data, both point and selected roots, a reducible-root
inverse, nested algebraics, successive infinitesimals, escaped Unicode
provider names and unknown-provider rejection. The independent Python JSON
parser checks the emitted value and polynomial packets; root helpers are checked
by the native executable. It checks agreement of printed packets with the structured JSON emitted
beside them, their top-level signature and frame field structure, frame/stage
counts and expected native observations. It independently checks literal
rational and Unicode data and
the first reducible defining head. It does not independently establish the
algebraic payload values or replay-graph correctness. Native readers also
check invalid UTF-8, truncated syntax, stale contexts, malformed coefficients,
trailing zeros and byte/depth/digit policies. Field arithmetic correspondence
and exact mathematical conformance remain supplied by the existing tower
proofs and algebraic oracles.

### Full root packets and fresh catalogs

`context.readRootText` and `readRootSetText` check the exact predecessor binding
before reconstructing their typed results. `Catalog.restoreRootText` and
`restoreRootSetText` first reconstruct that predecessor through its validated
base catalog, then replay each selected descriptor. Their byte counterparts
use the same shared UTF-8/JSON parser. Successful `restoreRoot_signature` and
`restoreRootSet_signature` laws retain the requested predecessor for arbitrary
input, and `readRoot_frame` proves exact re-encoding of every accepted selected
frame. `PackedRoot` and `PackedRootSet` retain the
returned predecessor explicitly. Old contexts and their objects remain valid.

Single roots use point/selected tags 0/1; root sets use universal/finite tags
2/3. Typed readers reject the other packet kind, including an algebraic zero
point and the universal set. Finite entries use a width-safe array loop.

Finite packets preserve the literal input order. The format reader does not
assert that an arbitrary list is a complete, sorted result for a polynomial;
use `Context.roots` and its correspondence laws for that mathematical contract.
The reader rejects unknown kinds, malformed points, nonpositive multiplicities,
nonempty universal payloads, stale predecessors, unknown validated providers,
changed descriptor fields or replay graphs, and invalid or oversized text.
The kernel roundtrip laws use a base-only catalog with actual origin-base
availability and lexical policy acceptance, with no assumed successful descriptor or byte parse.

Run the compiled full-root examples and the independent exact oracle:

```sh
lake exe hexrealclosure_root_format_conformance
python3 scripts/oracle/real_closure_root_format.py \
  conformance-fixtures/HexRealClosure/root-format.jsonl
```

Six fixtures include the zero and constant producers, literal point order,
a selected root of a reducible polynomial, a freshly reconstructed algebraic
predecessor with a nested selected root and a split inverse, and a complete
repeated-root result. The native executable checks byte/text reconstruction,
root kinds, selected values and cached owners. It also checks a 100,000-entry
finite packet under the default byte policy. The FLINT oracle independently
selects roots by their exact defining heads, intervals and Thom signs, evaluates
stored algebraic coefficients, and checks prescribed values, entry order and
multiplicities and each prescribed point/selected kind. Replay-graph acceptance remains the native checker's responsibility.
The fixture includes actual rejection messages; coupled mutation tests alter
both original and reconstructed packets to ensure agreement alone cannot hide
a changed embedding, kind or multiplicity. An extra unreachable replay entry
passes descriptor replay but is rejected as a noncanonical root frame; the
fixture checks that exact path. Outer-packet and descriptor predecessor
mismatches have distinct errors.

## Introductory paper examples

`hexrealclosure_basic_conformance` executes the introductory operations from
section 4 of [de Moura–Passmore, CADE 2013](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf).
The complete native producer returns both square roots of two in increasing
order with multiplicity one. The positive root owns the original inverse,
square and cube-plus-one calculations. Its actual checked enlargement retains
that selected root while adding a positive infinitesimal `ε`.
The next complete producer selects the unique real root `β` of `X³-ε` and
checks `ε<β<1`, `β³=ε`, and `1/ε>10^27` through native arithmetic.

```sh
lake exe hexrealclosure_basic_conformance
python3 scripts/oracle/real_closure_basic.py \
  conformance-fixtures/HexRealClosure/basic.jsonl
```

The independent pinned Z3 4.15.4 RCF oracle selects every retained root from
its original polynomial and retained interval (these examples have empty
Thom words), interprets all nine stored values and checks the four original
values after enlargement, including polynomial and endpoint transport.
Native execution replays the three producer-returned descriptors; checked
enlargement validates the rebuilt predecessor. These are compiled correctness
fixtures; ordinary-real realization and scientific timing remain separate
requirements. [Input provenance and coverage](../reports/hex-real-closure/basic-examples.md)
identify the transcribed paper operations. The two examples involving `π`
remain explicitly unsupported without a caller-validated provider and its
progress laws; no other constant is used in their place.
