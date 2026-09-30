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
The companion proofs use the shared theorem
`HexRealRootsMathlib.Tarski.check_rootSum` and only Lean’s standard logical axioms.

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
These cases exercise one bisection node; complete isolation and simultaneous
ordinary-real realization remain separate requirements.

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

The frontier feeds descriptor completion and factor assembly below. The
complete ordered `RootSet` still needs general descriptor comparison laws and
producer totality. Automatic dependency transport, compatible real-closed
union semantics and simultaneous ordinary-real realization remain separate
requirements of the full tower.

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

This intermediate output does not claim globally sorted root values or full
producer success. It is for nonzero squarefree input; the factor assembly below
restores Yun multiplicities and handles the zero-polynomial case.
Unresolved and whole-line enumeration currently prepare the retained domains
again; the requested upstream prepared-root enumeration API remains a subsequent
integration. `cell_enumeration_present` and `Whole.enumeration_present` prove
that these retained valid domains cannot return the absent-domain result. That
branch remains a diagnostic guard, using the internal system error rather than
a descriptor-replay error.

`hexrealclosure_isolation_conformance` emits eighteen actual executions. The pinned
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
The companion proves point comparisons and successful selected-root/point
comparisons in the ambient ordered real closed field, using the upstream
producer-success proof for unconditional mixed comparisons. Equality returned
by any successful comparison is equivalent to equality of the root values.
The sort relies on
completion’s distinctness proof; it does not certify arbitrary input lists
as distinct without the missing general comparison-order laws. General strict order for
descriptor pairs still requires the upstream Thom theorem, so this intermediate
sort does not establish the complete ordered `RootSet` contract. Factor assembly
restores multiplicities separately.
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
semantic zero. Global ordering and producer totality remain separate
obligations before a complete `RootSet`.

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

`HexRealClosureMathlib.BaseTests` also executes all three stages together: a
registered Liouville real constant, a positive infinitesimal, and a selected
root of `Y²−(τ−5/4+ε+2)` in `(1,2)`. It checks the root's equation, interval
signs and inverse in the constructed context.

The semantic sign, inverse and quotient proofs consume the proved shared
Tarski foundation. Their axiom guards contain only the three standard kernel
axioms, and the audited import cones contain no admissions. These interpretations are
conditional on an ambient ordered real closed field, not an existence proof.

The remaining tower work includes context enlargement and transport, complete
general root isolation and multiplicities, rational delegation agreement and
identification of native contexts with the compatible real-closed union.
Construction of a native algebraic context eagerly prepares and retains its
shared selected-root query domain. `Context.buildSigns` reuses it for singleton
and caller-supplied joint queries; `buildSigns_eq` proves exact agreement with
the original producer,
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
General persistent refinement, transport of later descriptors, complete
isolation and identification with the real-closed union remain open.
Reconstructing new validated algebraic levels from serialized frames remains
open. Native frame-format totality is proved independently of graph decoding
and byte-parser completeness.

Run `lake build HexRealClosure.FrameFormatTests` for total construction over a
non-monic reducible rational definition, followed by a definition with
noncanonical predecessor coefficients. The frame-format axiom guards use only
the standard three axioms.

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

Run `lake build HexRealClosure.TowerOrderTests HexRealClosureMathlib.TowerModelTests`.
Executable checks use a nonmonic reducible definition for √2 and a second root
with noncanonical predecessor coefficients. They cover semantically equal
but literally different nonzero expressions, all three comparison results,
canonical zero and embedded comparisons. Kernel examples propagate a rational
model through three arbitrary validated root levels, including the algebraicity
and image-field inclusions. The semantic root results use the proved
`Tarski.check_rootSum` theorem and only the standard three axioms. They are
relative to a supplied real-closed
ambient field and base embedding. Compatibility across native refinements and
identification with the real-closed algebraic union remain open. No tower
performance claim is made.

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

Identifying native towers with the compatible algebraic union, descriptor construction and simultaneous
realization of finite sign conditions at one ordinary real point remain
separate obligations.

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

Presenting every algebraic generator by a native selected-root descriptor and
identifying all compatible native presentations with this semantic union remain
required tower integration work.
