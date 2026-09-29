# Rational selected-root expressions

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
return, `inverse?` cannot fail its candidate check. Total sign-query producer
success remains an upstream requirement.

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
semantics use the proved `Tarski.check_rootSum` theorem.
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
means that the polynomial has no roots. Capped bounded bisection is implemented
below. Complete isolation and automatic dependency transport remain required;
general contexts and explicit recursive transport have separate APIs above.

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
old descriptors or counts. The frontier below recomputes every pending domain
and count after deflation. Complete isolation still needs descriptor construction
and restoration of the original multiplicities.

The generic deflation proofs use zero-reflecting coefficient interpretation
into a field and introduce no admissions. Packed selected-root execution tests
check cancellation of structurally different coefficient values. Thirteen
independent exact fixtures include nonmonic and repeated inputs, nonroot
rejection, inverse infinitesimals and removal at either of two infinitesimal
levels. Their SymPy oracle uses synthetic division in `QQ(epsilon, delta)`.
With SymPy and python-flint installed, run `lake build hexrealclosure_deflation_conformance`, then
`.lake/build/bin/hexrealclosure_deflation_conformance | python3 scripts/oracle/real_closure_deflation.py`.

For existing canonical number-field arithmetic and conversions, see the
[number-field chapter](../HexManual/Chapters/HexNumberField.lean) and
[real-algebraic chapter](../HexManual/Chapters/HexRealAlgebraic.lean).

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
evidence after deflation. Complete BKR fallback, factor merging and the
complete root-set API remain to be assembled and proved.

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

Descriptor construction, BKR completion, multiplicity restoration and
factor-list merging remain required for complete isolation. Automatic dependency
transport, compatible
real-closed union semantics and simultaneous ordinary-real realization remain
separate requirements of the full tower.

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
its stored domain. Absent search domains stay `none`; internal producer
failures remain explicit errors and cannot become empty root sets.

`Completion.coverage` proves that these actual output values are exactly all
roots of the original input. `Completion.nodup` proves each root appears once,
using distinct emitted points, their exclusion from the remaining head,
disjoint retained cells and the shared enumeration's coverage theorem. The
proofs apply to raw coefficients through a zero-reflecting interpretation in
an ordered real closed field, and use only the standard three axioms.

This intermediate output does not claim globally sorted root values or full
producer success. It is for nonzero squarefree input; Yun multiplicities and
the separate all-roots result for the zero polynomial must still be assembled.
Unresolved and whole-line enumeration currently prepare the retained domains
again; the requested upstream prepared-root enumeration API remains a subsequent
integration. `cell_enumeration_present` and `Whole.enumeration_present` prove
that these retained valid domains cannot return the absent-domain result. That
branch remains a diagnostic guard, using the internal system error rather than
a descriptor-replay error.

`hexrealclosure_isolation_conformance` emits ten actual executions. The pinned
Z3 RCF oracle independently checks inputs, finite-bound policy, node caps,
scalar-preserving deflation, cell counts, selected derivative words, literal descriptor contexts, complete
root coverage and absence of duplicates. Cases include nonmonic input,
negative leading scalar with an emitted zero, a nonquadratic generator,
four real roots, a whole-line inverse infinitesimal, close infinitesimal roots
requiring completion after the rational bisection cap, and invalid domains.
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
sort does not establish the complete ordered `RootSet` contract or multiplicities.
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

A zero polynomial returns `(0, 0)`. This transformation does not construct a
root set: a complete roots API must still return `all` for zero and restore
the extracted multiplicity when merging its other roots. The exact deflation
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
negative leading scalar.

The companion's `factorEntries_spec` ties every emitted root and label to the
actual factor input. `factorEntries_multiplicity` and `factorEntries_complete`
transport the actual raw Yun result into a characteristic-zero field and prove
exact labels and coverage. They require coefficient-operation preservation
and zero reflection; the executable coefficient type needs no field instance.
`assemble_spec` composes these results with zero extraction: a successful finite
output represents exactly the original polynomial's roots with their original
positive multiplicities. `assemble_all` proves the separate all-roots result
occurs exactly for semantic zero. Duplicate-free output, global ordering and
producer totality remain separate obligations before a complete `RootSet`.
