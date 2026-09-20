# hex-coverings

Quantifier-free satisfiability over `ℝ` by model-constructing search and
cylindrical cell explanations. Refute the negation of a universal goal, or
certify an algebraic model of an existential formula. Search is untrusted;
the kernel checks literal algebraic evidence and a propositional refutation
or a covering tree. Quantifier elimination with alternations belongs to
[CAD](../future-work.md#cylindrical-algebraic-decomposition).

Status: **planned**. This document also specifies `hex-coverings-mathlib`.
Neither library becomes active until the delineability theorem is proved in
Tau Ceti and its actual statement is reconciled with this interface. The
[request #10300](https://github.com/kim-em/hex-dev/issues/10300) remains open
for that reconciliation. These are new interfaces, not existing declarations;
this SPEC adds no implementation, Lake target, or phase registration.

## Placement and dependencies

`HexCoverings`, namespace `Hex.Coverings`, is Mathlib-free. It owns search,
export, literal certificates, and total budgeted checkers. It consumes
[hex-real-formula](hex-real-formula.md), `HexMvPoly`, `HexMvGcd`,
`HexMvFactor`, `HexResultant`, `HexRealRoots`, `HexRealAlgebraic`,
`HexNumberField`, and the planned [HexSturm](hex-sturm.md) coefficient
interface for sample replay (optionally `HexNumberFieldTower` for search
storage).
Projection uses `toUnivariate` and subresultants over multivariate
coefficients; lifting can use `RealAlgebraicPoly.roots`. Factorization and
canonical algebraic arithmetic run in the producer, not during replay.
The propositional adapter uses a kernel-reducible LRAT checker and a proved
formula/atom interpretation. Lean's `bv_decide` tactic uses native proof
discharge and is not the replay route. Its LRAT string parser is also not
kernel-reducible. Parse solver output in the untrusted producer and quote
literal actions and CNF. Reuse `Std.Tactic.BVDecide.LRAT.check` and
`check_sound` only after a `decide +kernel` reduction probe succeeds on the
pinned toolchain, including the array/map operations it uses. If that
fails, `HexCoverings` owns a list-form LRAT checker with its own soundness
theorem. The covering-tree alternative remains available.

`HexCoveringsMathlib` depends on `HexCoverings`, `HexRealFormulaMathlib`,
the polynomial, resultant, real-root and algebraic-number
correspondence libraries, `HexReflectMathlib`, Mathlib, and Tau Ceti. It owns
real cell semantics, projection correspondence, connectedness, checker soundness,
export correspondence, and tactic proof construction. The orchestration
adapter may depend on `HexVirtualSubstMathlib` and `HexRCF`; neither shared
formula library depends on coverings. Existing arithmetic correspondence
and univariate root theorems are reused. **Delineability is the only new
imported deep fact** for multivariate cell correctness: no imported CAD
completeness, single-cell soundness, or solver-correctness theorem replaces
the Hex proofs below. No new axiom, `native_decide`, or trusted extern is
permitted; follow [SPEC](../SPEC.md). Audit the emitted model, cell and
refutation theorems with `#print axioms`: only `propext`, `Classical.choice`
and `Quot.sound` are allowed. Reject `Lean.ofReduceBool`, generated
`*.native_decide.ax_*` declarations and `sorryAx`, including through the
imported delineability proof. Every acceptance equation is checked by the
kernel; a compiled Boolean result is not evidence.

## Formula language and tactic routing

Use `Hex.RealFormula.QF n`, its six comparisons of integer polynomials
with zero, Boolean connectives, fixed monomial order, and list kernel form.
Do not introduce a second source-language AST. The shared reifier from
[#10302](https://github.com/kim-em/hex-dev/issues/10302) proves equivalence
to the Lean proposition, including positive rational-denominator clearing,
binder scope, coordinate permutations, and explicitly selected hypotheses.
Nonpolynomial opaque expressions and symbolic divisors decline as specified
there. Internal root and cell predicates are certificate atoms, not an
extension of the user's polynomial language.

`solve : QF n → Budget → Outcome n` returns `sat ModelCert`,
`unsat RefutationCert`, or `unknown Reason`. Here all `n` coordinates are
existentially sought; the semantics is `∃ ρ : Fin n → ℝ, φ.toProp ρ`.
Refuting `¬G` proves `∀ρ, G ρ`; a model of `G` proves `∃ρ, G ρ`.
Free locals are universally closed only through an explicit proved frontend
conversion, with selected assumptions as antecedents. No existential witness
is generalized over symbolic parameters, and no alternation is silently
flattened. A model of `¬G` is a checked counterexample, not a proof of `G`.

The planned `real_arith` orchestration tries exact closed evaluation, the
existing RCF adapter for a univariate residue without symbolic parameters,
then budgeted [virtual substitution](hex-virtual-subst.md) when an eligible
degree-at-most-two elimination exists, then coverings on a supported
existential residue. Each successful preprocessing step retains its
equivalence. In particular, virtual substitution is tried before coverings
on `∀ x y : ℝ, x²+y² ≥ 2*x*y`. Explicit backend selection is available for
conformance and comparison. Before the covering companion is available,
fallback reports `backendUnavailable` and leaves the goal open.

## Fixed projection theorem

The candidate is in `TauCetiRoadmap.RealAlgebraicGeometry` in
[PR 420's Suggested.lean at 8ebbc3ef](https://github.com/TauCetiProject/TauCetiRoadmap/blob/8ebbc3efb0cc8bab6ee97314eb7fb875ce8f9d9e/TauCetiRoadmap/RealAlgebraicGeometry/Suggested.lean).
It is a target with an unfinished proof, not an available theorem:

```lean
theorem delineability (F : Finset (FamilyPoly n)) (S : Set (Base n))
    (hS : IsConnected S)
    (hproj : ∀ q ∈ projection F,
      SignInvariant (fun x => MvPolynomial.eval x q) S) :
    Nonempty (Delineation F S)
```

`Base n = Fin n → ℝ`, `FamilyPoly n = Polynomial (MvPolynomial (Fin n) ℝ)`.
`Delineation` provides a finite common stack of strictly ordered continuous
roots, constant degrees and multiplicities, `zero_or_ne`, `roots_iff`,
`rootMultiplicity_eq`, `used`, and sign invariance on every section and
sector. Nullified polynomials have no finite root list; their sign is zero
throughout the cylinder. `used` rules out extraneous stack roots.

Fix **exactly** that file's `projection`, also over integer coefficients:

- `reductum p k` retains powers strictly below `k`; `reducta p` contains
  all truncations for `k ∈ range (p.natDegree + 2)`, including zero and `p`.
- Set `T = ⋃ p ∈ F, reducta p`. Include every coefficient of every
  `r ∈ T` through `r.natDegree`, inclusive.
- For each `r ∈ T`, include `psc r r.derivative m d j` for
  `m=r.natDegree`, `d=r.derivative.natDegree`, `0 ≤ j ≤ min m d`.
- For **all ordered pairs** `r,s ∈ T`, including equal pairs and reducta
  of the same original polynomial, include `psc r s m d j` for their
  syntactic degrees and `0 ≤ j ≤ min m d`.

Retain zero and constant entries semantically; deduplication is set equality.
`psc` is the determinant of the specified principal Sylvester minor, with
`q`-columns first and `p`-columns second, including the empty determinant
convention. It is not `signedPsc`. Degree bounds are fixed before evaluation
at a sample; specialization must not replace them with specialized degrees.
McCallum and Brown projection, equational-constraint reductions, and Lazard
projection/lifting are outside version 1. Search may choose a conflicting
subfamily, but the checker requires the full operator for that subfamily.

For integer input use the candidate `integer_delineability`: its family is
`integerFamily P`, and its `hproj` quantifies over `integerProjection P`
with integer-to-real evaluation. Hex proves correspondence of its literal
projection with this set. Tau Ceti's `finSuccEquiv`/`Fin.cons` distinguish
coordinate **zero**; the shared formula language appends a coordinate at
the end. A proved permutation connects these at each level and is included
in input normalization. A positional convention alone is not a proof.

When PR 420 merges, a follow-up records the as-merged declaration, module,
revision, and any changed hypotheses before activation. Import the proved
Tau Ceti theorem, never the roadmap's `sorry` target. If the statement
changes, revise the checker contract rather than treating the candidate as
a permanent upstream API.

## Literal samples and checked export

Search may store canonical `RealAlgebraicNumber` coordinates, lazy roots, a
shared number field, or a tower. The serialized certificate contains only
integers, naturals, dyadics, tags, lists, and bounded references to such data.
In particular it has **no canonical `AlgebraicNumber` field**, real-valued
field, opaque executable closure, or unchecked semantic proof parameter.

The baseline replay represents a sample tuple by a nonzero squarefree
`m : ℤ[t]`, a dyadic open interval `(l,u)` with exactly one root `θ` of `m`,
and coordinates `aᵢ(θ)/dᵢ`, where `aᵢ : ℤ[t]` and `dᵢ` is a positive
integer. Rational tuples use a degree-one parameter. Neither irreducibility
nor a minimal polynomial is required. A literal Sturm certificate proves
the root count and nonroot endpoints, hence existence and uniqueness.
Store signs and substitution identities once per explanation and reference
them across obligations. Repeated parameterizations may share data through
an acyclic, bounds-checked table; sharing is optional, semantics is unchanged.

`checkSample` checks arities, positive denominators, isolation, every claimed
coordinate defining equation, and its selected real embedding. Cleared
substitution identities have the form `D*f(a₁/d₁,…,aₖ/dₖ) = m*q + r`
in `ℤ[t]`, with explicit positive clearing factor `D`. The checker replays
the polynomial identity and determines the sign of `r(θ)`; a zero
remainder proves zero, while other zeros need an exact common-root test.
Signs of denominators may never be guessed. Coordinate isolations and root
indices, checked under these substitutions, distinguish conjugates.
Independent annihilating polynomials without this embedding evidence do
not certify a tuple or its relation to a search sample.

The producer's `export : SearchSample n → Budget → ExportOutcome n`
supplies this data plus the identities and root-selection evidence.
`export_sound` states that accepted export denotes the search tuple when
that tuple's representation invariant holds. The final model/refutation
theorems do not assume this producer invariant: they check literal data
independently. A different exported tuple is useful only if all its own
cell and formula obligations pass.

Exporter termination and growth are separate implementation deliverables,
unmeasured by the spike. The budgeted algorithm must terminate by explicit
fuel/size descent, returning `unknown` if exactification, primitive-element
search, isolation refinement, or coefficient growth exhausts a limit.
Report input extension degrees, coefficient bit lengths and tower depth;
output parameter degree, numerator/denominator heights, eliminant heights,
isolation endpoint bits, witness bytes, and peak intermediate sizes. For
extensions of degrees `eᵢ`, the field degree is at most `∏ eᵢ`; this does
not bound the size of an unreduced generated eliminant. Before claiming a
complete unbudgeted exporter, prove its root-selection/primitive-element
search terminates and give explicit degree and coefficient-height bounds
for the actual elimination algorithm, including denominator clearing.
Finite corpus timings or the existence of a primitive element are not those
proofs. Budget checks apply before large allocations as well as after them.

## One cell explanation

`CellCert` is one theory explanation, not one learned resolvent and not one
sign query. Its literal payload carries:

1. The input/formula identity, arity and variable permutation; references to
   the signed literals being explained and the resulting clause. Literals
   may be input polynomial atoms or certificate root/cell atoms, including
   atoms introduced by earlier explanations. No fixed width is imposed.
2. An exported sample prefix and its isolation/substitution certificates.
3. Level families `P₁,…,Pₖ` of integer polynomials, projection witnesses,
   and a cell path. Each step is a section (equality to a root) or an open
   sector (between adjacent roots, allowing either infinity).
4. Each finite boundary as `(polynomial ID, zero-based distinct-real-root index)` of
   that level's family, its position in the merged stack, and root isolation,
   equality/order, multiplicity and complete root-count evidence at the
   sample prefix. Lower-level families include the projection polynomials
   required above them. Each input atom's polynomial belongs to the family
   at its highest variable level (constants are checked directly). Each
   root atom's defining polynomial belongs to the family at its comparison
   level, with its specified distinguished variable. Expanding a cell atom
   recursively includes the support of all its root predicates. Every
   lower family supplies the projection obligations of the family above.
5. Sign evidence for the relevant family at the sample, shared across all
   literal obligations, plus references to any child covering explanations.

Projection witnesses replay multiplication-only subresultant recurrences
over list-form integer multivariate polynomials. Check initialization,
pseudo-division identities, exact quotient identities, nonzero divisors,
normalization signs/scales, degree descent, terminal zero and defective
degree gaps. Hex's public Brown chain omits gap zeros and auxiliary scalars;
it cannot by itself enumerate the candidate's complete PSC set. The
correspondence layer must account for all requested PSCs and their
determinant normalization, including zero/constant/derivative-zero cases.
A stored representative `q'` may replace an exact PSC `q` only with a checked
identity `c*q = q'` for a nonzero integer `c`, including its sign, so sign
invariance of `q'` entails that of the original `q`. Zero PSCs need a checked
zero identity. This permits differing minor-order conventions without
changing the projection set in `hproj`. Determinant replay can handle
exceptional cases. A recurrence with an unchecked zero
scaling factor proves nothing and is rejected.

Every member of `projection Pᵢ` must have a lower-level sign-invariance
derivation. Checking that the supplied list is merely a subset is unsound.
Factoring or removing content is allowed as arithmetic storage only when
checked product identities and signs derive the sign of every original
projection member; it does not replace the theorem's operator with a
projection of a reduced basis. Constants and zero have trivial sign proofs.

Root isolation of a specialized polynomial over the sample field requires
more than isolating a rational eliminant. The baseline checker replays
Sturm sequences over that ordered algebraic sample: coefficient operations
are literal rational expressions in `θ`; integer-cleared identities and
univariate sign certificates check their values and nonzero divisors.
Check specialized degree, squarefree part and gcd/multiplicity witnesses,
root counts between dyadic endpoints and at infinity, and equality/order
when intervals overlap. Their union supplies every distinct root of every
nonzero family member, with no duplicates or extras in the merged stack.
All finite roots have dyadic isolating intervals; a sector sample can be
rational after refinement.

Implement this as a selected-root coefficient instance of the planned
`CoeffOps` interface described in [hex-sturm](hex-sturm.md#coefficients-and-evidence),
whose record is owned by `HexPoly` and whose shared recurrence/replay is
owned by `HexRealRoots`. HexCoverings owns the literal parameter-context
adapter and its evidence callbacks; its companion proves their interpretation
in `ℚ(θ)`. Since `m` need not be irreducible, do not assume that `ℚ[t]/(m)`
is a field. Use raw rational expressions with checked denominators at the
selected root. Coefficient evidence is bound to the exact context and
operands, is finite and acyclic, and reduces to univariate literal checks;
it cannot recursively justify its own sign. No second Sturm recurrence is
introduced. This adapter and its correspondence are new implementation
obligations, not an already available Hex API.

The baseline uses derivative Sturm root counts interpreted in `ℝ`, proved
from the existing real Sturm theory and coefficient correspondence. Reusing
the computational interface does not import the pending generic
Sturm–Tarski/Cauchy-index foundation of `HexSturmMathlib`. That companion
and general Tarski queries are optional later adapters; they must preserve
the baseline's stated theorem dependencies. No second unproved Tau Ceti
target becomes an assumption of `refute_sound` through sample replay.

The planned `HexSignDet` root descriptors and `HexRealClosure` sample
interface may supply alternative producers/evidence through explicit
adapters, with those libraries becoming dependencies of the adapters.
They preserve root identity, order and the real sample denotation required
here. Infinitesimal samples require finite-sign realization at an ordinary
real tuple before export. They do not enter this literal certificate as
non-real witnesses.

For sign evaluation, exact univariate replay in `ℚ[t]` is the baseline.
Interval evaluation may certify a separated strict sign only after checked
containment excludes zero; an interval containing zero cannot certify zero.
[Tarski replay](../../HexRealRoots/SPEC/hex-real-roots.md) and the planned
Thom/sign-determination interfaces in
[#10311](https://github.com/kim-em/hex-dev/issues/10311) and
[#10313](https://github.com/kim-em/hex-dev/issues/10313) can replace local
root/sign evidence once their soundness correspondences exist. The current RCF
Sturm checker is derivative-specific, not a general Sturm–Tarski checker.

## Constructing the theorem's hypotheses

The checker derives cell facts by induction on levels, starting with the
singleton `ℝ⁰`. It checks sample membership, so every accepted base is
nonempty. The induction gives `IsConnected S` and sign invariance on `S`
for every polynomial required by the next projection. Apply
`integer_delineability`, then use checked complete root counts and ordering
at the sample to identify the described boundaries with the common stack.
The `used` and `roots_iff` fields make that identification exhaustive;
constant multiplicities preserve the per-polynomial indices over the base.
Numerical root order at one point alone is not this argument.

The companion proves connectedness of each selected section or sector
from continuity and strict ordering: a section is a continuous graph over
`S`; a bounded sector is homeomorphic to `S × (0,1)` by interpolation;
unbounded sectors use positive half-lines, and a root-free stack is
`S × ℝ`. Transport through the coordinate embedding. These elementary
topological proofs belong to Hex; an additional unproved `stack_connected`
assumption is not passed to the soundness theorem. The theorem's section
and sector sign fields then propagate the checked sample signs to the cell.

For a nullified family member, check all specialized coefficients zero and
use their invariant signs (or `zero_or_ne`) to derive vanishing throughout
the base cylinder. It contributes no boundary. Degree drops use the full
reducta projection; do not assume a nonvanishing leading coefficient or
well-orientedness. Version 1 can decline a case it cannot export or replay,
but cannot ignore it or accept an arbitrary finite root list for zero.

## Clauses, coverings, and soundness

A cell predicate denotes the recursively guarded root-index description.
Root comparisons mean comparisons to the indexed distinct real root of
the specialized nonzero polynomial; a missing root makes the positive
predicate false. Boolean negation is its logical complement, including
outside its guard. They are not globally defined continuous root functions.
The atom table assigns these predicates, input atoms, and Tseitin atoms
stable IDs and gives each a real semantic interpretation.

For a cell `C` and signed literals `L₁,…,Lᵣ`, the checked explanation proves
`∀ρ, ρ ∈ C → ¬(L₁ ρ ∧ … ∧ Lᵣ ρ)`, using invariant signs and the Boolean
conflict. The clause is `¬C ∨ ¬L₁ ∨ … ∨ ¬Lᵣ`. Check all polynomial and
literal IDs against that conclusion; a false literal at the sample is
insufficient without its invariance on `C`. Root-literal truth also requires
the checked root-index correspondence and order invariance for its defining
polynomial on that cell; cell-literal truth composes those guarded facts.
A prefix cell may exclude all extensions only with checked child coverage,
not from one failed lift.

For LRAT, emit checked CNF definitions for cell guards and Tseitin nodes.
Cell clauses are axioms **of the propositional refutation only**: each
comes with the theorem above. Coverage clauses such as
`¬B ∨ C₁ ∨ … ∨ Cₛ` also need theory evidence. Verify that the children
cover every fiber above base `B`, including both unbounded ends and every
section endpoint. Local sample order is transported over `B` by a common
Collins delineation; children with different supports require a checked
common refinement and inclusion proofs. For the union family, re-establish
all projection obligations at every lower level of `B`'s cell chain. If
`B` is not invariant for that enlarged projection, subdivide `B` into
certified base cells and prove they cover `B` before combining their
fiber covers. Sign invariance for an earlier, smaller family is insufficient.
These coverage/definition clauses are necessary to relate new cell atoms; LRAT does not discover their real
meaning. Learned resolvents instead cite LRAT derivations. An external
solver verdict, trace, or reduced-projection explanation is not such a proof.

Alternatively `RefutationCert` contains a finite covering tree (or acyclic
DAG). A node covers the next real coordinate by certified sections/sectors
or checked unions of them, with endpoint inclusion recorded explicitly.
Children share the certified base or supply refinement/inclusion evidence.
Overlaps are allowed; gaps, omitted singleton endpoints, cycles, and
unproved base changes are rejected. Leaves prove the input Boolean formula
false from checked signs; if a leaf uses Boolean branch assumptions, the
tree must also exhaust those branches. Induction proves every extension
of the root `ℝ⁰` fails the formula. It substitutes for LRAT, not for the
cell checker. Larger excluded intervals can be unions of verified cells;
they do not acquire sign invariance merely by merging.

Required companion theorem shapes, in design notation, are:

```text
cell_sound : checkCell atoms c = true → ∀ρ, clauseSem atoms c.clause ρ
refute_sound : checkRefutation φ cert = true → ¬ ∃ρ, φ.toProp ρ
model_sound : checkModel φ cert = true → ∃ρ, φ.toProp ρ
```

The top-level checkers include decoding, input correspondence, all projection
and sample checks, cell/coverage clauses, CNF conversion, and LRAT or tree
replay. Their only hypothesis is acceptance on the supplied formula and
certificate, not user-supplied connectedness, sign invariance, completeness,
well-formedness, or correctness of search. `refute_sound` maps any supposed
real model to a Boolean valuation satisfying the input CNF and every
checked theory clause, contradicting accepted LRAT; the tree case uses
the exhaustion induction. The tactic composes this with the reifier's
equivalence for the negated goal. `checkModel` establishes a nonempty
literal sample and evaluates **every** atom needed for the original formula
and its Boolean structure; it needs no delineability or projection proof.
Witness extraction chooses the uniquely isolated parameter root and its
checked rational-polynomial coordinates.

## Search, termination, and fall-through

Compiled search assigns coordinates, selects conflicts, constructs cells,
backtracks and learns clauses; it may use single-cell, levelwise, or
covering construction. These choices do not change accepted semantics.
A heuristic run is a bounded proof/model attempt. Search budgets include
visited cells, explanations, degrees, coefficient bits, isolation refinement,
export size, propositional proof size and replay work. Exhaustion returns
`unknown`, never `unsat`. Invalid certificates report the failing obligation.

A complete decision-procedure claim requires a separately proved fair
fallback: finite full-Collins projection closure, exhaustive stacks at each
level, terminating algebraic sample production/export, and progress through
a finite set of cells. The same cell and covering checker can certify that
fallback without changing its trusted statement. NLSAT conflict learning
alone does not supply a termination proof. Until those obligations are met,
only acceptance soundness and bounded termination are claimed. Arbitrary
alternations, non-real carriers, unsupported root evidence, general
algebraic lifts beyond implemented depth, and missing external proof output
decline with precise reasons. Models remain exact, even when search used
floating-point approximations.

## Corpus sanity checks

The [spike report](../../reports/cad-sample-costs.md) from
[PR #10310](https://github.com/kim-em/hex-dev/pull/10310) supplies the
following witness shapes. These check that the format can express the
samples; they are not completed cell certificates or full projection runs.
Changes to the report require rechecking the representation and cost claims.

| Case | Literal sample and sign obligation | Additional cell obligation |
| --- | --- | --- |
| NLSAT paper | `16α³−8α²+α+16=0`, `−1<α<0`; `β<0`, `β²=1−α²`; reduce `α³+2α²+3β²−5` to `α³−α²−2<0` | A full tuple can use `t=α`, `β=−1−t/8+t²/2`, with the circle identity and negative-root selection checked; this boundary sample is not a model of Example 5's strict conjunction. |
| Circle/parabola | `α⁴+α²−1=0`, `α>0`, `β=α²`; check `β−α<0` and `β²+β−1=0` | Shared root equality and the zero sign are exact; retain the section when refuting `y≥x`. |
| Two circles | `α=1/2`, `4β²−3=0`, `β>0`; check `β−α>0` | Subtraction and root selection link both circles to the same sample; both signs of the intersection belong in exhaustion. |
| Kahan specialization | `t²=2`, `1<t<2`; `α=(1+t)/4`, `β=t/8`; circle residue `(5t²+8t−60)/64<0` | Check ellipse substitution and denominator signs; this fixed ellipse is not the four-parameter Kahan problem. |
| Sphere section | `t⁴−10t²+1=0`, `3<t<4`; `α=(t³−9t)/4`, `β=(11t−t³)/6`; `2α²=1`, `3β²=1`, both positive | The two coordinates generate different quadratic fields; level 3 can use `γ=(t²−5)/12`, checking `γ>0` and `6γ²=1`; these additional checks were not timed by the level-2 sign replay. |
| Tower 4 | `t⁴=2`, `t>1`, `β=t`, `α=t²`; `β−α<0` | Check the positive roots and all excluded sectors for `y≥x`. |
| Tower 8 | `t⁸=2`, `t>1`, `β=t`, `α=t²`; `β−α<0` | Same checks at degree 8; canonical output degree is not a cost prediction. |

For `(x−y)²<0`, a forced covering run must use the **full** projection,
including coefficients `1,−2y,y²` and the PSCs of all reducta. The base
splits at `y=0`; above each base cell the repeated section `x=y` has sign
zero and the two sectors have positive sign. Choose rational samples on
each base cell and prove the stack covers every `x`. Their conflicts and
coverage refute the negation of the inequality. Virtual substitution is
the default first multivariate attempt and avoids this covering proof.

## Complexity and Phase-4 evidence

Track visited search cells `V`, exported theory explanations `E`, learned
resolvents `R`, clause widths, distinct stored polynomials/isolations, and
expanded references separately. Projection support is not clause width.
Replay is output-sensitive: report decoding/CNF work, shared projection
and isolation work, per-explanation sign/coverage work, and LRAT literal
and hint visits (or covering-tree edges). A useful accounting contract is
`Tcheck = Tdecode + Tshared + Σᵢ Tlocal(i) + Tprop`; it is not a unit-cost
bound in `E`. Give arithmetic operation counts together with intermediate
degree/bit-size bounds for each checker. No polynomial bound in input size
or fixed per-clause latency is claimed; full-CAD fallback has the familiar
doubly exponential variable-count obstruction.

The spike's canonical level-2 lifts range from about 3.4 ms to 5.54 s;
degree-3 NLSAT is slower than degree-8 Tower 8. Focused kernel checking of
one supplied sign certificate has medians 81.3–1335 ms, excluding export,
projection, root-stack completeness, transport, soundness application and
LRAT. Whole fresh-module paired differences are a different measurement,
with some ranges crossing zero. Budget a cell explanation from **all** its
obligations, with measured sharing, not by assigning it one sign's cost.
The seven Z3 runs produced 0–10 explanations, 0–7 learned clauses and 0–5
primitive projected factors per explanation, excluding input support.
Those traces use Z3's projection rules; their factor counts do not predict
the full Collins payload. Repeated support motivates sharing, without
establishing its benefit or a maximum clause width.

Phase 4 separately measures search, canonical/lazy lifting, checked export,
projection witness production, certificate bytes, and kernel replay. Use
independent ladders for variables, atom count, main/total degree and integer
coefficient bit length; include sparse/dense inputs, Boolean branching,
repeated projection support, rational and disjoint-field samples, tower
depth, repeated roots, degree drops/nullification, and variable-order
permutations. Include higher-parameter ellipse and genuine algebraic
third-level lifts as additional families, not extrapolations from the spike.
Measure per-explanation cost against its sign count and shared-data size;
contrast interval strict-sign proofs with exact zeros and Thom/Tarski replay
across degree/height regimes once available. Z3/cvc5 timings are
informational comparisons of different solvers/proof obligations; no claim
of parity with an uncertified verdict is an acceptance criterion.

Follow [benchmarking](../benchmarking.md) and [Phase 4](../../PLAN/Phase4.md):
compiled benches remain Mathlib-free, proof probes use fresh `lake build`
modules with matched imports, and record both kernel work and wall time.
Include LRAT kernel reduction, literal action/CNF construction, rejected
proofs, and the emitted theorems' axiom audit in these probes. Report LRAT
replay independently of algebraic cell checking.
Use the shared host, one automatically selected CPU where supported, fixed
trial-major schedules, adjacent alternating AB/BA arms, and retain every
completed sample. At most one unchanged rerun follows an inconclusive
result. Export has its own termination/growth report, including failures;
the handwritten spike substitutions are not an exporter benchmark.

## Conformance and manual

Version fixtures with normalized formula, variable order, exact literal
certificate, expected verdict/signs, tool versions and seeds. Compare
quantifier-free verdicts with pinned Z3 `nlsat` or cvc5; `unknown` is not a
disagreement or evidence of unsatisfiability. Use python-flint for rational
univariate residues, gcds, root counts and signs, and existing canonical
Hex arithmetic as an additional sample cross-check. External solvers are
oracles or untrusted producers only. A solver lacking suitable evidence
cannot bypass replay. Z3 and cvc5 are `if_available` in `ci`; at least one
pinned solver is `required` in the `local` acceptance campaign, with the
chosen solver recorded. Record unavailable optional oracles as skips.
The `core` profile uses no external oracle. Extend
`scripts/ci/run_oracles.sh` and the existing install step when implementing
these tests, following [CI](../CI.md); do not add jobs or a matrix per
oracle. python-flint uses the existing oracle dependency.

Follow [testing](../testing.md) with typical, edge and adversarial cases per
operation. Include the corpus above and negative mutations: omitted PSC,
wrong normalization sign, zero recurrence divisor, omitted reductum,
specialized degree substituted for a fixed bound, wrong conjugate, missing
root, wrong multiplicity, zero polynomial with a finite root index, stale
atom ID, sign-zero claimed from an overlapping enclosure, missing endpoint
in a cover, a base change without inclusion evidence, malformed/cyclic
sharing, and an LRAT axiom that lacks a checked theory derivation. Every
mutation must reject or still prove its actual independently checked claim.

The manual explains a universal inequality and an existential algebraic
model using the shared formula syntax. Show backend choice, the cell path,
one theory explanation versus its learned resolvents, exported literals,
and why coverage certifies nonexistence. Include a budget exhaustion example
that leaves the goal open. Do not present canonical search values as kernel
evidence or claim a full CAD has been built by a local explanation.

## Reference designs and deferred choices

[Jovanović–de Moura, IJCAR 2012](https://dddejan.github.io/papers/jovanovic-ijcar2012.pdf)
motivates model-constructing conflict search;
[Brown–Košta, JSC 2015](https://doi.org/10.1016/j.jsc.2014.09.024)
motivates single-cell construction;
[Nalbach et al., JSC 2024](https://arxiv.org/abs/2212.09309)
provides the levelwise proof-rule design;
[Ábrahám et al., JLAMP 2021](https://arxiv.org/abs/2003.05633)
provides cylindrical coverings. Their reduced projection rules are not
automatically justified by this SPEC's Collins theorem. See also the
[alignment analysis](../../reports/decision-procedures-alignment.md#nlsat-mcsat-and-cylindrical-algebraic-coverings).

Search storage and exactification policy, single-cell versus levelwise
versus covering search, in-Lean CDCL versus external LRAT production,
cross-explanation storage sharing, interval versus Thom/Tarski evidence,
and efficient handling of nullification, deep algebraic lifts, many
parameters and variable ordering remain behind the checked interface.
Their optimizations require evidence; none weakens projection completeness,
root identity, sample signs or coverage.
