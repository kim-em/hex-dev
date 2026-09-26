# hex-kronecker-mathlib

The soundness and tactic companion of
[hex-kronecker](../../HexKronecker/SPEC/hex-kronecker.md).  It proves that the deterministic packed
integer checks establish polynomial identities and exposes the `kronecker`
tactic for every commutative ring.  It is unpublished because
the frontend depends on `HexReflect` and `HexReflectMathlib`.

Dependencies are `HexKronecker`, `HexMvPolyMathlib`, `HexReflect`,
`HexReflectMathlib`, and `HexMatrixMathlib`, plus Mathlib.  The library is not
`correspondence_only`: it owns a tactic and fresh-module proof probes.  The
tactic and its soundness theorem live together here, as required by
[matrix-tactics §Placement](../../SPEC/matrix-tactics.md#placement).

## Denotation and polynomial model

For a commutative ring `R`, `Expr.denote (v : Nat → R)` is total and defined
by structural recursion, interpreting integer constants by `Int.cast`, atoms
by `v`, and the remaining constructors by the corresponding ring operations.
For `v : Fin k → R`, `Expr.denoteFin h v` uses a proof
`h : e.WellFormed k` to interpret each occurring atom.  No definition maps a
malformed index modulo `k` or supplies an arbitrary value for it.

`Expr.toMvPolynomial` denotes the same tree in
`MvPolynomial (Fin k) Int`.  It is a semantic model used in proofs only; the
kernel checker never constructs or reduces it.  The main factorization
theorems are:

```lean
theorem denote_eq_eval₂ (h : e.WellFormed k) :
    e.denoteFin h v =
      MvPolynomial.eval₂Hom (Int.castRingHom R) v e.toMvPolynomial

theorem evalKron_eq_eval₂ (h : e.WellFormed k) :
    evalKron plan e =
      MvPolynomial.eval₂Hom (RingHom.id Int)
        (fun i => (plan.base : Int) ^ plan.stride i) e.toMvPolynomial
```

`denoteTerms v P` is the evaluation of `Hex.MvPoly.Kernel.denote P`, transported
by `HexMvPolyMathlib.equiv` and `MvPolynomial.eval₂Hom`.  The analogous
`packTerms_eq_eval₂` theorem passes through that definition; it does not
define a second conversion between `MvPoly` and `MvPolynomial`.

The mixed-radix lemma proves that exponent vectors in the common degree box
have distinct codes.  The balanced-digit lemma then generalizes
`Hex.Internal.packDigits_inj`: if every exponent is in that box, the
coefficient ℓ¹ bound is at most `H`, and `2 H < B`, equality after evaluation
at `xᵢ = B^sᵢ` implies equality in `MvPolynomial (Fin k) Int`.  Its proof
flattens the dense box in mixed-radix order and invokes the existing
one-variable injectivity result.  It reuses rather than restates that result.

Consequently the public soundness statements have the following direction:

```lean
theorem checkExprEq_sound (h : checkExprEq budget k lhs rhs = true) :
    ∀ {R} [CommRing R] (v : Nat → R), lhs.denote v = rhs.denote v

theorem checkTermsEq_sound (h : checkTermsEq budget k lhs rhs = true) :
    denoteTerms R v lhs = denoteTerms R v rhs

theorem checkMulTerms_sound
    (h : checkMulTerms budget mode k n r m M A C = true) :
    denoteMatrix n r R v M * denoteMatrix r m R v A =
      denoteMatrix n m R v C
```

Here `denoteMatrix n m` is the total `Matrix (Fin n) (Fin m) R` obtained from
row lists with `getD`; the theorem derives the exact row counts and lengths
from the check's successful shape validation, so padding is never observed in
the conclusion.  The checker also implies both expression trees are well
formed, which is why the first public theorem needs no separate hypothesis.

The target ring needs no injectivity hypothesis: injectivity is used once in
the integer polynomial model, after which polynomial equality is mapped to
any commutative ring.  Matrix soundness is proved entrywise.  The plain mode
uses `Hex.Matrix.Packed.dotInt`; the signed-packed mode is first identified
with that ordinary integer dot product by `HexMatrixMathlib.dotIntPacked_eq`.
The proof then applies scalar Kronecker injectivity.  Neither
`Matrix.mul_apply` nor finite indexing is reduced by the Boolean checker.

The mixed list/tree product checker and its kernel form have the analogous
matrix soundness statement, with the right matrix denoted from expression
trees. Prove it using `packTerms_eq_eval₂` on the list operands and
`evalKron_eq_eval₂` on the tree operands, followed by the same bounded-box
injectivity argument as `checkMulTerms_sound`. Structural tree degrees and
ℓ¹ bounds supply the right operand's bounds. Mixed tree/list value equality
uses the same argument. Neither proof normalizes the input trees to term
lists. The modular variants first recover the integer polynomial identity
with the checked quotient and then transport it to characteristic `p`.
`Kernel.mulTerms_sound` has the same universal matrix conclusion as
`checkMulTerms_sound`, with a `Kernel.mulTerms` hypothesis instead of the
budgeted check. `Kernel.mulTermsMod_sound` likewise retains the modular
matrix conclusion. The corresponding mixed and tree/list equality theorems
also remove only the resource-policy premises, retaining all shape, atom,
residue-leaf, quotient and mathematical-bound checks.

## Characteristic `p`

For `0 < p`, a passing quotient-witness check gives

```text
L̃ - R̃ = p Q
```

in `MvPolynomial (Fin k) Int` by the same bounded-box injectivity theorem.
Mapping this equality to any `[CommRing R] [CharP R p]` kills the right-hand
side and proves equality of the two denotations.  For residue-provider input,
the bridge uses `HexReflectMathlib.residueHom p R` and its coefficient laws to
identify canonical `ZMod64 p` coefficients with their integer representatives.
No injectivity of `residueHom` is required for soundness.

`checkExprEqMod_sound`, `checkTermsEqMod_sound`, and
`checkMulTermsMod_sound` state these results, the last pointwise over the
quotient-witness matrix.  Completeness of the witness interface says that
equality of the formal residue polynomials yields an integer `Q`; it does not
claim that the checker constructs `Q`.  The producer is compiled code owned
by the consumer.  Consumers without a quotient use the residue term-list
checker specified by
[issue #10257](https://github.com/kim-em/hex-dev/issues/10257).  In particular,
this library never treats base-`p` integer multiplication as polynomial
multiplication.

## Reflection boundary

No addition to hex-reflect is required.  `Hex.Reflect.ReifiedRing.expr`
already retains the unnormalized `Lean.Grind.CommRing.Expr`, and
`Lean.Meta.Sym.Arith.ofRingExpr` already quotes it.  This library adds a
structural, constructor-for-constructor translation into
`Hex.Kronecker.Expr`:

```text
.num/.natCast/.intCast → .int       .var → .atom
.add/.sub/.neg/.mul/.pow → the matching constructor.
```

It also proves that translation preserves denotation under the sealed atom
assignment.  The translation rejects an out-of-range variable instead of
using the normalizer's variable conversion.  It never calls
`Hex.Reflect.normalize`, `Expr.toPoly`, `Expr.toPolyC`,
`convertTerms?`, or `Conversion.terms`.  Those surfaces collect like terms
and would defeat the tree checker's purpose.

## The `kronecker` tactic

The tactic closes goals `a = b` when `a` and `b` have the same carrier `R`,
`[CommRing R]` is available, and both sides reify in the fixed
commutative-ring language.  Examples of the surface are:

```lean
example {R : Type*} [CommRing R] (x y : R) :
    (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  kronecker

example {R : Type*} [CommRing R] (x y : R) :
    (x + y)^2 = x^2 + 2*x*y + y^2 :=
  kronecker% ((x + y)^2 = x^2 + 2*x*y + y^2)
```

`kronecker% (a = b)` is the term form and elaborates to a proof of the
displayed equality.  Both forms share one implementation and configuration;
neither name carries a `hex_` prefix.  The owning library declares
`syntax (name := kroneckerTac) &"kronecker" optConfig : tactic` once; the
term form declares
`syntax (name := kroneckerTerm) "kronecker%" "(" term ")" : term`.
Both elaborators use `@[no_fallback]` and answer `throwUnsupportedSyntax`
outside their fragment.

`HexKroneckerMathlib.Config` embeds `Hex.Kronecker.Budget`, whose defaults are
`maxDenseDigits := 65536` and `maxPackedBits := 16777216`; callers may tighten
either limit. The frontend rejects `maxPackedBits` above its default before
reflection or constructing the saturation cap. Programmatic `Budget` values
remain unrestricted. It is distinct from `HexMatrixMathlib.KernelConfig`, which
configures only the existing `rank` and `det` frontends.

The implementation opens one hex-reflect session and calls
`Hex.Reflect.reifyCommRing` on both sides against its shared growing atom
environment.  That session surface performs carrier classification, caching,
atom allocation and reflection-budget charging and returns
`ReifiedRing.expr`; its `charInst?` records any discovered characteristic.
The tactic seals the environment once, translates the two retained trees,
and runs the bit-length implementation `Preflight.exprEq`, proved equal to
`sizeExprEq` in every report field. It does not request a `Conversion`.  If the report
fits the configuration, it emits the quoted trees and applies
`Kernel.exprEq_sound` to `Eq.refl true`.  The
elaborator performs no `Kernel.whnf` pre-evaluation and does not ask
`Meta.check` to evaluate the proof before the kernel's single synchronous
check. The retained-tree translation and kernel traversals use direct
recursors, with proved `csimp` equations for native elaborator execution.
The accepted theorem's axiom audit permits only `propext`,
`Classical.choice`, and `Quot.sound`.

`checkExprEq_sound` maps an established integer polynomial identity to every
commutative ring, so the tactic requires no characteristic hypothesis and
proves such identities over finite fields as readily as over `ℚ`.  What it
cannot prove in positive characteristic is an identity of formal
polynomials that holds only modulo `p`, such as `(x + 1) ^ p = x ^ p + 1`
over `ZMod p`: that needs the quotient witness, here
`Q = ((x + 1) ^ p - x ^ p - 1) / p` with integer coefficients.  Programmatic
consumers may supply one and apply the `...Mod_sound` theorems, but this
tactic neither searches for that witness nor silently falls back to
normalized residue terms.  An identity of polynomial functions that is not
an identity of formal polynomials, such as `x ^ p = x` over `ZMod p`, has no
quotient witness and is outside every arm: the `Mod` theorems conclude
equality in every commutative ring of characteristic `p`, including
`(ZMod p)[X]`, where `X ^ p ≠ X`.

## Outcomes and diagnostics

The tactic follows [matrix-tactics' outcome protocol](../../SPEC/matrix-tactics.md#outcome-protocol-and-diagnostics):

- A goal other than equality, different carriers, a missing `CommRing`
  instance, an unresolved carrier metavariable, or syntax outside
  the reflected fixed ring fragment is `notApplicable` and delegates with
  `throwUnsupportedSyntax`.
- A recognized polynomial identity whose exact preflight exceeds either
  limit is `declined`.  Its stable diagnostic is
  `kronecker declined: dense box requires <D> digits and <N> packed bits
  (limits <Dmax> digits, <Nmax> bits)`; a saturated value is a certified
  lower bound and is printed as `at least <limit + 1>`.  The diagnostic
  also prints the per-atom degree
  bounds when `D` is the exceeded dimension and `limitingStage` when the bit
  bound comes from an outer matrix packing.
- Unequal packed values are an ordinary false-target failure and report that
  the goal is not a polynomial identity in the sealed atoms.  They are not a
  proof that the equality is false after using hypotheses or relations among
  atoms. Because accepted certificates must not be pre-evaluated, this
  diagnosis follows the kernel rejection; only the rejected case is checked
  again by compiled code to distinguish a false target from a bad certificate.
- An ill-formed quoted tree or a kernel-rejected certificate is `failure`,
  never a decline and never a request for another solver.

Opaque subterms and symbolic powers not recognized as ring operations may be
independent atoms when hex-reflect classifies them that way.  The tactic uses
no local hypotheses or algebraic relations between atoms.  It therefore can
prove identities uniformly in such atoms, but it cannot prove `x = 0` from a
hypothesis `hx : x = 0`.

## Fresh-module comparisons and shipping bar

Proof probes live under `bench/HexKroneckerMathlib/ProofProbe`, declared
exactly in `libraries.yml`.  The runner builds fresh modules with warm imports
and six adjacent candidate/reference pairs, alternating `AB`/`BA`, retaining
every completed sample on the shared host.  Each accepted family has matched
modules for `kronecker`, Mathlib `ring`, and Grind's `grobner` from
`Init/Grind/Tactics.lean`; import-only baselines are subtracted round by round.
The sources use identical propositions and construction modules.

The primary grid uses atom counts `1, 2, 3, 4, 6, 8` and degrees
`2, 4, 8, 16`.  It records preflight declines rather than invoking the tactic
where the dense box is outside budget.  Additional determinant-shaped probes
expand the determinant of an `n × n` matrix whose entries are polynomials in
`k` shared atoms, varying `n`, `k`, and entry degree.  A separate
many-independent-atoms family uses `n²` linear atoms and must decline before
packing once its `2^(n²)` dense box crosses the limit; a slow success is a
failure of dispatch.

The preregistered operational cleanup timeout is 180 seconds.  The absolute
candidate ceiling is 30 seconds for each accepted atom-and-degree case and 60
seconds for each accepted determinant-shaped case.  These values are fixed by
this SPEC before measurements are collected.  The implementation PR records
the exact source hashes, raw samples, paired medians, `.olean` sizes, axiom
audits, and one kernel-only profile for each family.  The Mathlib-free bench
supplies the complexity evidence; these probes measure reification, emitted
literals, kernel checking, and total tactic cost.

The tactic ships under the opt-in exception of
[matrix-tactics §The bar against Mathlib](../../SPEC/matrix-tactics.md#the-bar-against-mathlib),
exactly as that exception is written: the tactic and term form ship
explicitly opt-in once the full family table is recorded and the absolute
ceilings pass, with every losing family in the table.  Being strictly below
both `ring` and `grobner` on a family is not a condition for opt-in
shipping; it is the condition for that family to enter a default chain, and
the chain then dispatches on the winning regime.  The report names the
winning regime from the measurements (the determinant-shaped families and
the larger expansions) and the losing one (small grids, where reflection and kernel traversal
are a substantial fraction of invocation cost), and records the per-family ratios for
both.  Dense boxes outside the accepted budget decline before proof
construction.  A family accepted by either comparator but outside the
Kronecker regime is recorded as scope deliberately delegated, not as a
packed success.  No default chain changes merely because the opt-in bar
passes.

## Placement and consumers

The pair remains unpublished because this companion's reification dependency
would violate the released mirrors' import closure.  It adds no released
manifest entry and `scripts/release/check_released_manifest.py` must remain
clean.  Tactic syntax, implementation, soundness and proof probes all live in
this companion.

Expression and mixed-product soundness are reusable APIs independent of the
symbolic determinant evaluator. That evaluator uses direct algebraic proofs;
it need not retain small closed forms or determinant-specific packed wrappers
as consumers. Polynomial rank certificates may reuse this pair under their own
contract. Each consumer depends downward; the Kronecker libraries do not import
a certificate consumer.
