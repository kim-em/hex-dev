# hex-mv-factor (multivariate factorization over `Z`, depends on hex-mv-hensel)

Factorization of `MvPoly n Int cmp`: the search that finds a
decomposition, the checker that accepts one, and the separate
certificate that upgrades a checked decomposition to a factorization
into irreducibles. Mathlib-free. The companion `hex-mv-factor-mathlib`
identifies the checked statements with `MvPolynomial (Fin n) ℤ`,
discharges the univariate irreducibility obligations the Mathlib-free
checker leaves open, proves uniqueness against Mathlib's unique
factorization, supplies `Decidable (Irreducible p)`, and extends
`factor_poly` and `irreducibility` to multivariate inputs. The tactic
surface also accepts an open commutative-ring expression, reifies its
polynomial atoms as formal variables, and returns a certified formal
factorization together with its denoted product identity.

This SPEC expands the "Multivariate factorization" entry in
[future-work](../../SPEC/future-work.md). It consumes the lifting contract
accepted in [hex-mv-hensel](../../HexMvHensel/SPEC/hex-mv-hensel.md), the content, exact
division, and squarefree decomposition accepted in
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md), the representation fixed by
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md), and univariate
integer factorization from
[hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md).
It owns everything hex-mv-hensel lists under "What stays in the
downstream consumer" and nothing that hex-mv-hensel already owns.

## Why this library exists

**Factorization is the operation the multivariate stack was built
for.** hex-mv-poly fixed the representation, hex-mv-gcd added division,
content, and squarefree decomposition, and hex-mv-hensel added the
lift. Each of those exists because factoring `f ∈ ℤ[x₁, …, x_v]` needs
it, and none of them factors anything. This library is the driver that
calls them in Wang's EEZ order and is responsible for the choices the
lift refuses to make: which variable stays, where the others are
evaluated, how the leading coefficient is distributed, and what to do
when the lift is rejected.

**Downstream consumers want irreducible factors, not a product.**
Partial fraction decomposition in several variables, the projection
phase of cylindrical algebraic decomposition, and primary decomposition
all need the *irreducible* factors, and each of them is unsound when
handed a decomposition that merely multiplies back. A product identity
is cheap and proves nothing about irreducibility, so this library keeps
the two claims in separate types with separate checkers and separate
soundness theorems.

**The search is where the interesting decisions are.** Every failure
mode of EEZ is a decision this library makes: a point that drops the
degree, a point whose image is not squarefree, a point that splits `f`
more finely than `f` splits, a prime that makes coprime images look
non-coprime, a leading-coefficient distribution that admits no integer
rescaling, and a modulus that is too small for reconstruction. The
lifting engine reports each of them as a distinct `Failure`
constructor precisely so that the policy can live here.

## Scope

In scope: structural reductions (zero, units, constants, monomial
content, integer content), squarefree decomposition and multiplicity
bookkeeping, the main-variable choice, evaluation-point search,
univariate factorization of the image, factorization of the leading
coefficient and its distribution among the factors, construction of
hex-mv-hensel `Input` values and the discharge of V1 to V6, the
modulus schedule, the retry and recombination policy, the decomposition
certificate and its checker, the irreducibility certificate and its
checker, and the complete Kronecker route that makes irreducibility
decidable without a coefficient bound.

Not in scope, and each is named again where it is used: multivariate
Hensel lifting itself, the multivariate diophantine solver, the
coefficient bound and its proof, gcd, content, exact division, and
squarefree decomposition, univariate integer factorization, and integer
factorization of the content.

The Mathlib companion also owns the multivariate extensions to the shared
`factor_poly` / `irreducibility` elaborators: direct support for the two
multivariate polynomial representations and atom reification for open ring
expressions. The computational search and checkers remain in this library;
the companion owns only the expression-facing reifier and tactic assembly,
plus the transport into Mathlib propositions.

Also not in scope: factorization coefficient rings other than `Int`, absolute
factorization (factoring over `ℚ̄` or a number field), factorization
over `F_q[x₁, …, x_v]`, and sparse Hensel lifting (see
[hex-mv-hensel §Future extension: sparse Hensel lifting](../../HexMvHensel/SPEC/hex-mv-hensel.md)).
The arbitrary commutative ring accepted by the expression tactic is only the
target of evaluation of an integer polynomial; the factorizer still runs over
`Int` coefficients.

**Why `Int` and not a general coefficient domain.** The four
ingredients this library composes are all integer-specific. Univariate
Berlekamp-Zassenhaus is a `ZPoly` algorithm whose recombination and
coefficient recovery are built on Mignotte's bound. hex-mv-hensel's
whole modular apparatus, the prime, the exponent, the symmetric
representatives, and the reconstruction test, exists because `ℤ` is not
a field. Wang's leading-coefficient distribution is a divisibility
argument among *integers*, namely the values `L_j(a)`. And the content
and primitive-part conventions below are exactly the ones that stop
being interesting over a field. A version over `ℚ` is clearing
denominators followed by this library; a version over `F_q` is a
different algorithm with a different lifting engine, and pretending
otherwise would produce an interface with one nontrivial instance.

## The two claims, and why they have separate types

The single most important thing this SPEC fixes is that a checked
product is not a factorization. Both statements are useful, they cost
very different amounts to establish, and conflating them is the
standard way a computer algebra system ends up asserting irreducibility
it never verified.

```lean
namespace Hex.MvFactor

/-- One entry of a decomposition. -/
structure Factor (n : Nat) (cmp : Mono n → Mono n → Ordering) where
  factor       : MvPoly n Int cmp
  multiplicity : Nat

/-- A product decomposition of a subject supplied by the caller: an
integer scalar and a list of powers. Nothing here claims the factors
are irreducible. -/
structure Decomp (n : Nat) (cmp : Mono n → Mono n → Ordering) where
  content : Int
  factors : List (Factor n cmp)

def Decomp.product (D : Decomp n cmp) : MvPoly n Int cmp :=
  D.factors.foldl (fun acc e => acc * e.factor ^ e.multiplicity) (C D.content)

def checkDecomp (f : MvPoly n Int cmp) (D : Decomp n cmp) : Bool
```

`checkDecomp f D` requires all of:

- **D1.** `D.product = f`, an exact identity in `MvPoly n Int cmp`.
- **D2.** Every `multiplicity` is positive.
- **D3.** Every `factor` is nonconstant (`vars ≠ []`).
- **D4.** Every `factor` is normalized: `polyNormalize e.factor = e.factor`
  and `content e.factor = 1`.
- **D5.** The factors are pairwise distinct.

```lean
/-- What a checked decomposition witnesses. -/
def IsDecompOf (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop :=
  D.product = f ∧
  (∀ e ∈ D.factors, 0 < e.multiplicity ∧ ¬ IsConst e.factor)

/-- Accepted data tied to the subject its caller asked about. -/
structure CheckedDecomp (f : MvPoly n Int cmp) where
  raw   : Decomp n cmp
  valid : checkDecomp f raw = true

theorem checkDecomp_sound : checkDecomp f D = true → IsDecompOf f D
```

Indexing the checked form by the subject is the lesson
[hex-int-factor](hex-int-factor.md) records with
`CheckedFactorization`: a record carrying a decomposition of one
polynomial is a perfectly good `Decomp` for any other, so either every
downstream theorem carries `checkDecomp f D = true` as a hypothesis or
the validity travels with the data. The second is better, and it is
what "takes checked data" has to mean.

D2 and D3 are what stop the trivial decomposition `⟨1, [(f, 1)]⟩` from
being *wrong*; they do not stop it from being *uninformative*, and
nothing in this type does. D4 and D5 buy canonicity rather than
soundness: `polyNormalize` fixes the sign from the `cmp`-leading
coefficient, `content = 1` puts every integer factor in the scalar, and
distinctness makes the multiplicities unambiguous. Without D5, the same
polynomial could appear twice and `multiplicity` would mean nothing.

**Normalization depends on the monomial order, and over `ℤ` as well.**
This is the same trap [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) records for `gcd`:
negation flips every coefficient at once, but *which* monomial is
leading changes with `cmp`, so `x - y` normalizes to `x - y` under an
order with `x` leading and to `y - x` under an order with `y` leading.
So the transported statement is one lemma with an explicit unit,
`factor_reorder` below, not an equality.

The stronger claim is a separate structure carrying one irreducibility
certificate per factor:

```lean
/-- A decomposition together with a certificate that each factor is
irreducible. This is a complete factorization up to the integer
content, which is deliberately not factored. -/
structure Complete (n : Nat) (cmp : Mono n → Mono n → Ordering) where
  decomp : Decomp n cmp
  certs  : List (IrredCert n cmp)

def checkComplete (f : MvPoly n Int cmp) (K : Complete n cmp) : Bool

/-- Mathlib-free irreducibility, reused from
[hex-mv-hensel](../../HexMvHensel/SPEC/hex-mv-hensel.md) rather than restated: no
factorization into two nonunits. The companion identifies it with
Mathlib's `Irreducible`. -/
-- Hex.MvHensel.Irred

def IsFactorizationOf (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop :=
  f ≠ 0 ∧
  IsDecompOf f D ∧
  (∀ e ∈ D.factors, MvHensel.Irred e.factor) ∧
  D.factors.Pairwise fun a b =>
    ∀ u : Int, u * u = 1 → a.factor ≠ b.factor * C u
```

`checkComplete f K` requires `f ≠ 0`, runs `checkDecomp f K.decomp`,
requires `K.certs.length = K.decomp.factors.length`, and runs
`checkIrred` on each factor against its certificate. Its soundness
theorem is stated with the univariate obligations under "The
irreducibility certificate", because that is where they arise.

**The `f ≠ 0` check is not decoration, and leaving it out is the
easiest way to make this type lie.** `⟨⟨0, []⟩, []⟩` passes
`checkDecomp` (its product is `C 0 = 0`), passes the length check, and
passes the empty list of certificate checks vacuously. Without the
explicit rejection, `checkComplete` would therefore accept a "complete
factorization of `0`", contradicting the convention under "Degenerate
inputs" that `0` has none. The same clause is in `IsFactorizationOf`
for the same reason: `0` is not a product of irreducibles, and a Prop
that says it is cannot be transported to Mathlib's `Irreducible`.

The pairwise clause is non-association, and it is what makes the
multiplicities the true ones rather than an arbitrary split of them.
It needs no separate check: the units of `MvPoly n Int cmp` are exactly
`C 1` and `C (-1)`, because the ring is a domain over `ℤ` and a unit
has degree zero in every variable, so D4's normalization plus D5's
distinctness give it. Recording that step here is what stops a later
reader from adding a redundant sixth condition to `checkDecomp`.

**Why the content is not factored.** `Factorization` in
[hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md)
carries a signed integer `scalar` and does not split it into constant
prime polynomials, `sqfDecomp` in [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) carries a
`content : R` and does not factor it, and SymPy's `factor_list` does
the same. This library follows that convention: `C p` for prime `p` is
genuinely irreducible in `ℤ[x₁, …, x_v]`, so the ring-theoretic
factorization is `content`'s prime factorization together with the
polynomial factors, and a caller who wants it composes this library's
answer with [hex-int-factor](hex-int-factor.md)'s
`CheckedFactorization`. That composition is three lines at the call
site and it is the reason hex-int-factor is not a dependency here.
Every completeness statement below therefore reads "into irreducibles
up to the integer content", and never drops the qualifier.

## What a checked decomposition does not prove

[hex-mv-hensel §What a checked lift does not prove](../../HexMvHensel/SPEC/hex-mv-hensel.md)
makes this point about one lift; it is worth making again about the
whole pipeline, because the pipeline has more places to lose it.

- D1 admits `⟨1, [(f, 1)]⟩` for every `f`. A decomposition into `r`
  pieces says nothing about whether those pieces split further.
- A *failed* search proves nothing either. The search gives up when its
  fuel runs out, and by default its fuel runs out long before the
  modulus reaches the proved coefficient bound, so "no finer
  decomposition was found" is not "no finer decomposition exists".
- In particular a rejected lift is not a refutation. `lift` returning
  `.error (.reconstruct m)` becomes the statement "no factorization
  compatible with this splitting exists" only under
  `no_lift_of_reconstruct`, whose hypotheses are `valid inp`,
  `BoundsFactors inp B`, and `2 * B < inp.setup.modulus`. The default
  configuration satisfies none of the last two, and "Why a failed lift
  is not a refutation" says what it would cost to.

Everything this library says about irreducibility is therefore carried
by `IrredCert` and by nothing else.

## The irreducibility certificate

```lean
/-- A checkable witness that a polynomial is irreducible, modulo a list
of univariate irreducibility obligations that the checker cannot
discharge Mathlib-free. -/
inductive IrredCert :
    (n : Nat) → (cmp : Mono n → Mono n → Ordering) →
    [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type 1
  | degreeOne (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (prim : ContentCert n Int cmp') :
      IrredCert (n+1) cmp
  | image (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (a : Fin n → Int)
      (prim : ContentCert n Int cmp') : IrredCert (n+1) cmp
  | embed (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
      [IsMonomialOrder cmp'] (sub : MvPoly n Int cmp')
      (cert : IrredCert n cmp') : IrredCert (n+1) cmp
  | kronecker (scalar : Int) (uni : List (ZPoly × Nat)) : IrredCert n cmp

def checkIrred (g : MvPoly n Int cmp) (c : IrredCert n cmp) : Bool

/-- The univariate irreducibility facts a successful `checkIrred` still
needs. Computed from the subject and the certificate, so a caller can
see exactly what it is trusting. -/
def obligations (g : MvPoly n Int cmp) (c : IrredCert n cmp) : List ZPoly

theorem checkIrred_sound
    (h : checkIrred g c = true)
    (ho : ∀ F ∈ obligations g c, MvHensel.Irred F) :
    MvHensel.Irred g

theorem checkComplete_sound
    (h : checkComplete f K = true)
    (ho : ∀ e ∈ K.decomp.factors.zip K.certs,
            ∀ F ∈ obligations e.1.factor e.2, MvHensel.Irred F) :
    IsFactorizationOf f K.decomp
```

`IrredCert` lives in `Type 1` because its `degreeOne` and `image`
constructors store `ContentCert n Int cmp'`, whose coefficient type is an
index and therefore already places that certificate in `Type 1`.  This is a
universe requirement only; it does not change the stored evidence or checker.

**The obligations are the honest part of this design.** Irreducibility
of a univariate integer polynomial is not something the Mathlib-free
tree decides: `ZPoly.factorize` is total and returns factors it calls
irreducible, but the theorem that they are irreducible is
`hex-berlekamp-zassenhaus-mathlib`'s, proved from completeness of
classical recombination. Rather than pretend otherwise, `checkIrred`
reduces multivariate irreducibility to a list of univariate statements
and names them. The companion discharges the list, either from the
factorizer's own theorem or from
`Decidable (Irreducible f)` for `Polynomial ℤ`, and only then is the
conclusion unconditional. This is [design
principle 2](../../SPEC/design-principles.md) applied to a hypothesis about
irreducibility rather than about analysis, and it has the same shape as
hex-mv-hensel stating `BoundsFactors` and letting its companion
discharge it.

### `degreeOne`

`checkIrred g (.degreeOne i cmp' prim)` requires `degreeOf i g = 1` and
`checkContent (toUnivariate i cmp' g).toList prim = true` with
`prim.value = 1`. It contributes no obligations.

If `g = u · w` then `degreeOf i u + degreeOf i w = 1`, because degrees
in a domain add, so one factor, say `u`, is constant in `x_i` and is
therefore `constIn i cmp' ū` for a unique `ū : MvPoly n Int cmp'`.
Every coefficient of `toUnivariate i cmp' g` is then `ū` times the
corresponding coefficient of `toUnivariate i cmp' w`, so `ū` is a
common divisor of the coefficient list `checkContent` was run against,
and that checker's maximality clause with `value = 1` makes `ū` a unit.
`constIn` carries units to units in both directions, so `u` is a unit
too. `g` itself is a nonunit because its degree is positive.

This is the constructor that covers `X j`, and with it every factor of
a monomial content, at no cost and with nothing left to discharge.

### `image`

`checkIrred g (.image i cmp' a prim)` requires `degreeOf i g ≥ 1`,
requires `MvPoly.eval a (lcIn i cmp' g) ≠ 0`, and requires the same
content check as `degreeOne`. Its obligation list is
`[ZPoly.primitivePart (imageAt i cmp' a g)]`.

The argument is hex-mv-hensel's
`irreducible_of_image_irreducible` argument, run one step further so
that it tolerates a nonunit integer scale on the image. Write
`F = imageAt i cmp' a g`, `γ = ZPoly.content F`, and
`h = ZPoly.primitivePart F`, so `F = γ · h` with `h` primitive and, by
the obligation, irreducible.
Suppose `g = u · w`. Applying the ring homomorphism `imageAt i cmp' a`
gives `imageAt u · imageAt w = γ · h`. Taking contents and primitive
parts, which is Gauss's lemma at arity one and is
[hex-poly-z](../../HexPolyZ/SPEC/hex-poly-z.md)'s
`content (f * g) = content f * content g`, gives
`primitivePart (imageAt u) · primitivePart (imageAt w) = ± h`, so one
of the two primitive parts, say the first, is a unit and `imageAt u` is
a nonzero constant. The leading coefficients satisfy
`lcIn u · lcIn w = lcIn g`, and `eval a (lcIn g) ≠ 0` in the domain
`MvPoly n Int cmp'` forces `eval a (lcIn u) ≠ 0`, so the `x_i`-degree
of `u` does not drop under evaluation and `degreeOf i u = 0`. The
content check then makes `u` a unit, exactly as in `degreeOne`.

**Why the scale matters and why this is not a citation of
`irreducible_of_image_irreducible`.** That theorem's hypothesis is
`Irred (inp.images[j])`, irreducibility of the image *as the lift
received it*. The images this library builds are rescaled by Wang's
leading-coefficient correction, so `inp.images[j] = γ_j · h_j` with
`γ_j` a nonunit integer whenever the evaluation introduces content, and
the hypothesis is then false while the conclusion is still true. When
the scale happens to be `± 1` the theorem does apply, given its other
hypotheses; the point is that nothing guarantees it, so this library
proves the scaled form itself rather than depending on a case
distinction the caller cannot control. The proof is
the same argument with one extra Gauss step, it needs no lift at all,
and it is the reason `image` mentions no prime, no exponent, and no
`Input`. "Open questions" records the amendment that would let
hex-mv-hensel state the scaled form once.

**The `image` route is the one that normally fires.** For an
irreducible primitive `g`, Gauss's lemma makes `g` irreducible in
`ℚ(other variables)[x_i]`, and Hilbert's irreducibility theorem says
the integer points at which that irreducibility fails to specialize
form a thin set. So a small random point usually gives an irreducible
image and a certificate with one univariate obligation. Nothing is
proved from that, in exactly the way [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) proves
nothing from the success rate of its heuristic gcd: it is why the cheap
route is worth trying first, and the fuel makes the producer partial
regardless.

### `embed`

`checkIrred g (.embed i cmp' sub cert)` requires
`g = constIn i cmp' sub` and `checkIrred sub cert = true`, and its
obligations are `sub`'s.

`constIn i cmp'` is an injective ring homomorphism onto the polynomials
of `x_i`-degree zero. A factorization of `constIn i cmp' sub` has both
parts of `x_i`-degree zero because degrees add, so both are in the
image, and injectivity pulls the factorization back to arity `n`. Units
on both sides are `±1`, so nonunits map to nonunits.

This is the constructor for factors found in `contentIn i cmp' f`,
which the pipeline factors one arity down. It is what makes the
certificate type recurse on the arity in the same way the pipeline
does.

### `kronecker`

The complete route. It needs no evaluation point, no prime, and no
coefficient bound, and it is the reason irreducibility is decidable
here at all.

Fix `d j = degreeOf j g` and the mixed-radix weights
`w 0 = 1`, `w j = ∏_{k < j} (d k + 1)`. The substitution

```text
kron d p = p(z^(w 0), …, z^(w (n-1)))  :  MvPoly n Int cmp → ZPoly
```

is a ring homomorphism, and it is injective on the monomials with
`degreeOf j ≤ d j`, because those exponent vectors are exactly the
mixed-radix digit strings for the weights. Its partial inverse
`unKron?` reads the digits back and fails when a digit exceeds its
bound.

**This is not `HexPolyZ/Kronecker.lean`.** That file packs the
*coefficients* of a `ZPoly` into a single integer to multiply through
`Nat` arithmetic. This substitution packs the *variables* of an
`MvPoly` into a single variable. Both are called Kronecker
substitution in the literature and neither reduces to the other, so the
names here are `kron` and `unKron?` and the collision is worth naming
once rather than being rediscovered.

Write the certificate's univariate data as `uni = [(P_1, e_1), …]`.
`checkIrred g (.kronecker scalar uni)` requires:

- `content g = 1`, the producer-free scalar content fold, and
  `¬ IsConst g`;
- `C scalar * ∏_k P_k ^ e_k = kron d g` in `ZPoly`;
- every `P_k` primitive of positive degree, and the `P_k` pairwise
  distinct;
- for every exponent vector `b` with `b ≤ e` and `b ∉ {0, e}`: either
  `unKron? d (∏_k P_k ^ b_k)` is `none`, or the polynomial it returns is
  constant, or exact division of `g` by that polynomial fails.

Its obligations are `uni.map Prod.fst`.

Every divisor of `g` has `degreeOf j ≤ d j`, because degrees add in a
domain, so it lies in the range where `kron` is injective on monomials.
Injectivity on monomials means the divisor's coefficients reappear
unchanged at distinct exponents of the image, so a primitive divisor
has a primitive image. `g` is primitive, so every divisor of `g` is
primitive up to sign, and its image is therefore `± ∏_k P_k ^ b_k` for
some `b ≤ e`, by unique factorization in `ℤ[z]` and the obligations.
The enumeration visits the image of every candidate proper divisor, so
refuting all of them refutes every proper factorization. Two things are
deliberately not enumerated. `scalar` is not, because a primitive
divisor contributes none of it. And the sign is not, because
`unKron?` is linear and `u ∣ g` exactly when `-u ∣ g`, so one
representative of each pair settles both. `b = 0` and `b = e` are the
excluded ends for the same reason they are the trivial factorizations:
`kron` is injective on the monomials involved, so `b = e` forces
`u = ± g` and `b = 0` forces `u = ± 1`.

**Its cost is the point of it, not an oversight.** `kron d g` has
degree `∏_j (d j + 1) - 1`, so factoring it is univariate factorization
at dense-size degree, and the enumeration is `∏_k (e_k + 1)` exact
divisions. Neither has a useful bound in terms of the input, and both
are astronomically worse than the `image` route on inputs where the
`image` route fires. It is specified for the same reason
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md)'s extended-subresultant route and
[hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md)'s
`factorTrial` are: it is unconditional, it needs no bound anybody has to
prove, and it is what makes the companion's `Decidable` instance total.

**The checker does not refactor.** The certificate carries the
univariate factorization, so `checkIrred` verifies a product identity
in `ZPoly` rather than re-running Berlekamp-Zassenhaus. The
enumeration, which the checker does re-run, is exact division and
nothing else. That is the smallest checker this route admits: a
negative statement about every subset has no shorter witness than the
list of refutations, and each refutation is one division.

### The other side: reducibility

Irreducibility is expensive to certify and reducibility is cheap, so
the two get different types:

```lean
/-- A factorization into two nonunits. -/
structure Split (n : Nat) (cmp : Mono n → Mono n → Ordering) where
  left  : MvPoly n Int cmp
  right : MvPoly n Int cmp

def checkSplit (g : MvPoly n Int cmp) (S : Split n cmp) : Bool

theorem checkSplit_sound : checkSplit g S = true → ¬ MvHensel.Irred g
```

`checkSplit g S` requires `S.left * S.right = g` and that neither side
is a unit, which for `MvPoly n Int cmp` is `polyIsUnit`. One
multiplication and two constant-time tests, no obligations.

The Kronecker sweep produces one or the other, and that is what makes
it a decision rather than a search:

```lean
inductive Verdict (n : Nat) (cmp : Mono n → Mono n → Ordering)
  | irreducible (cert : IrredCert n cmp)
  | reducible   (split : Split n cmp)

/-- Total on a nonconstant primitive subject: the sweep either refutes
every candidate divisor, and returns the certificate recording that, or
it finds one, and returns it. -/
def kronDecide (g : MvPoly n Int cmp) : Verdict n cmp

theorem kronDecide_irreducible
    (hprim : MvPoly.content g = 1)
    (hnonconst : ¬ MvPoly.IsConst g)
    (h : kronDecide g = .irreducible c)
    (ho : ∀ F ∈ obligations g c, MvHensel.Irred F) :
    MvHensel.Irred g
theorem kronDecide_reducible (h : kronDecide g = .reducible S) :
    checkSplit g S = true
```

**Retaining the divisor is not an optimisation.** Without it the sweep
would answer "no certificate produced", which is indistinguishable from
"budget exhausted" and cannot discharge a negative. The companion's
`Decidable` instance needs both branches of a genuine decision, and
`.reducible` is the branch that supplies the `isFalse`. The sweep
already has the divisor in hand at the moment it stops, so keeping it
costs nothing.

Constants are outside `kronDecide`, which requires `¬ IsConst g`. `C p`
is irreducible in `ℤ[x₁, …, x_v]` exactly when `p` is a prime integer,
and this library has no primality test and does not want one, for the
reason under "The two claims". The constant case is therefore decided
in the companion, where Mathlib's integer primality decision is already
available; `0` and `± 1` are the two remaining constants, and neither
is irreducible.

### Why a failed lift is not a refutation

There is an obvious fifth constructor, and this SPEC deliberately does
not have it: refute a proper splitting by exhibiting an
`MvHensel.Input` for it whose `lift` fails. It is not admissible as
written, and the reason is worth recording so that it is not added
later by someone reading `lift_none` too quickly.

`lift_none` says a lift of a *nonexistent* compatible factorization
fails. The converse, `no_lift_of_reconstruct`, is the one a refutation
needs, and its hypotheses are `valid inp`, `BoundsFactors inp B`, and
`2 * B < inp.setup.modulus`. So the constructor would carry a second
kind of obligation, a coefficient bound discharged by
`boundsFactors_coeffBound` in hex-mv-hensel's companion, and the
checker would have to run the lift at a modulus past `2 * coeffBound`.
Two things follow. The modulus is not one the search reaches: the
schedule under "Reconstruction and the modulus schedule" doubles from a
heuristic estimate and stops, and hex-mv-hensel says plainly that
lifting to the proved bound is not something a caller wants to do.
And the refutation would have to be repeated for every admissible
leading-coefficient distribution of the splitting, since a factor's
leading coefficient is only constrained to be a divisor of `lcIn g`
with a prescribed value at the point, which requires a complete
factorization of `lcIn g` to enumerate.

The result would be a certificate that is conditional on an unproved
bound, expensive to check, and no cheaper than `kronecker` on the
inputs where it is needed. If the companion proves the Mahler length
form of the bound, whose exponent is linear in `d₁ + Σ_t d_t` rather
than in their product, the arithmetic changes and the constructor
becomes worth having; "Open questions" records that as an amendment
with its prerequisite named.

## The pipeline

Everything below is untrusted. It produces `Decomp` and `IrredCert`
values, and `checkDecomp` and `checkIrred` decide whether they are
accepted, in the sense of [design
principle 4](../../SPEC/design-principles.md).

**Termination.** The pipeline enters itself twice, at step 2 on
`contentIn i cmp' s` and at step 4 on `lcIn i cmp' s`, and both are at
arity `n` when the caller was at arity `n + 1`, so the recursion is
structural on the arity and bottoms out at the constants. Everything
else in a single call is bounded by the configured fuel. The arity drop
is free rather than an invariant to maintain, for the reason
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) gives about its own certificate: the types
of `contentIn` and `lcIn` say so.

### 0. Structural reductions, always applied

In order, each of which shrinks the problem without any search:

- **Zero.** `f = 0` gives `⟨0, []⟩`, whose product is `0`, so it is a
  checked decomposition. It is not a `Complete`: `0` has no
  factorization into irreducibles, and `complete?` reports
  `.zero` rather than returning a structure whose meaning would have to
  be special-cased by every consumer.
- **Constants.** `f = C c` gives `⟨c, []⟩`, including the units `±1`.
  D3 keeps constants out of the factor list, so this is the only place
  they can go.
- **Monomial content.** Divide out `monoContent f` and emit one factor
  `X j` with multiplicity `m j` for each variable in it. Each of those
  factors gets a `degreeOne` certificate, so the monomial part of the
  answer is complete with no obligations at all.
- **Integer content.** Divide out `content f` from
  [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md), which is the producer-free scalar fold,
  and put it in `Decomp.content` together with the sign that
  `polyNormalize` extracts.

After these, `f` is primitive, nonconstant, and not divisible by any
variable.

### 1. Squarefree decomposition

Call `sqfDecomp` from [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md). It returns
`⟨c, [(s_k, k)]⟩` with the `s_k` squarefree, primitive, nonconstant,
pairwise coprime, and of distinct multiplicities; `c` is `±1` here,
because step 0 already removed the content, and it multiplies into
`Decomp.content`. Factor each `s_k` and raise every factor found to the
power `k`.

Two things this buys, both of which the rest of the pipeline assumes.
The factors of `s_k` are pairwise distinct, so D5 holds after the
merge. And each `s_k` being squarefree is what makes an evaluation
point with a squarefree image *available*: if `f` had a repeated
factor, every image would be non-squarefree and the point search would
never succeed.

Nothing is lost by factoring the pieces separately, because
`sqfDecomp_coprime` makes factors of different multiplicity coprime, so
no factor is discovered twice.

### 2. The main variable, and the content in it

For a squarefree primitive `s`, choose `i` with `degreeOf i s > 0`,
split `s = constIn i cmp' (contentIn i cmp' s) * primPartIn i cmp' s`,
factor the content one arity down by recursive entry into this same
pipeline, and wrap each factor found there in `embed`.

The content and the primitive part are coprime: a common divisor would
have its square dividing `s`, contradicting squarefreeness. So the two
factor lists concatenate without a merge step, which is the same
argument [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) makes for Yun's content recursion.

Steps 3 to 7 work on `primPartIn i cmp' s`, and `s` denotes it from
here on, so `contentIn i cmp' s = 1` throughout them. That primitivity
is used three times: it is what makes a factor constant in `x_i`
impossible, it is the hypothesis of the `image` and `degreeOne`
certificates, and it is what makes "the image never hides a
factorization" below true.

**Choosing `i` is a heuristic with two opposed costs, and no rule
dominates.** The lift costs `O(∏_{j ≠ i} (d_j + 1))` univariate solves,
which argues for keeping the *largest* degree in the main variable so
that it is not in the product. The univariate factorization and the
recombination search cost grow with `d₁ = degreeOf i s` and with the
number of univariate factors, which argues for the *smallest*. The rule
this library uses, in order: prefer a variable in which `lcIn i cmp' s`
is a nonzero constant, since that removes the leading-coefficient
distribution entirely; then prefer the variable minimising the term
count of `lcIn i cmp' s`; then prefer the largest `degreeOf i s`. The
benchmark family "main-variable choice" measures the rule against the
alternatives rather than asserting it, and the choice is recorded in
the trace so a regression is attributable.

### 3. Evaluation points

The point search is where most failures are caught, and it catches them
before any lifting happens.

```lean
/-- Why a candidate point was rejected. Recorded per attempt in the
trace, and aggregated in `Failure.point`. -/
inductive PointReject
  | degreeDrop
  | notSquarefree
  | leadingSplit

/-- What an accepted point yields. The point loop returns this, so the
univariate factorization and the assignment are computed once and not
recomputed by the caller. -/
/- Here `n` is the number of non-main variables, so the target has arity
`n + 1`.  Indexing `Probe` by the target arity would not determine the
`Fin n` point or the inner comparator at arity zero. -/
structure Probe (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering) where
  point   : Fin n → Int
  images  : List ZPoly                 -- rescaled, so V3 and V4 hold
  leading : List (MvPoly n Int cmp')
  uni     : List ZPoly                 -- the primitive irreducible h_j
```

A candidate `a : Fin n → Int` is admissible when:

1. **No degree drop.** `MvPoly.eval a (lcIn i cmp' s) ≠ 0`. This is
   hex-mv-hensel's V2, it is one evaluation, and it is checked first
   because it is the cheapest.
2. **Squarefree image.** `SquareFreeRat (imageAt i cmp' a s)`, which is
   [hex-poly-z](../../HexPolyZ/SPEC/hex-poly-z.md)'s relative predicate
   and already carries a `Decidable` instance; the underlying test is
   the gcd of the *primitive part* with its derivative, through
   [hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md).

   The relative predicate is the right one and the ring-theoretic one
   would be wrong here. Evaluation routinely gives the image a nonunit
   integer content, and `F = 2(x² + 1)` is not squarefree in `ℤ[x]`
   while its polynomial part is and its factorization is
   multiplicity-free. Testing `F` itself would reject good points for a
   property the algorithm does not need. This is the same convention
   [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) fixes under "What squarefree means
   here".
3. **A usable leading-coefficient distribution exists**, in the sense
   of the next section.

Condition 2 is load-bearing in three separate places, which is why it
is an admissibility condition rather than something discovered later.
It makes the univariate factors pairwise coprime, so V6 has a chance of
holding at some prime. It makes the univariate factorization
multiplicity-free, which is what makes the rescaling identity under
"Leading coefficients" reproduce V3 exactly. And it makes the map from
divisors of `s` to subsets of the univariate factors well defined,
which is what the recombination search enumerates over.

**Small points, and why the search does not draw uniformly.** The
lifting engine works in shifted coordinates and the coefficient bound
it needs is a bound on the *shifted* factors, which grow with the size
of the point: hex-mv-hensel's own example has factors with coefficients
at most `1` whose shift at `a = 10` carries a coefficient of `20`. The
search therefore enumerates points in shells of increasing `‖a‖_∞`,
starting from `0`, and within a shell draws the order from the supplied
`Rand`. Zero coordinates are free in a second sense: `shift` is the
identity in a variable whose coordinate is zero, so a point with many
zeros keeps the target sparse.

**Preferring points with fewer image factors.** The number of
univariate factors bounds the recombination search, and different
admissible points give different counts. The search examines up to
`cfg.pointScouts` admissible points and keeps the one whose image has
the fewest factors, which is Wang's own rule. The count is only ever an
upper bound for the number of true factors, so a point achieving the
minimum over the scouted set is a heuristic and never a proof; a point
whose image is irreducible is different, and that case exits
immediately through the `image` certificate.

Randomness is an explicit `Rand` argument and the advanced state comes
back with the result, following the convention
[hex-finite-field](hex-finite-field.md) sets under "Randomness".

### 4. Leading coefficients

This is the step hex-mv-hensel refuses to do, for the reason it gives:
finding the distribution is itself recursive multivariate
factorization, so doing it below the factorizer would make the graph
circular.

Decompose `Λ = lcIn i cmp' s` by recursive entry into this pipeline at
arity `n`, giving `Λ = c · ∏_m Ω_m^{b_m}`. That decomposition does not
depend on the point, so it is computed **once per main variable**,
before the point loop, and only the assignment below is redone per
point. Write `h_1, …, h_r` for the primitive irreducible univariate
factors of `F = imageAt i cmp' a s`, so that `F = scalar · ∏_j h_j`
with the product multiplicity-free by admissibility condition 2.

**A decomposition suffices here; irreducibility of the `Ω_m` is not
needed.** V4 constrains the product and the values, not the nature of
the pieces, so the recursive call is `factorWith` rather than
`completeWith` and no certificate is produced for `Λ`. A coarser
decomposition only makes the assignment fail more often, which costs a
point rather than correctness. This matters because the leading
coefficient is one of the two places the pipeline recurses, and paying
for certificates there would multiply the work for no gain.

Wang's assignment then works entirely in the integers, in two stages:
first which `Ω_m` go where, then how much of `c` goes with them.

**Stage one: the polynomial parts, by division by the evaluated
factor.** Set `d_m = Ω_m(a)`. The assignment is unambiguous exactly
when the `d_m` can be separated from each other and from `scalar`, and
the test for that needs no prime factorization: strip
`g = gcd(d_m, previous)` repeatedly from `d_m` while `g ≠ 1`, and
require what is left to be more than `1`. That is Wang's non-divisor
condition, and it is the gcd loop
`dmp_zz_wang_non_divisors` implements. When it fails, the point is
rejected with `.leadingSplit` and the search moves on, which is one of
the responses hex-mv-hensel names under "Leading coefficients" and
costs one point rather than a search over distributions.

With the condition in force, the exponent of `Ω_m` in `L_j` is the
number of times `d_m` divides `lc h_j · c`, computed by repeated exact
division, and the assignment is rejected unless those exponents sum
over `j` to `b_m`.

**Divide by the value, not by a prime.** Counting instead the
multiplicity of some prime `q_m ∣ d_m` in `lc h_j` is wrong whenever
`d_m` is not squarefree as an integer. With
`s = (y·x + 1)(x + 1)` at `y = 4`, `Λ = Ω_1 = y` and `b_1 = 1`, the
images have leading coefficients `4` and `1`, and `d_1 = 4`. The only
available prime is `q = 2`, whose multiplicity in `4` is `2`, so the
prime rule assigns `Ω_1` the exponent `2` and the sum check then
rejects a distribution that is in fact correct. Dividing by `d_1 = 4`
gives the exponent `1`, which is the truth. The prime formulation also
smuggles in an integer factorization that neither the dependency list
nor the complexity table pays for; the division formulation needs only
exact division and gcd.

**Stage two: the integer part, and why putting it all in one `L_j` is
wrong.** The tempting shortcut is to say that V4 constrains only the
product `∏_j L_j` and the values `L_j(a)`, so the placement of `c` does
not matter. It does. `check`'s condition C4 pins each lifted factor's
leading coefficient to the `L_j` it was given, so a placement that
differs from the true factors' own leading coefficients makes
`IsLiftOf` uninhabited, and `lift` then reports `.reconstruct` on an
input that has a perfectly good factorization. With main variable `x`,
one other variable `y`, and
`s = (2y·x + 1)(3x + y)` at `y = 5`, the images are `h_1 = 10x + 1` and
`h_2 = 3x + 5`, `Λ = 6y`, and the truth is `(L_1, L_2) = (2y, 3)`.
Placing all of `c = 6` in `L_1` gives `(6y, 1)`, whose second entry
does not even admit an integer rescaling, and a variant of the same
example where both rescalings happen to be exact fails later and more
expensively.

Write `P_j` for the polynomial part stage one assigned to `j`. The
rescaling below needs `lc h_j ∣ L_j(a)`, so the integer multiplier of
`L_j` is at least

```text
need_j = |lc h_j| / gcd (|lc h_j|) (|P_j(a)|) .
```

Those are forced. The assignment is rejected unless `∏_j need_j ∣ |c|`,
each `L_j` receives its `need_j`, and the residual `|c| / ∏_j need_j`
together with the sign of `c` is placed on `L_1`. On the running
example, `need_1 = 10 / gcd(10, 5) = 2` and `need_2 = 3 / gcd(3, 1) = 3`,
whose product is exactly `|c| = 6`, so the residual is `1` and the
assignment is the truth.

**The residual placement can be genuinely ambiguous, and the recovery
is the ordinary one.** The `need_j` are forced but the residual is not.
With `Λ = 8` and `lc h_1 = lc h_2 = 2` the `need_j` are both `1` and
the residual is `8`, so `(2, 4)` and `(4, 2)` both satisfy every
constraint above and at most one matches the truth. Putting the
residual on `L_1` is a deterministic choice, not a derivation; a wrong
choice shows up as a `.reconstruct` failure, and the response is the
same as for an unlucky point, another point. Enumerating the residual's
placements instead would sometimes save a point, and "Open questions"
records that rather than pretending the deterministic choice is
forced.

The assignment produces candidate leading coefficients `L_1, …, L_r`
with `∏_j L_j = Λ`, which is V4's first condition. The second
condition, `MvPoly.eval a L_j = lc F_j`, is then *made* to hold by
rescaling the univariate factors:

```text
γ_j = L_j(a) / lc h_j ,      F_j = γ_j · h_j .
```

The division must be exact; when it is not, the assignment is rejected.

**This rescaling is exactly what makes V3 an identity over `ℤ`.**
hex-mv-hensel requires `∏_j F_j = imageAt i cmp' a s` and says only
that folding the univariate factorizer's scalar into a factor is the
caller's job. The rescaling does it, and it does it in the one way that
keeps V4 true at the same time:

```text
∏_j γ_j = (∏_j L_j(a)) / (∏_j lc h_j) = Λ(a) / lc(∏_j h_j)
        = lc F / (lc F / scalar) = scalar ,
```

using `Λ(a) = lc F`, which is admissibility condition 1, and
`F = scalar · ∏_j h_j`. So `∏_j F_j = scalar · ∏_j h_j = F`. Folding
the scalar into a single factor instead would satisfy V3 and break V4
for every factor whose leading coefficient then fails to match, which is
the failure hex-mv-hensel reports as `.leadingImage j`.

**The rescaled images are not irreducible, and that is fine.** `F_j` is
a nonunit integer times an irreducible primitive polynomial as soon as
`γ_j ≠ ±1`. Nothing in the lift needs the images irreducible; V1
requires only positive degree, which rescaling preserves. The one place
irreducibility of an image is used is the `image` certificate, and it
is stated about `ZPoly.primitivePart`, which is `h_j` again.

**The monicised alternative is not taken.** Replacing `s` by
`Λ^(d₁ - 1) · s(x_i / Λ)`, which is monic in `x_i`, removes the
distribution problem entirely: every factor's leading coefficient is
`1` and the assignment is unique. It also multiplies the coefficient
size by up to `‖Λ‖^(d₁ - 1)` and multiplies the degrees in the other
variables by `d₁`, which the lift pays for as `∏_{j ≠ i}(d_j + 1)`
grows. This library uses the non-divisor assignment above and
treats its failure as a reason to change the point. "Open questions"
records what monicisation would be worth if the assignment turns out to
fail often in practice.

### 5. Building the `Input`, and discharging V1 to V6

The lift refuses to start unless `valid inp` holds. Every condition it
checks has a named source here, and this table is the answer to "does
the caller actually supply what the lifting engine requires":

| condition | what it demands | discharged by |
|---|---|---|
| V1 | equal list lengths, `r ≥ 1`, `l ≥ 1`, `d₁ ≥ 1`, `deg F_j ≥ 1` | lists built together in step 4; `l ≥ 1` from the modulus schedule; `d₁ ≥ 1` from the main-variable choice; positive degree because `ZPoly.factorize` returns nonconstant factors and rescaling preserves degree |
| V2 | `deg (imageAt i cmp' a s) = d₁` | point admissibility condition 1 |
| V3 | `∏_j F_j = imageAt i cmp' a s` | the rescaling identity in step 4 |
| V4 | `∏_j L_j = lcIn i cmp' s` and `L_j(a) = lc F_j` | the assignment and the rescaling in step 4 |
| V5 | `p ∤ lc F_j` | prime selection below |
| V6 | the partial-fraction identity modulo `q`, with `deg σ_j < deg F_j` | `witnessOf?`, retried at the next prime on `none` |

**Prime selection.** `p` is drawn from hex-mod-arith's bundled bounded
prime stream and must divide no `L_j(a)`, which is V5, and must leave
the images coprime, which is V6. The two failures are different: V5 is
decided by one integer test per factor before any polynomial work, and
V6 is decided by `witnessOf?` returning `none`. On `.notCoprime` the
first response is the next prime, because a prime dividing the
resultant of two images makes coprime images look non-coprime and a
different prime fixes it; only after `cfg.primeFuel` primes have
declined does the search conclude that the images share a factor over
`ℤ` and change the point. That is exactly the two-cause reading
hex-mv-hensel gives the failure, and admissibility condition 2 is what
makes the second cause unlikely enough to be tried second.

Small primes are preferred, for hex-mv-gcd's reason: kernel replay of a
bounded prime's primality proof gets expensive near the 31-bit limit.
Only `witnessOf?` and the univariate solves work modulo `p`; the
working modulus `q = p^l` is held as a `Nat` and routinely exceeds 64
bits, so `ZMod64 q` is not the representation, as hex-mv-hensel
records.

### 6. Reconstruction and the modulus schedule

The starting exponent `l` is chosen so that `p^l` exceeds twice a
*heuristic* estimate of the shifted factors' coefficients: the one-norm
of `shift i a s` times a small factor, not `coeffBound inp`. On a
`.reconstruct` failure `liftWith` doubles the exponent and re-derives
the witness, up to `cfg.doublings` times, which is hex-mv-hensel's own
escalation and needs nothing from this library except the budget.

**Why the proved bound is not the schedule.** `coeffBound inp` exists
and `BoundsFactors` is discharged in hex-mv-hensel's companion, so
setting `l` from the bound would make each individual lift decisive.
The two available derivations of that bound are Kronecker substitution
into Mignotte, whose exponent is the *dense size* `∏_j (d_j + 1)` and
so is unusable, and Mahler's length inequality, whose exponent is
linear in `d₁ + Σ_t d_t` and would be usable. Until the companion
proves the second form, starting from the bound would mean starting at
a modulus of astronomical size on every input, so the schedule is
heuristic and the consequence is stated rather than hidden: a
`.reconstruct` failure at the end of the schedule is not a proof that
no compatible factorization exists.

**What the caller gets instead.** Soundness never depends on the
schedule. A successful lift is accepted only through `check`, which is
an exact identity over `ℤ`, so a too-small modulus costs time and never
correctness. That is hex-mv-hensel's "a successful lift needs no bound
at all to be sound", and it is why the heuristic schedule is
admissible.

### 7. Recombination, and unlucky points

A point can be admissible and still split `f` more finely than `f`
splits. hex-mv-hensel's example is `x₁² + x₂` at `x₂ = -1`, whose image
is `(x₁ - 1)(x₁ + 1)` while `f` is irreducible. The lift of the full
splitting then runs to full precision and fails the product test.

The response is to try coarser groupings. A group of univariate factors
multiplied together is a legitimate `Input`, so for a subset
`T ⊆ {1, …, r}` with `0 < |T| < r` the two-block grouping
`[∏_{j ∈ T} F_j, ∏_{j ∉ T} F_j]` is lifted, with leading coefficients
`∏_{j ∈ T} L_j` and its complement. V1 through V5 survive the grouping
by multiplicativity: the two block products still multiply to the
image, their leading coefficients still multiply to `Λ` and still
evaluate correctly, and `p` divides neither block's leading
coefficient because it divides none of the factors'. V6 does not
survive, because the witness is about the images the lift was given, so
`witnessOf?` is rerun on the two blocks. On success, recurse on the two
factors found; on failure, continue. Subsets are enumerated by
increasing cardinality up to `cfg.recombLevels`, and complements are
not revisited.

At `r = 2` that enumeration is empty: the only two-block grouping is
the splitting that already failed. So a failed lift at `r = 2` means
another point immediately, and the example above is exactly that case.
Recombination earns its budget from `r ≥ 3`.

**The image never hides a factorization, and that is what makes a
subset search the right shape.** If `s = u · w` with both nonconstant
in `x_i`, then neither drops degree at an admissible point, so both
images have positive degree and the image is reducible; and if one of
them is constant in `x_i` it divides `contentIn i cmp' s = 1`. So an
*irreducible* image proves `s` irreducible, which is the `image`
certificate, and with a squarefree image every true factor's
*primitive* image is, up to sign, a subproduct of the `h_j`.

**Being the right shape is not the same as being exhaustive, and the
difference is worth stating precisely.** Three separate conditions have
to hold before "the enumeration found nothing" would mean "there is
nothing":

- the leading-coefficient assignment for the subset has to match the
  true factor's own leading coefficient, which the `need_j` rule forces
  only up to the residual placement of step 4;
- every cardinality has to be enabled, where `cfg.recombLevels` bounds
  them;
- the modulus has to be large enough for the lift of the true grouping
  to reconstruct, which the heuristic schedule does not guarantee.

The search satisfies none of the three by default, which is exactly why
an exhausted recombination is reported as `.recombine` and never as
irreducibility. Irreducibility comes from `IrredCert` and from nowhere
else.

**The cost per candidate is a lift, not a division.** Univariate
Berlekamp-Zassenhaus recombines by trial-dividing a candidate product,
which is cheap. Here each grouping needs its own lift, at
`O(∏_{j ≠ i}(d_j + 1))` univariate solves, because the multivariate
factor corresponding to a grouping is not available until it has been
lifted. This is the single strongest reason the point search prefers
points with few image factors, and it is why `cfg.recombLevels`
defaults to a small number rather than to `r`.

**Bad, unlucky, and fatal.** The vocabulary matches
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md)'s for Brown's algorithm, and the analogy is
exact. A *bad* point is one the admissibility tests reject, before any
work. An *unlucky* point is one whose image splits too finely, and it
is detected only by a failed lift and repaired by recombination. A
point that survives both and still yields nothing means the modulus
schedule ran out, and the response is a new point rather than more
doublings, because a new point is usually cheaper than another doubling
of `l`.

### 8. Normalization and the merge

The factors the lift returns are correct and not yet canonical, and the
gap is easy to miss because `check` looks like it has already settled
everything. `check_sound` gives the product identity, the image at the
point, and the leading coefficient in the *main* variable. It says
nothing about the `cmp`-leading coefficient of the factor as a whole,
which is what D4's `polyNormalize` is about, and the two are different
coefficients: the main-variable leading coefficient is
`lcIn i cmp' g`, a polynomial, while `polyNormalize` looks at the one
monomial that `cmp` ranks highest. A lifted factor can perfectly well
come back with that coefficient negative.

So the last thing the pipeline does, before offering anything to
`checkDecomp`, is:

- normalize every factor with `polyNormalize`, and multiply the `±1`
  units it extracts into `Decomp.content`, which is where D4 requires
  them to end up;
- merge entries that are now equal, adding their multiplicities, which
  is what D5 requires and what makes the multiplicities meaningful;
- sort by multiplicity, so the answer is reproducible across runs and
  comparable across monomial orders.

Each step is linear in the number of factors and none of them can fail.
Leaving any of them out produces a correct product that `checkDecomp`
rejects, which is the good failure mode, but it wastes a whole search.

## Failure cases

```lean
inductive Failure (n : Nat) (cmp : Mono n → Mono n → Ordering)
  | zero
  | point       (attempts : Nat) (last : Option PointReject)
  | lift        (inner : MvHensel.Failure)
  | recombine   (levels : Nat)
  | irreducible (factor : MvPoly n Int cmp)
  | random      (error : RandError)

structure Partial (f : MvPoly n Int cmp) where
  found  : CheckedDecomp f
  reason : Failure n cmp
  rand   : Rand
```

| failure | what it means | who acts |
|---|---|---|
| `.zero` | a complete factorization of `0` was requested | caller: the zero decomposition is available from `factor?` |
| `.point` | no admissible point within `cfg.pointFuel`, with the last rejection recorded when there was one | caller: raise the fuel or the shell bound, and read `last` to learn which admissibility condition was failing |
| `.lift` | hex-mv-hensel refused in a way the retry policy does not handle, `.arity` and `.witnessDegree` in particular | producer bug in this library; these are the constructors a correct caller cannot trigger |
| `.recombine` | groupings up to `cfg.recombLevels` were exhausted | caller: raise the level budget, or accept the decomposition found |
| `.irreducible` | a decomposition was found but no `IrredCert` for the named factor was produced within budget | caller: enable the Kronecker route, or accept the decomposition |
| `.random` | the generator was exhausted | caller: supply a fresh `Rand` |

**There is no separate `.leading` failure.** A leading-coefficient
assignment that cannot be built is a property of the point, it is
already admissibility condition 3, and it is already
`PointReject.leadingSplit`. A second constructor for it would be
unreachable, and the aggregate that a caller actually wants is
"`cfg.pointFuel` points tried, the last one rejected for this reason",
which is what `.point` carries. `last` is an `Option` because
`pointFuel = 0` and an empty shell both give up without having rejected
anything.

**Every failure carries the decomposition found so far.** `Partial`
holds a `CheckedDecomp`, so a caller that runs out of budget keeps the
coarser answer instead of nothing, and can resume with a larger budget.
This is the structure [future-work](../../SPEC/future-work.md) anticipates for
the number-field consumers under `PartialFactorization`, and it is the
reason the public entry point returns `Except (Partial f) _` rather
than `Option`: the distinctions in the middle column are what a caller
dispatches on, and collapsing them to `none` forces it to rediscover
them.

There is no total `factor : MvPoly n Int cmp → Decomp n cmp`. A finite
fuel does not make a partial search total, and [design
principle 8](../../SPEC/design-principles.md) does not admit "the default is
generous" as a classification. The one total form in the library is
`checkDecomp`, which is a decision procedure rather than a search.

## Degenerate inputs

Each of these is a convention that a consumer would otherwise
rediscover as a bug.

- **Zero.** `factor? 0` returns the checked `⟨0, []⟩`, whose product is
  `0`. `complete? 0` reports `.zero`.
- **Units.** `factor? 1` returns `⟨1, []⟩` and `factor? (-1)` returns
  `⟨-1, []⟩`. Both are complete: the factor list is empty and there is
  nothing to certify.
- **Constants.** `factor? (C 12)` returns `⟨12, []⟩`. Complete up to
  the integer content, which is the qualifier every completeness
  statement here carries.
- **Monomials.** `factor? (C 6 * X 0 ^ 2 * X 1)` returns
  `⟨6, [(X 0, 2), (X 1, 1)]⟩`, complete with two `degreeOne`
  certificates and no obligations.
- **Repeated factors.** `g^3 · h` returns `g` with multiplicity `3`,
  from the squarefree decomposition, and never as three separate
  entries; D5 makes the alternative unrepresentable.
- **A factor of `f` that involves no variable of the main one.** It is
  found in `contentIn i cmp' f` one arity down and wrapped in `embed`.
- **Arity zero.** `MvPoly 0 Int cmp` is the constants, and the constant
  case above is the whole answer.
- **Arity one.** The point is the empty tuple, `imageAt` is
  `toUnivariate` composed with the coefficient projection, and the
  `image` certificate's obligation is irreducibility of the input
  itself. The library must agree with `ZPoly.factorize` on these
  inputs, and the conformance suite checks it in Lean rather than
  against the oracle, since both sides are ours.

## Are the hypotheses sufficient?

Collected, because this library's whole job is to supply hypotheses to
theorems proved elsewhere.

1. **Into the lift.** V1 through V6 are discharged by the table in
   step 5. Nothing else is required by `lift`, and `lift_progress` then
   says the only failure that can occur after `valid` is
   `.reconstruct`, which is what makes the retry policy in step 7 a
   policy about points and groupings rather than about the lifting
   code.
2. **Out of the lift.** `check_sound` gives `IsLiftOf`, whose product
   clause is exactly what D1 needs: `reconstruct` has already undone
   the shift, so a certificate's factors are in the coordinates the
   caller handed in and no further translation happens here.
   `lift_unique` is
   unconditional given `valid`, so a grouping that lifts has exactly
   one lift and the recombination search never has to compare two
   answers for the same subset.
3. **Not used.** `lift_complete` and `no_lift_of_reconstruct` are not
   used by the default configuration, because their bound hypotheses
   are not met by the modulus schedule. They are cited only in
   statements about what a failure does *not* mean.
4. **Into `checkIrred`.** `degreeOne` and `embed` need only
   `checkContent_sound`'s maximality clause and the fact that degrees
   add in a domain, both from hex-mv-gcd. `image` additionally needs
   Gauss's lemma on `ZPoly`, which is
   [hex-poly-z](../../HexPolyZ/SPEC/hex-poly-z.md)'s multiplicativity of
   `content` and `primitivePart`, plus the univariate obligation.
   hex-mv-hensel reaches the same fact through hex-mv-gcd's arity-one
   case in `coprimeRat_of_witness`; the two are the same lemma at two
   types, and the image here is a `ZPoly`, so hex-poly-z's is the one
   this library cites. `kronecker` needs unique factorization in `ℤ[z]` for the
   subset argument, and the injectivity of the mixed-radix substitution
   on the monomials of every divisor, which is the same combinatorial
   fact hex-mv-hensel's companion needs for the Kronecker route to its
   coefficient bound. Neither library should prove it twice; it is
   Mathlib-free and belongs in whichever of the two lands first, with
   the other importing it.
5. **Into `checkComplete`.** Product identity plus irreducibility of
   every factor is a complete factorization; no separate completeness
   argument is needed, and in particular the search's own exhaustion is
   never an input to it. Uniqueness of the answer is a companion
   statement, from Mathlib's unique factorization.

Three conclusions the chain does **not** support, each of which an
earlier reading of this design gets wrong.
`irreducible_of_image_irreducible` does not apply to a rescaled image,
so the `image` route proves its own slightly stronger statement. A
failed search is not a refutation at any budget the default
configuration uses. And the completeness qualifier "up to the integer
content" is not removable: `content` is not factored, and a consumer
that needs `C p` as an irreducible factor composes with
hex-int-factor.

## The API

```lean
namespace Hex.MvFactor

variable {n : Nat} {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]

structure Factor (n : Nat) (cmp)
structure Decomp (n : Nat) (cmp)
structure Complete (n : Nat) (cmp)
inductive IrredCert (n : Nat) (cmp)
inductive Failure (n : Nat) (cmp)
inductive PointReject
structure Probe (n : Nat)
    (cmp : Mono (n + 1) → Mono (n + 1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering)
structure Partial (f : MvPoly n Int cmp)

structure CheckedDecomp (f : MvPoly n Int cmp)
structure CheckedComplete (f : MvPoly n Int cmp)

/-- The witness on the other side: a factorization into two nonunits.
Checking it is one multiplication and two unit tests, so reducibility
is as cheaply certified as irreducibility is expensively. -/
structure Split (n : Nat) (cmp) where
  left  : MvPoly n Int cmp
  right : MvPoly n Int cmp

def checkSplit (g : MvPoly n Int cmp) (S : Split n cmp) : Bool

/-- The total decision the Kronecker route supports on a nonconstant
primitive subject. -/
inductive Verdict (n : Nat) (cmp)
  | irreducible (cert : IrredCert n cmp)
  | reducible   (split : Split n cmp)

/-- True when every certificate in `K` avoids the `kronecker`
constructor, which is what makes `checkComplete K` kernel-replayable. -/
def NoKronecker (K : Complete n cmp) : Bool

structure Config where
  rand         : Rand
  pointFuel    : Nat
  pointScouts  : Nat
  pointShell   : Nat
  primeFuel    : Nat
  doublings    : Nat
  recombLevels : Nat
  kronecker    : Bool
  kroneckerDeg : Nat

def Config.default : Config := {
  rand := Rand.ofSeed 0
  pointFuel := 256
  pointScouts := 4
  pointShell := 8
  primeFuel := 16
  doublings := 6
  recombLevels := 3
  kronecker := false
  kroneckerDeg := 4096
}

-- Checkers, and the data they accept
def checkDecomp   (f : MvPoly n Int cmp) (D : Decomp n cmp) : Bool
def checkIrred    (g : MvPoly n Int cmp) (c : IrredCert n cmp) : Bool
def checkComplete (f : MvPoly n Int cmp) (K : Complete n cmp) : Bool
def obligations   (g : MvPoly n Int cmp) (c : IrredCert n cmp) : List ZPoly
def IsDecompOf        (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop
def IsFactorizationOf (f : MvPoly n Int cmp) (D : Decomp n cmp) : Prop

-- Search
def factorWith   (cfg : Config) (f : MvPoly n Int cmp) :
    Except (Partial f) (CheckedDecomp f × Rand)
def factor?      (f : MvPoly n Int cmp) : Except (Partial f) (CheckedDecomp f)
def completeWith (cfg : Config) (f : MvPoly n Int cmp) :
    Except (Partial f) (CheckedComplete f × Rand)
def complete?    (f : MvPoly n Int cmp) : Except (Partial f) (CheckedComplete f)
def irredCert?   (cfg : Config) (g : MvPoly n Int cmp) :
    Except (Failure n cmp) (IrredCert n cmp × Rand)

-- Pieces the conformance drivers exercise directly
def probe (cfg : Config) (i : Fin (n+1)) (cmp') (a : Fin n → Int)
    (s : MvPoly (n+1) Int cmp) (lc : Decomp n cmp') (r : Rand) :
    Except PointReject (Probe n cmp cmp' × Rand)
def distribute?  (i : Fin (n+1)) (cmp') (a : Fin n → Int)
    (lc : Decomp n cmp') (uni : List ZPoly) (scalar : Int) :
    Option (List (MvPoly n Int cmp') × List ZPoly)
def kron    (d : Fin n → Nat) (p : MvPoly n Int cmp) : ZPoly
def unKron? (d : Fin n → Nat) (P : ZPoly) : Option (MvPoly n Int cmp)

/-- The complete route as a decision. Total on a nonconstant primitive
subject, and the only entry point that answers "reducible" with a
witness rather than with an exhausted budget. -/
def kronDecide (g : MvPoly n Int cmp) : Verdict n cmp
```

`probe` takes the leading coefficient's decomposition rather than
computing it, because that decomposition does not depend on the point
and the point loop runs many times. It returns the rescaled images and
the assigned leading coefficients, so the driver above it constructs an
`MvHensel.Input` without recomputing anything, and it returns the
advanced `Rand`.

`factor?` and `complete?` are `factorWith` and `completeWith` at
`Config.default`, discarding the advanced `Rand`, so ordinary use is
deterministic through the fixed default seed and a caller that needs
independent runs threads its own generator. That is hex-mv-gcd's
convention for `gcd` versus `gcdWith`.

`List` rather than `Array` throughout the certificate data, for the
reason hex-mv-poly records under "Kernel exposure": `Array`'s derived
`DecidableEq` stalls `decide`, while `List` equality reduces, and the
factor count is small.

The one statement relating two monomial orders is

```lean
/-- Factoring under a different monomial order returns the same
multiset of factors up to a per-factor sign. `reorder` is
hex-mv-poly's comparator change. -/
theorem factor_reorder {D : Decomp n cmp} {D' : Decomp n cmp₂}
    (hK : IsFactorizationOf f D) (hK' : IsFactorizationOf (reorder f) D') :
    ∃ us : List Int, (∀ u ∈ us, u * u = 1) ∧
      D'.factors.Perm (D.factors.zipWith
        (fun e u => ⟨reorder e.factor * C u, e.multiplicity⟩) us) ∧
      D.content = D'.content *
        (D.factors.zipWith (fun e u => u ^ e.multiplicity) us).prod
```

The content is corrected by the same units, and saying instead that the
two contents are equal would be false. For `f = x - y`, an order with
`x` leading gives content `1` and factor `x - y`; an order with `y`
leading sees leading coefficient `-1`, normalizes the factor to
`y - x`, and must carry `-1` in the content to keep the product. The
units appear with the multiplicities because a factor of even
multiplicity contributes none.

The statement is about *complete* answers, because that is where
uniqueness makes the pairing canonical; two checked decompositions of
the same subject need not correspond at all.

## Complexity

These are **probe counts** in the sense
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) and [hex-mv-hensel](../../HexMvHensel/SPEC/hex-mv-hensel.md) use:
they count evaluations, univariate factorizations, lifts, and
divisions, and they omit the cost of each probe. Multiplying through
would need a cost model for arithmetic modulo `q` at `l` words, which
depends on the modulus schedule and is not modelled here.

Parameters: `v = n` variables, `d₁` the degree in the main variable,
`d_j` the degrees in the others, `t` terms in the input, `r` univariate
image factors, `M` the maximum multiplicity, and `w` the number of
pieces in the decomposition of `lcIn i cmp' f`.

| operation | algorithm | probe count |
|---|---|---|
| structural reductions | monomial gcd fold, scalar content fold | `O(v · t)` machine operations |
| `sqfDecomp` | hex-mv-gcd, Yun with content recursion | `O(v · M)` multivariate gcds |
| one point test | one evaluation and one `ZPoly` gcd | `O(t · v)` coefficient operations plus one univariate gcd |
| point search | shells until admissible, then scouting | `≤ pointFuel` point tests |
| univariate factorization | `ZPoly.factorize` at degree `d₁` | one call per admissible point, so up to `pointScouts` of them |
| leading-coefficient decomposition | recursive entry at arity `n`, hoisted out of the point loop | one factorization in `v - 1` variables per main variable |
| distribution | gcd-stripping non-divisor test, then division by the evaluated factors | `O(w²)` integer gcds plus `O(r · w)` exact divisions, and no integer factorization |
| one lift attempt | hex-mv-hensel `liftWith` | `O(∏_{j ≠ i} (d_j + 1))` univariate solves per doubling |
| recombination | one lift per grouping | `Σ_{k ≤ recombLevels} C(r, k)` lift attempts |
| `checkDecomp` | powers by square-and-multiply, then one product | `O(r + Σ_k log e_k)` multiplications, `r` of them for the product itself |
| `checkIrred` `image` | one evaluation, one content replay | `O(t)` coefficient operations plus the `ContentCert` replay |
| `kronDecide` producer | one `ZPoly.factorize` at degree `∏_j (d_j + 1) - 1`, then the sweep | one univariate factorization at dense-size degree, plus the sweep below |
| `checkIrred` `kronecker` | substitution, one product identity in `ZPoly`, subset sweep | `∏_k (e_k + 1)` multivariate `divExact?` calls, each preceded by one `unKron?` |
| `kron`, `unKron?` | exponent rewriting in mixed radix | `O(v · t)` machine operations |

The table carries the design argument twice. The accepted answer costs
`O(r + Σ log e_k)` multiplications to check regardless of how it was found,
which is what makes replay affordable and is why every claim is
attached to a checker. And the two irreducibility routes are separated
by an enormous constant, which is why the search tries the `image`
route on several points before enabling `kronecker` at all.

## Kernel exposure

The kernel replay closure is `checkDecomp`, `checkComplete`, and
`checkIrred` restricted to `degreeOne`, `image`, and `embed`, together
with what those call: `MvPoly` multiplication, powering, and equality,
`imageAt`, `lcIn`, `toUnivariate`, `constIn`, `MvPoly.eval`,
`polyNormalize`, `scalarContent`, hex-mv-gcd's `checkContent`,
`DensePoly` content, primitive part, degree and equality, and `List`
length and indexing. Each is `@[expose]`.

Nothing in the pipeline is in that closure: point search, prime search,
`witnessOf?`, the lift, and the recombination enumeration are search
and never appear in a proof term. `Config`, `Failure`, `Partial`, and
`PointReject` are likewise outside.

`checkIrred` on `kronecker` is **deliberately outside** the closure.
Its sweep runs `∏_k (e_k + 1)` exact divisions on polynomials of dense
size, and `divExact?` is one of the operations hex-mv-gcd explicitly
keeps out of its own closure.

**The restriction has to be visible in the data, not only in the
prose.** `checkComplete` dispatches on whichever constructors its
argument happens to carry, so "the closure is `checkComplete` minus
`kronecker`" is not a statement about a function; it is a statement
about the data it is applied to. `NoKronecker K` is the decidable
predicate that says so, and the kernel claim is: for `K` with
`NoKronecker K = true`, `checkComplete f K` replays in the kernel at
the cost the complexity table gives. `cfg.kroneckerDeg` bounds the
*producer* and says nothing about a certificate a caller constructs, so
it cannot carry this guarantee.

`checkSplit` is in the closure: one multiplication and two unit tests
is the cheapest thing in this library.

One thing the closure does *not* contain is a discharge of the
obligations. A replayed `checkIrred` establishes the implication, not
the conclusion; the univariate facts come from the companion. A kernel
proof of irreducibility is therefore a kernel replay of `checkIrred`
plus a companion-side proof of each obligation, and this SPEC does not
claim it is one artefact.

## Conformance

Fixtures follow [SPEC/testing.md](../../SPEC/testing.md). A Lean driver at
`conformance/HexMvFactor/EmitFixtures.lean` exposed as
`lean_exe hexmvfactor_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexMvFactor/mvfactor.jsonl`, and an oracle driver
at `scripts/oracle/mvfactor_sympy.py`. One tuple appended to `ORACLES`
in `scripts/ci/run_oracles.sh`, not a new job, per
[SPEC/CI.md](../../SPEC/CI.md):

```
"HexMvFactor|hexmvfactor_emit_fixtures|scripts/oracle/mvfactor_sympy.py|conformance-fixtures/HexMvFactor/mvfactor.jsonl"
```

Three fixture kinds. `mvfactor` carries the arity, the comparator name,
and the subject's term list, and its result records the content and the
`(factor, multiplicity)` list. `mvirred` carries one term list and
records the Boolean irreducibility decision together with the
certificate constructor that produced it. `mvpoint` carries a subject,
a main variable, and a point, and records the `PointReject` verdict or
the resulting images and leading coefficients. All three reuse the
`(exponent vector, coefficient)` encoding hex-mv-poly's `mvpoly`
fixture kind defines, so one parser serves them, hex-mv-gcd's three
kinds, and hex-mv-hensel's two.

**The oracle suite alone cannot catch the bugs this library is most
likely to have**, for the reason [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) gives
about its own routes. Every answer goes through `checkDecomp`, and a
rejected candidate falls through to another point or another grouping,
so an end-to-end fixture passes even when the non-divisor
assignment never fires, when the point scouting always keeps the first
point, or when recombination is dead code. The suite therefore has two
halves.

**Route-level tests**, in Lean, invoking the pieces directly and
asserting on internals: that a constructed degree-dropping point was
rejected with `.degreeDrop` and a non-squarefree one with
`.notSquarefree`; that `distribute?` returns the assignment forced by
the non-divisor condition on a case built to satisfy it, and `none` on
a case built not to; that the rescaled images satisfy V3 and V4
exactly, checked by calling `MvHensel.valid`; that an unlucky point
reaches recombination and that the two-block grouping that succeeds is
the one predicted; that the `image` certificate fires before
`kronecker` is ever consulted; and that `checkIrred` rejects a
certificate whose content certificate has been corrupted in one field.
These are the tests that fail when a route regresses.

**Oracle fixtures**, which check the public answer. Cases that must be
present:

- `0`, `1`, `-1`, `6`, `12x`, `x²y³`, and `6x²y`: the whole structural
  path, including the conventions for content and monomial content.
- Irreducible inputs in 2 to 5 variables with constant, monomial, and
  nonconstant leading coefficients in the main variable.
- Repeated factors: `g³ · h`, `g² · h⁵`, and a case whose repeated
  factor lives entirely in `contentIn i cmp' f`.
- Nonconstant `L_j` sharing a common factor, which is the case Wang's
  assignment exists for and the case a lift that quietly renormalises
  leading coefficients gets wrong.
- A leading coefficient failing the non-divisor condition at the first
  admissible point, so the `.leadingSplit` rejection and the move to
  another point are both exercised.
- A leading coefficient whose integer part must be split between two
  factors, `(2y·x + 1)(3x + y)` being the smallest, so that a
  distribution which dumps the content into one `L_j` is caught. Its
  ambiguous sibling, where two placements satisfy every constraint and
  only one lifts, is present as well.
- The unlucky point `x₁² + x₂` at `x₂ = -1`: the image splits into
  `(x₁ - 1)(x₁ + 1)` while `f` is irreducible, so the lift reaches full
  precision and fails. With `r = 2` there is no coarser two-block
  grouping to try, so the search moves to another point and the answer
  arrives through an `image` certificate. The fixture records both the
  failed point and the successful one.
- The same shape with `r = 4` at an unlucky point, where a coarser
  grouping does exist and is the one that lifts.
- A point whose image is non-squarefree, rejected before any lifting.
- A prime dividing the resultant of two images, where the same input
  succeeds at the next prime, distinguishing the two causes of
  `.notCoprime`.
- An input whose true factors have coefficients larger than the
  starting modulus allows, so reconstruction fails once and succeeds
  after a doubling.
- A factorization requiring recombination at cardinality 2 and one at
  cardinality 3, so that `recombLevels` is exercised at its default and
  one above it.
- The same input factored at two different monomial orders, checking
  that the factor sets agree up to the sign unit of `factor_reorder`.
- An input for which `kronecker` is the only available certificate,
  small enough that the sweep terminates, checking that the decision
  agrees with the `image` route on an input where both apply.
- Arity one, where the answer must agree with `ZPoly.factorize`,
  checked in Lean rather than against the oracle since both sides are
  ours.
- A sparse input whose lift intermediates are dense, recording the
  known gap while no sparse route is specified.

**Oracle choice.** SymPy is the oracle. `sympy.factor_list` covers the
public answer over `ℤ` including the content convention, which is the
same convention this library uses. The comparison is nevertheless up to
a per-factor sign and a permutation: SymPy normalizes signs by its own
generator order, while this library normalizes by the `cmp` under test,
and `factor_reorder` is the statement that the two differ by units. The
driver therefore compares the factor multisets after normalizing the
oracle's output under the tested comparator, and compares the contents
after the same correction. For the route-level halves that a public answer cannot
see, `sympy.polys.factortools` exposes the matching internals:
`dmp_zz_wang_test_points` for point admissibility,
`dmp_zz_wang_non_divisors` for the non-divisor test,
`dmp_zz_wang_lead_coeffs` for the assignment and the rescaling, and
`dmp_zz_wang` for the whole EEZ driver. Comparing those directly is
what catches an inverted divisibility test or an off-by-one in the
assignment, which an end-to-end fixture cannot: a wrong assignment
usually makes the lift fail loudly and the search recover at the next
point, producing a correct public answer from a broken route.

Those are internal SymPy names rather than public API, so the driver
tests one known case per name at startup and fails with a clear message
if a name has moved, rather than reporting a skip. That is the policy
hex-mv-hensel's driver uses for the same module, and the
`HEX_REQUIRE_ORACLES=1` preflight applies to the SymPy dependency
itself.

Irreducibility is compared through `factor_list` rather than through
`Poly.is_irreducible`: the list form is defined for every arity and
every domain the fixtures use, and for a *nonconstant* subject
"irreducible" is then "one factor, multiplicity one, unit content",
which is exactly this library's `Complete` with a singleton factor
list. Constants are not covered by that reading, since `C 2` is
irreducible with an empty factor list and a nonunit content; the
`mvirred` fixtures record the constant cases as the companion decides
them, against `sympy.isprime` on the content, and the Mathlib-free
`kronDecide` declines them by its `¬ IsConst` precondition.

The companion adds randomised comparison against
`MvPolynomial (Fin n) ℤ` through hex-mv-poly's `equiv`, checking
`IsFactorizationOf` and `Irreducible` directly rather than through
SymPy's normalisation conventions.

## Benchmarking

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), with drivers at
`bench/HexMvFactor/Bench.lean`. Native only for throughput. A separate
`bench/HexMvFactor/Kernel.lean` suite replays valid and
one-field-corrupted data through `by decide +kernel`: a decomposition
with three factors and mixed multiplicities, a `degreeOne` certificate,
an `image` certificate, an `embed` certificate, and a decomposition
whose product identity is off by one coefficient.

Families, chosen to isolate the costs the complexity table separates:

- **Dense EEZ**, 2 to 4 variables, degree 4 to 12 in each, two or three
  irreducible factors, constant leading coefficient. The end-to-end
  family, and the one the required external comparator is scoped to.
- **Nonconstant leading coefficients**, the same shapes where
  `lcIn i cmp' f` has several irreducible factors. Isolates the
  recursive factorization of the leading coefficient and the
  assignment.
- **Factor count**, `r` from 2 to 8 at fixed degrees, which drives the
  recombination search.
- **Recombination stress**, inputs whose image splits into many more
  pieces than `f` does, so that the measured cost is lifts per accepted
  factor.
- **Point difficulty**, inputs whose small points mostly drop the
  degree or give non-squarefree images, measuring the point search
  rather than the lift.
- **Coefficient size**, the same shapes with coefficients large enough
  to force several doublings. Times should grow with `l²` and not
  faster.
- **Main-variable choice**, the same input presented so that the two
  candidate rules disagree, which is what turns the heuristic in step 2
  into a measurement.
- **Irreducible inputs**, where the answer is a single factor and the
  whole cost is certificate production, run with `kronecker` disabled
  and enabled so that the gap between the two routes is on record.
- **Sparse targets**, sparse `f` with dense lift intermediates. This
  records the known gap while no sparse route is specified; it does not
  claim to isolate a route.

**Comparators.** FLINT's `fmpz_mpoly_factor` is `gating`, scoped to the
**dense EEZ** bench target, with the goal that this library solve every
rung the comparator solves under the declared cap and stay within a
stated constant of it there. That is the required ratio
[hex-mv-hensel](../../HexMvHensel/SPEC/hex-mv-hensel.md) defers to this library, on the one
family where the two implementations are doing the same work. On every
other family FLINT is `informational`: its sparse Hensel lifting and
Zippel interpolation have no counterpart here while hex-mv-hensel
specifies only the dense diophantine recursion, so a ratio there would
be a check on routes that do not exist, which is the same position
hex-mv-gcd takes for `fmpz_mpoly_gcd`. Singular's `factorize` is
`informational` for the same reason. SymPy is the oracle and is not a
performance comparator: `dmp_zz_wang` is Python, so a favourable ratio
would measure the language and not the algorithm.

## The Mathlib layer

`hex-mv-factor-mathlib` does four things the Mathlib-free layer
cannot: it discharges the univariate obligations, it identifies the
checked statements with Mathlib's, it proves uniqueness, and it provides
the proof-producing multivariate tactic surface. Writing
`e` for hex-mv-poly's
`equiv : MvPoly n Int cmp ≃+* MvPolynomial (Fin n) ℤ` and `eZ` for
hex-poly-mathlib's `equiv : DensePoly Int ≃+* Polynomial ℤ`:

```lean
/-- Every obligation a produced certificate leaves is discharged by the
univariate factorizer's own irreducibility theorem. -/
theorem obligations_irred (h : irredCert? cfg g = .ok (c, r)) :
    ∀ F ∈ obligations g c, MvHensel.Irred F

theorem irred_iff (p : MvPoly n Int cmp) :
    MvHensel.Irred p ↔ Irreducible (e p)

theorem checkIrred_irreducible (h : checkIrred g c = true)
    (ho : ∀ F ∈ obligations g c, Irreducible (eZ F)) :
    Irreducible (e g)

/-- The transported factorization statement. It takes the same
obligation hypothesis `checkComplete_sound` does, because
`checkComplete` does not establish it. -/
theorem factorization_spec (h : checkComplete f K = true)
    (ho : ∀ e ∈ K.decomp.factors.zip K.certs,
            ∀ F ∈ obligations e.1.factor e.2, Irreducible (eZ F)) : …
    -- e f = C K.decomp.content * ∏ (e factor) ^ multiplicity,
    -- with every factor irreducible and pairwise non-associated

/-- The form a caller normally wants: provenance discharges the
obligations through `obligations_irred`, so there is nothing left to
supply. -/
theorem factorization_spec_of_complete
    (h : completeWith cfg f = .ok (K, r)) : …

theorem factorization_unique : …
    -- against UniqueFactorizationMonoid (MvPolynomial (Fin n) ℤ)

theorem checkSplit_not_irreducible (h : checkSplit g S = true) :
    ¬ Irreducible (e g)

instance : DecidablePred (Irreducible : MvPolynomial (Fin n) ℤ → Prop)
```

`irred_iff` is not reproved here: hex-mv-hensel's companion already
identifies `Irred` with `Irreducible`, and this library imports it.

`obligations_irred` is the theorem that makes the whole obligation
design pay off. Every obligation a *produced* certificate carries is a
polynomial that `ZPoly.factorize` returned, so
`hex-berlekamp-zassenhaus-mathlib`'s irreducibility theorem applies
directly. A certificate assembled by a caller from other data gets the
weaker `checkIrred_irreducible`, where the caller supplies the
obligations.

**`factorization_spec` may not drop that hypothesis, and the tempting
version of it is false.** A `checkComplete`-only statement concluding
irreducibility would let a caller hand in the singleton decomposition
of `x² - 1` with an `image` certificate at any point where the degree
does not drop: the product identity holds, the content certificate
checks, and the single obligation is the *reducible* polynomial
`x² - 1`, which nobody ever verified. The obligation hypothesis, or
provenance through `completeWith`, is exactly what rules that out. This
is the one place in this SPEC where dropping a hypothesis would turn a
product check into an irreducibility claim.

The `Decidable` instance is assembled from three cases, and each needs
saying, because a decision procedure has to answer on every input and
`IrredCert` alone answers on none of the negative ones.

- **Zero and units.** `0` and `± 1` are not irreducible, decided
  outright.
- **Other constants.** `C p` is irreducible exactly when `p` is prime
  in `ℤ`, which Mathlib decides. This is the case no `IrredCert`
  constructor covers, by the content convention, and it is why the
  instance lives in the companion rather than in the Mathlib-free
  layer.
- **Nonconstant.** Take the primitive part, run `kronDecide`, and use
  `kronDecide_irreducible` or `kronDecide_reducible` accordingly. A
  nonunit content makes the input reducible and supplies its own split.
  `kronDecide` is total because `ZPoly.factorize` is total, `unKron?`
  and exact division are total, and the sweep is finite.

The executable path tries `irredCert?` at the default configuration
first, so it is fast on the inputs where the `image` route fires and
merely finite elsewhere. This is the multivariate counterpart of
`hex-berlekamp-zassenhaus-mathlib`'s `Decidable (Irreducible f)` for
`Polynomial ℤ`.

**What the instance is and is not for.** It makes `Irreducible p`
decidable, so a Mathlib development can case on it and a tactic can
call it at elaboration time. It is *not* a recommendation to discharge
such a goal with `decide`, which reduces the whole search in the
kernel: the search is a search, and this SPEC keeps it out of the
kernel closure on purpose. The route for a proof term is
`checkIrred_irreducible` on a produced certificate, whose replay is one
evaluation and one content check for the `image` constructor. Saying
which of the two a consumer wants is the point of having both.

### Multivariate `factor_poly` and `irreducibility`

The ordinary `HexMvFactorMathlib` umbrella registers
`HexMvFactorMathlib.FactorTactic.extension` for closed executable
`MvPoly n Int cmp` values, structurally reifiable
`MvPolynomial (Fin n) ℤ` expressions, and open commutative-ring expressions.
It is found through `Hex.FactorTactic.extensionNames`; its generic expression
arm is last within the extension, and the extension itself is last in global
dispatch order, so it cannot capture a more specific univariate or
multivariate polynomial representation.

For the two actual polynomial representations, the tactics have the same
meaning as their univariate counterparts:

- `factor_poly p` returns a scalar, normalized irreducible factors with
  multiplicities, their product identity, and irreducibility proofs in the
  input polynomial ring;
- `irreducibility p` proves `MvHensel.Irred p` for an `MvPoly` input and
  Mathlib's `Irreducible p` for an `MvPolynomial` input; and
- a search decline produces a diagnostic and no proof. The factor search and
  certificate construction run as untrusted elaborator code, while the
  emitted term contains only literal data, checker replays, obligation
  discharge, and representation/evaluation lemmas.

The expression arm exists for uses such as

```lean
factor_poly 1 + x + y + x * y
```

where `x` and `y` are local values in a commutative ring rather than fields of
an already constructed polynomial value. It recognizes integer constants,
`0`, `1`, addition, subtraction, multiplication, negation, and powers by
literal natural exponents. Every maximal unrecognized ring-valued
subexpression is an atom. Definitionally equal atoms share one index, and new
atoms receive indices in deterministic left-to-right first-occurrence order;
the example therefore reifies to
`1 + X 0 + X 1 + X 0 * X 1` with the atom table `#[x, y]`. The internal
representation uses `MvPoly n Int Mono.grevlex`.

The reifier does **not** zeta-reduce a local `let` before the atom fallback.
The expression supplied by the user is the abstraction boundary: in

```lean
let p := 1 + x + y + x * y
factor_poly p
```

`p` is one atom, so the formal input is `X 0` with atom table `#[p]` and its
formal factorization is the single factor `X 0`. This is intentionally not the
factorization of `p`'s assigned value. A caller who wants the latter supplies
the expanded expression. Operation-head normalization may expose the declared
ring operations, but it must not unfold a local definition merely to discover
more polynomial structure.

The result records the formal polynomial and its interpretation, not a false
claim about the ambient ring. Its public contract has this shape (field names
and projections are part of the API even if the constructor is assembled by
a helper theorem):

```lean
structure FactoredExpr {R : Type u} [CommRing R] (subject : R) where
  n             : Nat
  atoms         : Fin n → R
  input         : MvPoly n Int Mono.grevlex
  decomp        : MvFactor.Decomp n Mono.grevlex
  reified       : MvPoly.eval₂ (fun z => (z : R)) atoms input = subject
  formal_mul    : decomp.product = input
  factors_mul   :
    MvPoly.eval₂ (fun z => (z : R)) atoms decomp.product = subject
  factors_irred :
    ∀ q ∈ decomp.factors, MvHensel.Irred q.factor
```

Thus the example exposes formal factors `1 + X 0` and `1 + X 1`, proves
their formal irreducibility, and proves that their denotations multiply to the
original expression, hence `(1 + x) * (1 + y) = 1 + x + y + x * y` in the
ambient ring. Zero and constant inputs use the scalar/empty-factor convention;
they do not manufacture an `IsFactorizationOf 0` witness.

Formal irreducibility must not be transported through the atom substitution.
That implication is false: the formally irreducible polynomial `1 + X 0`
becomes the unit `1` when its atom is interpreted as `0`. Consequently the
generic expression arm of `factor_poly` exposes only
`MvHensel.Irred q.factor`, never `Irreducible` of the denoted ambient value,
and the generic arm of `irreducibility` must decline with a diagnostic that
explains this distinction. Ambient irreducibility is available only on the
direct `MvPoly` and `MvPolynomial (Fin n) ℤ` paths, where the correspondence
is a ring equivalence rather than an arbitrary evaluation homomorphism.

The existing shared front end currently rejects free variables before it
offers an input to extensions and parses only `term:max`. It is amended so
that:

- open inputs reach the generic multivariate extension, while the existing
  executable-literal extensions retain their own closed-input checks;
- both term and tactic forms accept an unparenthesized compound argument, so
  the exact example above parses as one `factor_poly` invocation; and
- the tactic form introduces the atom table, scalar/decomposition data,
  `factors_mul`, and formal `factors_irred` hypotheses. Existing univariate
  result shapes and introduction names remain compatible.

The hand-written expression reifier is temporary and isolated in
`HexMvFactorMathlib/Reify.lean`. Its module documentation must contain this
warning prominently and verbatim in substance:

> **WARNING: TEMPORARY REIFIER — REPLACE, DO NOT GROW.** This entire parser
> must be replaced by Lean 4's built-in `Lean.Meta.Sym.Arith` reification once
> that API is ready for this proof-producing use. Do not add consumers of its
> internal syntax tree or duplicate its recursion elsewhere.

The reifier exposes only the atom table, the `MvPoly` literal, and the proof
of its evaluation equation. Its regression tests specify the supported
syntax and atom-order contract, so replacing the implementation wholesale
does not change tactic behavior.

Required tactic regressions cover:

- the exact unparenthesized `1 + x + y + x * y` example, including the two
  deduplicated atoms and the denoted product identity;
- the same expression behind `let p := ...`, where `factor_poly p` preserves
  the abstraction boundary and produces exactly the single atom `#[p]`;
- repeated and compound atoms, subtraction, negation, and literal powers;
- closed `MvPoly` and structural `MvPolynomial (Fin n) ℤ` factorization and
  irreducibility;
- a negative generic-`irreducibility` case whose diagnostic names the
  substitution soundness boundary;
- extension discovery and precedence over the generic expression fallback;
- preservation of every existing univariate tactic regression; and
- inspection of emitted declarations showing that factor search, point
  search, lifting, and certificate generation do not occur in proof terms.

The ordinary forms are required here. Extending the `factor_poly!` and
`irreducibility!` kernel-evaluation fallbacks is not: multivariate search is
deliberately outside the kernel closure, and those forms may be added only
with a separate replay budget and SPEC amendment.

`factorization_unique` uses `MvPolynomial.uniqueFactorizationMonoid`.
Uniqueness is genuinely a companion statement: the Mathlib-free layer
proves that its answer *is* a factorization into irreducibles, and that
any two such agree up to units and order is unique-factorization
theory, not certificate replay.

Following the project split, no other mathematical theorem about
`MvPoly` belongs here, plus one correspondence lemma per public
semantic operation: `checkDecomp`, `checkIrred`, `factor?`,
`complete?`, and `kron`.

## Milestones

1. **The answer type and its checker.** `Factor`, `Decomp`,
   `Decomp.product`, `checkDecomp`, `IsDecompOf`, `CheckedDecomp`,
   `checkDecomp_sound`, and the structural reductions of step 0. This
   milestone touches no lifting concept and can be built against
   hex-mv-poly and hex-mv-gcd alone.

2. **Irreducibility certificates without search.** `IrredCert`,
   `checkIrred`, `obligations`, `checkIrred_sound` for `degreeOne`,
   `image`, and `embed`, `Split` with `checkSplit`, `Complete`,
   `checkComplete`, `NoKronecker`, and `IsFactorizationOf`. The `image`
   soundness proof, with its Gauss step, is the substantial piece.

3. **The point and leading-coefficient layer.** `probe`, `Probe`,
   `PointReject`, the shell enumeration, `distribute?` with its
   non-divisor test and `need_j` allocation, the rescaling,
   and the route-level tests that check V1 to V6 by calling
   `MvHensel.valid` on the constructed `Input`. Written before the
   driver, because they are what the driver's failures are diagnosed
   against.

4. **The EEZ driver.** `Config`, `Failure`, `Partial`, the squarefree
   and content recursion, prime selection, the modulus schedule, the
   lift call, recombination, the normalization and merge pass, and
   `factorWith` / `factor?`. This is the first usable release: it
   returns checked decompositions and, through milestone 2,
   certificates whenever the `image` route fires.

5. **The complete route.** `kron`, `unKron?`, the `kronecker`
   constructor and its soundness, `Verdict` and `kronDecide` with both
   of its theorems, `irredCert?`'s fallback, and
   `completeWith` / `complete?`.

6. **Conformance and benchmarks.** The three fixture kinds, the SymPy
   driver with its internal-name preflight, the kernel replay suite,
   and the nine benchmark families.

7. **The companion.** `obligations_irred`, the transported statements,
   uniqueness, and the `Decidable` instance. It can begin after
   milestone 4; the instance needs milestone 5.

8. **The tactic surface.** The direct `MvPoly` and `MvPolynomial` extensions,
   `FactoredExpr`, the isolated atom reifier, the shared-front-end amendments,
   registration, emitted-term audit, and tactic regressions. It needs
   milestone 7's obligation discharge and irreducibility transport; the
   reifier and result type can be developed independently once the
   `MvPoly.eval₂` API is available.

## File organisation

```
HexMvFactor/
  Decomp.lean     -- Factor, Decomp, checkDecomp, soundness, structural reductions
  IrredData.lean  -- IrredCert, Split, Complete, and Verdict shared data
  Irred.lean      -- checkIrred, obligations, checkSplit, Complete replay, soundness
  Point.lean      -- Config, probe, Probe, PointReject, the shell enumeration
  Leading.lean    -- lc factorization, distribute?, the rescaling to V3 and V4
  Input.lean      -- building MvHensel.Input, prime selection, the modulus schedule
  Eez.lean        -- the per-squarefree driver, retries, recombination, normalization
  Kronecker.lean  -- kron, unKron?, kronDecide, the complete route
  Factor.lean     -- the top-level recursion and public API
HexMvFactor.lean
HexMvFactorMathlib/
  Correspondence.lean -- transport of checkDecomp and checkIrred
  Irreducible.lean    -- obligation discharge, irreducibility, the Decidable instance
  Unique.lean         -- uniqueness against UniqueFactorizationMonoid
  FactoredExpr.lean   -- certified result for an atom-reified ring expression
  Reify.lean          -- temporary parser-with-proof; replace by Lean.Meta.Sym.Arith
  FactorTactic.lean   -- MvPoly, MvPolynomial, and expression tactic extension
  FactorTacticTests.lean -- syntax, dispatch, soundness-boundary, and replay tests
HexMvFactorMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexMvFactor:
    deps: [HexBasic, HexMvPoly, HexMvGcd, HexMvHensel, HexPoly, HexPolyZ, HexPolyZGcd, HexBerlekampZassenhaus, HexPolyFp, HexModArith, HexModular, HexArith]
    mathlib: false
    done_through: 1
    status: active
    phase4:
      comparators:
        - tool: "FLINT fmpz_mpoly_factor (dense EEZ bench target)"
          class: gating
          goal: "Solve every rung of the dense EEZ family that the comparator solves under the declared cap, and stay within a stated constant of it there. Scoped to that bench target; on the sparse, recombination-stress, and irreducible-input families the same tool is informational, because FLINT's sparse Hensel and Zippel routes have no counterpart in the dense diophantine recursion hex-mv-hensel specifies."
        - tool: "Singular factorize"
          class: informational
          rationale: "A second mature EEZ implementation with different route selection and its own crossovers, useful as orientation on every family and not as a yardstick for any single one."
  HexMvFactorMathlib:
    deps: [HexMvFactor, HexMvHenselMathlib, HexMvGcdMathlib, HexMvPolyMathlib, HexBerlekampZassenhausMathlib, HexPolyZMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexMvHensel` supplies the lift, `Irred`, and the failure vocabulary.
`HexMvGcd` supplies exact division, content and primitive part in a
named variable, `monoContent`, `scalarContent`, `polyNormalize`,
squarefree decomposition, and `ContentCert` with its checker.
`HexBerlekampZassenhaus` supplies `ZPoly.factorize`. `HexPolyZGcd`
supplies the univariate integer gcd behind the squarefree-image test.
`HexPolyZ` supplies `ZPoly` and its content and primitive part.
`HexPolyFp`, `HexModArith`, and `HexModular` come in through the prime
supply and the symmetric representatives, and `HexArith` through the
integer gcd behind the non-divisor test. `HexPoly` comes in
through `DensePoly`.

The computational dependency chain through `HexModular`, `HexPolyZGcd`,
`HexMvGcd`, and `HexMvHensel` is active and registered in `libraries.yml`.
The Mathlib companion remains planned: it starts only after the
Mathlib-facing bridge libraries in its dependency list are available.

`HexIntFactor` is deliberately absent; "The two claims" gives the
reason and "Open questions" records the flag that would add it.

## Why the search and the checkers are one library

The checkers have no consumer other than this library's own search and
the companion's transport, their dependency set is identical, and
`Decomp.lean` plus `Irred.lean` is a few hundred lines. Splitting them
out would produce a library with two decision procedures, the same
dependencies, and a second round of release plumbing.

The seam, if one appears, is the one hex-mv-gcd has: `Decomp.lean` and
`Irred.lean` carry the verification path and no search, while
`Point.lean`, `Leading.lean`, `Eez.lean`, and `Kronecker.lean` carry
search and no soundness proofs. A sparse lifting route would replace
`Eez.lean`'s call into hex-mv-hensel and leave the first pair
untouched.

## Open questions

- **Whether hex-mv-hensel should state the scaled form of
  `irreducible_of_image_irreducible`.** Its hypothesis is
  irreducibility of the image as the lift received it, and the images
  this library supplies carry Wang's correction scale, so the theorem
  does not apply and this library proves the scaled statement itself.
  One amendment there would let both libraries share it. It waits until
  a second consumer wants it, which is the same policy hex-mv-hensel
  applies to hex-hensel's partial-fraction tuple.
- **Whether a failed lift should become a refutation constructor.** It
  becomes worth having once hex-mv-hensel's companion proves the Mahler
  length form of the coefficient bound rather than the Kronecker
  reduction to Mignotte, because only then is the conclusive modulus
  reachable. It would still need a complete factorization of
  `lcIn i cmp' g` to enumerate admissible distributions, so the
  amendment is not small.
- **Whether the integer placements should be enumerated.** The greedy
  gcd pass picks one splitting of `Λ`'s integer content among the
  factors, and when two placements satisfy every constraint a wrong
  pick costs a whole point. Enumerating them is finite and usually
  tiny, and it trades a cheap loop for a lift attempt each. No
  measurement exists yet, and the "nonconstant leading coefficients"
  family is where one would come from.
- **Whether monicisation is worth a second route.** Replacing the
  target by `Λ^(d₁ - 1) · f(x_i / Λ)` makes every factor monic in the
  main variable and removes the distribution search and its failure
  mode entirely, at the cost of coefficient and degree growth that the
  lift pays for. The "nonconstant leading coefficients" and
  "point difficulty" families are what would settle it.
- **Whether the content should be factored behind a flag.** Composing
  with hex-int-factor at the call site is three lines and keeps this
  library free of a dependency it otherwise does not need, but every
  consumer that wants the ring-theoretic factorization writes those
  three lines. If a third one appears, the flag is cheaper than the
  repetition.
- **Which sparse route merits an amendment.** Shared with
  [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) and
  [hex-mv-hensel](../../HexMvHensel/SPEC/hex-mv-hensel.md), whose open questions of the same
  name should be decided together. The dense diophantine recursion is
  the dominant cost of this library on sparse inputs, and the
  "sparse targets" family measures it in the meantime.
- **Whether factorization over `ℚ` and over `F_q` are entry points or
  libraries.** Over `ℚ` it is clearing denominators and calling this
  library, which is a wrapper. Over `F_q` the lifting engine itself
  changes, since the modulus and reconstruction disappear, so it is a
  different library that reuses only the recombination and certificate
  shapes. hex-mv-hensel has the matching open question about its own
  field case, and the two answers should agree.
