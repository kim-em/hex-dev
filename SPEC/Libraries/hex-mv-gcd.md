# hex-mv-gcd (multivariate gcd and squarefree decomposition, depends on hex-mv-poly)

Greatest common divisors, cofactors, content, primitive part, exact
division, and squarefree decomposition for `MvPoly n R cmp`. Mathlib-free.
The companion `hex-mv-gcd-mathlib` transports the Mathlib-free soundness
theorems onto `MvPolynomial (Fin n) R`, proves the squarefree
correspondence, and supplies the decidability instances that make the
operations usable from a Mathlib goal.

This SPEC expands the "Multivariate gcd and squarefree decomposition"
entry in [future-work](../future-work.md) and depends on the representation
fixed by [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md). The coprimality
certificate inherited from the modular-gcd item does not generalise as
written; "The certificate" gives the complete replacement. The algorithms
use hex-mv-poly's landed arity-dropping recursive view, so termination is
structural and no parallel arity-preserving API is introduced.

## Why this library exists

**Rational expression simplification.** `cancel`, the second of the three
pieces of the `Together` / `Apart` item in
[future-work](../future-work.md), reduces `p / q` to lowest terms. That
is a multivariate gcd plus its cofactors, and nothing else. It is the
consumer with the highest call volume, and it is dominated by the case
`gcd = 1`, which is why coprime detection gets its own fast path below
rather than falling out of the general algorithm.

**Multivariate factorization.** Wang's EEZ algorithm begins by
squarefree-decomposing the input and splitting off the content in the
main variable, and calls gcd throughout leading-coefficient correction.
Squarefree decomposition is the reason that algorithm may assume its
input has no repeated factors, which is what makes the Hensel lifting
step well posed.

**`MvPoly n R cmp` as a coefficient ring for hex-resultant.**
hex-resultant's subresultant chain is written against `[Div R]` with
`ExactDivLaws R`, and it already has a recursive instance tower for
`DensePoly R`. Giving `MvPoly n R cmp` the same instances runs the chain
over multivariate coefficients, which is what multivariate resultants,
elimination, and the multivariate extension of `hex-rcf` need. The
instances are in this library rather than in hex-mv-poly because exact
division of multivariate polynomials is an algorithm, not a projection.

Two limits on that claim, both visible in hex-resultant's source rather
than in its SPEC, and both stated again below:

- The executable chain and its correctness theorems both run over
  `MvPoly`: the Mathlib-free `Lean.Grind.CommRing` tower is now landed in
  `HexMvPoly/Ring.lean`. This library must still supply `Div` and prove
  `ExactDivLaws`; neither follows from the ring structure.
- The instances do not let a caller nest the type. The certificate below
  bottoms out in a Bézout identity in the coefficient ring, and
  `MvPoly n R cmp` is not a Bézout domain for `n ≥ 1`. Nested
  coefficients have to be flattened to `MvPoly (m+n) R` first.

**Divisibility and squarefree tests from Mathlib.** The companion supplies
`Decidable (a ∣ b)` and `Decidable (Squarefree p)` for
`MvPolynomial (Fin n) ℤ`, and the same squarefree instance over `ℚ`, in
the style of `hex-berlekamp-mathlib`'s `Decidable (Irreducible f)`.
The integer case combines the polynomial-part test here with Mathlib's
existing decision procedure for squarefreeness of the integer content;
integer factorization is not a dependency.

**Partial fractions and CAD.** `Apart` in more than one variable and the
projection phase of cylindrical algebraic decomposition both need
squarefree bases and content. They are downstream of factorization, so
they are consumers of this library rather than drivers of its design.

## Scope

In scope: gcd with cofactors, gcd of a list, lcm, content and primitive
part in a named variable, monomial content, exact division and its
`Option` form, divisibility, characteristic-zero squarefree decomposition
and radical, and a squarefreeness decision over perfect fields in any
characteristic.

Not in scope: full positive-characteristic squarefree decomposition,
factorization into irreducibles (that is `hex-mv-factor`,
and it depends on this library), Gröbner bases, resultants themselves
(hex-resultant computes them once this library supplies the instances),
multivariate Hensel lifting, and the sparse Hensel gcd route (see
"Routes not specified here").

Also not in scope: the univariate integer case, which is
[hex-poly-z-gcd](hex-poly-z-gcd.md). That library computes gcds of
`ZPoly` for the consumers that hold `DensePoly Int` and would otherwise
convert, its certificate is the arity-one specialisation of the one
below with an unconditional soundness theorem, and this
library's integer producer should call it for the arity-one base case
rather than reimplement it.

The coefficient rings that matter are `Int`, `Rat`, `ZMod64 p`, and
`FpPoly p`. Verification is written against algebraic interfaces; candidate
production is a separate backend because modular reduction, reconstruction,
and random evaluation are not operations of an abstract gcd domain.

## What the coefficient ring must supply

```lean
namespace Hex

/-- Executable operations a coefficient ring must supply. `exactDiv a b`
is required to be correct only when `b ∣ a` and `b ≠ 0`; other inputs
return a stable junk value. -/
class GcdOps (R : Type u) [Zero R] [One R] [Add R] [Mul R] [Dvd R] where
  gcd      : R → R → R
  exactDiv : R → R → R
  isUnit   : R → Bool
  normUnit : R → R

/-- The canonical associate chosen by `GcdOps`. -/
def normalize [Zero R] [One R] [Add R] [Mul R] [Dvd R] [GcdOps R]
    (a : R) : R :=
  a * GcdOps.normUnit a

/-- Coefficient rings in which coprimality is witnessed by a Bézout
identity. Required of the base ring only, never of `MvPoly`. -/
class BezoutOps (R : Type u) [Zero R] [One R] [Add R] [Mul R] [Dvd R]
    extends GcdOps R where
  xgcd : R → R → R × R

/-- The algebraic hypotheses the gcd algorithms need of `R`. Separated
from the operations so that a consumer may compute without them. -/
class LawfulGcdOps (R : Type u) [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] : Prop where
  dvd_iff        : ∀ a b : R, a ∣ b ↔ ∃ c, b = a * c
  one_ne_zero    : (1 : R) ≠ 0
  no_zero_div    : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0
  gcd_dvd_left   : ∀ a b, GcdOps.gcd a b ∣ a
  gcd_dvd_right  : ∀ a b, GcdOps.gcd a b ∣ b
  dvd_gcd        : ∀ a b d, d ∣ a → d ∣ b → d ∣ GcdOps.gcd a b
  gcd_normalized : ∀ a b, normalize (GcdOps.gcd a b) = GcdOps.gcd a b
  exactDiv_cancel : ∀ a b, b ≠ 0 → GcdOps.exactDiv (a * b) b = a
  isUnit_iff     : ∀ a, GcdOps.isUnit a = true ↔ ∃ b, a * b = 1
  normUnit_unit  : ∀ a, ∃ b, GcdOps.normUnit a * b = 1
  normalize_mul  : ∀ a b, normalize (a * b) = normalize a * normalize b
  normalize_idem : ∀ a, normalize (normalize a) = normalize a
  normalize_unit : ∀ a, GcdOps.isUnit a = true → normalize a = 1

/-- Correctness of the executable extended gcd at the base ring. -/
class LawfulBezoutOps (R : Type u) [Lean.Grind.CommRing R] [DecidableEq R]
    [BEq R] [LawfulBEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R] : Prop where
  xgcd_bezout : ∀ a b,
    let uv := BezoutOps.xgcd a b
    uv.1 * a + uv.2 * b = normalize (GcdOps.gcd a b)

/-- The proof-only statement that every pair has a greatest common divisor.
It deliberately does not select an executable operation. -/
class GcdDomainLaws (S : Type u) [Lean.Grind.CommRing S] [Dvd S] : Prop where
  dvd_iff : ∀ a b : S, a ∣ b ↔ ∃ c, b = a * c
  one_ne_zero : (1 : S) ≠ 0
  no_zero_div : ∀ a b : S, a * b = 0 → a = 0 ∨ b = 0
  gcd_exists : ∀ a b : S, ∃ g : S,
    g ∣ a ∧ g ∣ b ∧ ∀ d, d ∣ a → d ∣ b → d ∣ g

/-- Euclid's lemma in the form certificate maximality needs. This class
does not mention a multivariate gcd operation, so it can be established
before that operation is defined. -/
class CoprimeCancelLaws (S : Type u) [Lean.Grind.CommRing S] [Dvd S] : Prop where
  cancel_coprime : ∀ g a b d : S,
    (∀ e, e ∣ a → e ∣ b → ∃ u, e * u = 1) →
    d ∣ g * a → d ∣ g * b → d ∣ g
```

with `normalize a = a * GcdOps.normUnit a`, matching Mathlib's naming so
the companion's transport lemmas do not have to rename anything.

Five of the `LawfulGcdOps` fields are load-bearing and easy to leave out.
`one_ne_zero` supplies the nontriviality required by `Fraction`.
`no_zero_div` is used by every
argument below that multiplies leading coefficients or reasons about the
degree of a divisor. `normalize_mul` is what makes Gauss's lemma an
equality rather than an `Associated` statement. `gcd_normalized` is what
makes `gcd` a function rather than a choice of associate, and
`normalize_unit` turns a normalized unit gcd into `1`.

`LawfulGcdOps R` implies `GcdDomainLaws R`, which implies
`CoprimeCancelLaws R` by ordinary gcd-domain arithmetic. Independently of
any multivariate candidate producer, the proof-only Gauss development
lifts `GcdDomainLaws R` through `MvPoly`; it then derives
`CoprimeCancelLaws (MvPoly n R cmp)`. Those lifts are named algebraic
deliverables below rather than something hidden inside checker soundness.

`normUnit` returns a unit on **every** input including zero, so the field
instance is `normUnit a = if a = 0 then 1 else a⁻¹`, not `a⁻¹`.

Lawful instances are required alongside the executable ones. In
particular, `BezoutOps.xgcd` is not sufficient by itself: an
implementation returning `(0, 0)` would satisfy the operations class and
make the arity-zero certificate impossible to prove.

`GcdOps` instances required here are `Int` (gcd through hex-arith,
`normUnit` the sign with `normUnit 0 = 1`), `Rat` and concrete fields,
`ZMod64 p` for prime `p`, `FpPoly p`, `DensePoly Int`, and
`MvPoly n R cmp` through this library's checked implementation.

`BezoutOps` holds for `Int`, for fields, and for `FpPoly p` with `p`
prime. It does not hold for `MvPoly n R cmp` with `n ≥ 1`, and it does
not hold for `DensePoly Int`: neither ring is a Bézout domain. That
failure is not incidental, and it is what makes the certificate design
below the shape it is.

**Modular reduction is a separate, total interface.** The fast
coprimality certificate reduces coefficients into a small field, and no
operation above provides that. The verifier accepts a homomorphism as
certificate data rather than discovering one through typeclass search:

```lean
/-- A total ring homomorphism from the coefficient ring into a finite
field, supplied per certificate. -/
structure CoeffHom (R : Type u) (p : Nat) [Zero R] [One R] [Add R]
    [Mul R] [ZMod64.Bounds p] where
  toField : R → ZMod64 p
  map_zero : toField 0 = 0
  map_one  : toField 1 = 1
  map_add  : ∀ a b, toField (a + b) = toField a + toField b
  map_mul  : ∀ a b, toField (a * b) = toField a * toField b
```

`Int` supplies one at every bounded prime. `ZMod64 p` supplies the
identity at its own prime, and `FpPoly p` supplies evaluation at a
chosen field point. There is no ring homomorphism `Rat → ZMod64 p`, so
the rational backend clears denominators to propose its candidate and
uses the `ratLift` certificate below to transport coprimality from the
primitive integer models. `splitBezout` remains its deterministic fallback.
Partial maps are not accepted: knowing that a map is defined on the
product does not by itself show that it is defined on an arbitrary divisor
and quotient.

## Exact division

Exact division is the operation every check in this library runs, so it
is specified before the gcd itself.

```lean
namespace Hex.MvPoly

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R]

/-- Division with remainder against a single divisor, in the monomial
order `cmp`: repeatedly cancel the leading monomial of the running
dividend against the leading monomial of `g`, moving a term to the
remainder when `Mono.dvd` fails. -/
def divMod [IsMonomialOrder cmp] (f g : MvPoly n R cmp) :
    MvPoly n R cmp × MvPoly n R cmp

/-- The exact quotient, or `none` when `g = 0` or `g ∤ f`. -/
def divExact? [IsMonomialOrder cmp] (f g : MvPoly n R cmp) :
    Option (MvPoly n R cmp)

instance : Dvd (MvPoly n R cmp)  -- `∃ q, f = q * g`
instance [IsMonomialOrder cmp] (f g : MvPoly n R cmp) : Decidable (g ∣ f)

/-- The total form, for hex-resultant's `[Div R]` interface. -/
instance [IsMonomialOrder cmp] : Div (MvPoly n R cmp)
instance [IsMonomialOrder cmp] [LawfulGcdOps R] :
    ExactDivLaws (MvPoly n R cmp)

/-- No term of `r` can be cancelled by the leading term of `g`: either
the leading monomial does not divide it or the corresponding coefficient
quotient does not check by multiplication. -/
def ReducedBy [IsMonomialOrder cmp] (r g : MvPoly n R cmp) : Prop
```

The zero-divisor branch is `divMod f 0 = (0, f)`. The decidable
divisibility instance uses equality when the proposed divisor is zero and
`divExact?.isSome` otherwise, so it still decides the existential `Dvd`
relation and in particular reports `0 ∣ 0`.

`divMod` terminates because `IsMonomialOrder.wf` well-orders the
monomials and each step strictly decreases the leading monomial of the
running dividend. This is the one place the `wf` field of
`IsMonomialOrder` is load-bearing, and it is why the divisibility
operations require the full class rather than `TransCmp` plus
`LawfulEqCmp`.

When the leading monomial divides but the leading coefficient does not,
`divMod` moves that term to the remainder and `divExact?` fails. The
coefficient quotient is accepted only after multiplication reconstructs
the coefficient; `GcdOps.exactDiv` is allowed to return junk off its
lawful domain.

`divExact?` is not `divMod` followed by a zero test. It fails as soon as
either leading divisibility check fails, which is the common case when
the answer is "does not divide" and is what makes trial division cheap
enough to run on every candidate.

```lean
theorem divMod_spec : f = (divMod f g).1 * g + (divMod f g).2
theorem divMod_reduced (hg : g ≠ 0) : ReducedBy (divMod f g).2 g
theorem divExact?_zero_right : divExact? f 0 = none
theorem divExact?_eq (hg : g ≠ 0) : divExact? f g = some q ↔ f = q * g
theorem divExact?_isSome_of_dvd (hg : g ≠ 0) : g ∣ f → (divExact? f g).isSome
```

The `g ≠ 0` hypothesis on `divExact?_eq` is not decoration. At `f = 0`
and `g = 0` the right-hand side holds for every `q`, and a deterministic
`Option` returns at most one, so the unconditional biconditional is
false. `divExact? f 0 = none` is the separate stated behaviour, which
also makes `0 ∣ 0` decide as `true` through the `Dvd` instance rather
than through `divExact?`.

**Principle 8 classification.** `Div (MvPoly n R cmp)` is a total form of
the partial helper `divExact?`. It is admissible as
**`unreachable-by-pipeline-invariant`**, with the unreachability theorem
`divExact?_isSome_of_dvd` named above. The pipeline invariant is that
every division this library performs is preceded by a divisibility test
or is justified by a divisibility fact already established (content
division after a content gcd, cofactor extraction after an accepted
certificate). The only external consumer of the `Div` instance is
hex-resultant's subresultant chain, whose own SPEC states the matching
invariant that a valid Brown run proves every quotient exact.

**A performance requirement, not an optimisation.** Trial division
dominates the running time of a modular gcd whenever the gcd is large,
so `divExact?` carries a cheap necessary-condition filter ahead of the
division loop: `degreeOf j g ≤ degreeOf j f` for every `j`, `Mono.dvd`
of the monomial contents, and divisibility of the leading coefficients.
A producer backend with a total `CoeffHom` may additionally test one
small-field evaluation; the generic operation cannot assume that map
exists. Each test rejects without allocating a quotient. The filter is a
prefilter only, and the division loop remains the decision.

## The recursive view

hex-mv-poly supplies the arity-dropping pair, and this library uses it as
it stands:

```lean
def toUnivariate (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n+1) R cmp) : DensePoly (MvPoly n R cmp')

def ofUnivariate (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (q : DensePoly (MvPoly n R cmp')) : MvPoly (n+1) R cmp
```

`HexMvPoly/Recursive.lean` proves `toUnivariate_coeff`,
`ofUnivariate_coeff`, and both round trips, on top of the `removeVar` and
`insertVar` monomial reindexing. Everything the algorithms need in the
main variable then comes from hex-poly on the result: `DensePoly.degree?`
is the degree in `xᵢ`, distinguishing the zero polynomial from a constant
as the certificate's degree checks require; `DensePoly.leadingCoeff` is
the leading coefficient in `xᵢ`; and `DensePoly.coeff k` is the
`xᵢ`-degree-`k` slice.

The arity drops at every step, and two costs follow. Reindexing between
the remaining `n` variables and the original `n+1` is `Fin.succAbove i`
and its partial inverse, and it appears in every statement relating a
coefficient back to the polynomial it came from. And nothing determines
the comparator on the remaining variables, so `cmp'` is an explicit
argument that every recursive step chooses and every statement carries.

An arity-preserving view, whose coefficients stay in the same `n`
variables and merely happen not to involve `xᵢ`, removes both costs. It
is not worth its price. `Recursive.lean` is 436 lines with three fold
lemmas and four round-trip theorems, and the arity-preserving pair would
mirror all of it, where the reindexing is bookkeeping inside proofs that
are being written anyway.

The arity drop also buys something the other view has to pay for. "The
coefficients do not involve `xᵢ`" holds **in the type**, so no invariant
is carried, and the certificate below recurses structurally on the arity
rather than on a set of remaining variables. Progress is then free rather
than a side condition the checker has to verify.

One operation is needed that hex-mv-poly does not name, and it belongs
here rather than there:

```lean
/-- Embed a polynomial in the remaining variables as one that is constant
in `xᵢ`. `ofUnivariate i cmp'` applied to a `DensePoly.C`. -/
def constIn (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (c : MvPoly n R cmp') : MvPoly (n+1) R cmp
```

with `coeff_constIn`, `constIn_mul` (it is a ring homomorphism), and
injectivity. Content and primitive part are stated through it.

## What hex-mv-poly supplies

hex-mv-poly is finished (`done_through: 7`), so the two additions this
library needed were made to a complete library rather than to a draft.
Both are landed, in `HexMvPoly/Ring.lean` and `HexMvPoly/Structural.lean`.

**`Lean.Grind.CommRing (MvPoly n R cmp)`**, with the `NatCast`, `OfNat`,
`SMul Nat`, `IntCast`, `SMul Int`, semiring, and ring instances beneath
it. Every hex-resultant correctness theorem takes
`[Lean.Grind.CommRing S]`, so without it the subresultant chain runs over
`MvPoly` and none of its theorems apply.
`HexResultant/ExactDiv.lean` builds the same tower for
`DensePoly`. The `Semiring.npow` field uses hex-mv-poly's existing
`npowBySq` and its proved `pow_succ` rather than a second power
operation.

**`mapCoeffs`**, a linear coefficient map with `coeff_mapCoeffs` and the
homomorphism laws `mapCoeffs_zero`, `mapCoeffs_one`, `mapCoeffs_add`, and
`mapCoeffs_mul`. `Structural.bind` already changes the coefficient type,
so `bind φ X` is a coefficient map, but it folds one polynomial addition
and one monomial product per term, making a pure coefficient map
quadratic in the term count where a map over the backing values is
linear. Reduction modulo a prime is on the inner loop of every modular
route below. `bind` also carries no homomorphism laws, which is what the
certificate needs. The laws take their hypotheses on `φ` explicitly
rather than through a bundled homomorphism record.

Nothing further is needed from hex-mv-poly. `monoContent` is not one of
its additions: `Mono.gcd` exists and the fold over `support` is three
lines belonging with the content operations here. The arity-preserving
recursive view is not wanted at all, for the reason under "The recursive
view".

## Required amendment to hex-resultant

The `splitBezout` certificate constructor needs the Bézout cofactors of
the subresultant chain. hex-resultant does not compute them, and it is
worth saying so explicitly because the chain looks as though it must:
`subresultantAux` calls `pseudoDivMod` and keeps only `.2`
(`HexResultant/Subresultant.lean:609` and `:616`); the quotient is
discarded and no transformation is accumulated.

An extended chain is therefore a new recurrence that tracks the
transformation pair through the pseudo-scaling and the exact scalar
division at every step, with proofs that each cofactor numerator is
divisible by the Brown scalar it is divided by.

The owning contract is now recorded under "Planned extended chain for gcd
consumers" in [hex-resultant's SPEC](../../HexResultant/SPEC/hex-resultant.md);
its signature is repeated here only to show the consumer boundary:

```lean
/-- The subresultant chain with the cofactors producing each entry:
`(uₖ, vₖ, Sₖ)` with `uₖ · f + vₖ · g = Sₖ`. -/
def subresultantChainExt [Zero R] [DecidableEq R] [One R] [Add R] [Sub R]
    [Mul R] [Div R] (f g : DensePoly R) :
    Array (DensePoly R × DensePoly R × DensePoly R)
```

That is a substantive development, not a one-line export, and it is a
hard prerequisite for this library's complete fallback. The modular
constructor is intentionally primary but cannot be complete while
`ZMod64.Bounds` caps its primes. With
`L = lcm(1, …, 2^31 - 1)`, the coprime univariate pair `x` and `x + L`
has identical images at every permitted prime. The extended chain
produces the `splitBezout` constructor without a modulus and is what
makes `gcdCert_checks` provable for every input.

## Content and primitive part

```lean
def contentIn (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp']
    (p : MvPoly (n+1) R cmp) : MvPoly n R cmp'
def primPartIn (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp']
    (p : MvPoly (n+1) R cmp) : MvPoly (n+1) R cmp
def content (p : MvPoly n R cmp) : R
def primPart (p : MvPoly n R cmp) : MvPoly n R cmp
```

The scalar `content` is the producer-free `scalarContent` fold named
below; only `contentIn`, whose coefficients are themselves multivariate,
needs `ContentCert` and recursive gcd production.

```lean
theorem contentIn_mul_primPartIn :
    constIn i cmp' (contentIn i cmp' p) * primPartIn i cmp' p = p
theorem contentIn_dvd_coeff :
    ∀ k, contentIn i cmp' p ∣ (toUnivariate i cmp' p).coeff k
theorem contentIn_zero : contentIn i cmp' 0 = 0
theorem primPartIn_zero : primPartIn i cmp' 0 = 0
theorem primPartIn_content (hp : p ≠ 0) :
    contentIn i cmp' (primPartIn i cmp' p) = 1
theorem contentIn_mul  :
    contentIn i cmp' (p * q) = contentIn i cmp' p * contentIn i cmp' q
theorem primPartIn_mul :
    primPartIn i cmp' (p * q) = primPartIn i cmp' p * primPartIn i cmp' q
theorem content_mul_primPart : C (content p) * primPart p = p
theorem content_zero : content (0 : MvPoly n R cmp) = 0
theorem primPart_zero : primPart (0 : MvPoly n R cmp) = 0
theorem content_primPart (hp : p ≠ 0) : content (primPart p) = 1
theorem content_mul : content (p * q) = content p * content q
theorem primPart_mul : primPart (p * q) = primPart p * primPart q
```

The four multiplicativity statements are Gauss's lemma in the named
variable and scalar views. They are stated for normalized content, so they
are equalities rather than association statements, which is what
`normalize_mul` in `LawfulGcdOps` is for. Their proofs are the largest
piece of algebra in the executable Mathlib-free layer.

**The universal property of content is the hard one.**

```lean
theorem dvd_contentIn (d) :
    (∀ k, d ∣ (toUnivariate i cmp' p).coeff k) → d ∣ contentIn i cmp' p
```

`contentIn` is computed by folding this library's own multivariate gcd,
so `dvd_contentIn` is gcd maximality one arity down. The proof is a
simultaneous induction on the arity with `checkGcd_greatest`; the
`ContentCert` below exposes every fold step and prevents the induction
from calling a candidate producer.

The checker also needs unit and normalization operations before the
public multivariate `GcdOps` instance exists. They are nonrecursive and
live in `Normalize.lean` rather than behind that instance:

```lean
/-- The constant unit selected from the leading coefficient; `C 1` at
zero. -/
def polyNormUnit (p : MvPoly n R cmp) : MvPoly n R cmp
def polyNormalize (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p * polyNormUnit p
/-- True exactly for a constant polynomial whose coefficient is a unit. -/
def polyIsUnit (p : MvPoly n R cmp) : Bool
/-- Normalized gcd fold of the distributed scalar coefficients. This does
not call the multivariate gcd. Public `content` delegates to it. -/
def scalarContent (p : MvPoly n R cmp) : R

theorem polyIsUnit_iff :
    polyIsUnit p = true ↔ ∃ q, p * q = 1
```

`checkCoprime.unit` calls `polyIsUnit`, and `checkGcd` calls
`polyNormalize`. The later `GcdOps (MvPoly n R cmp)` instance delegates
its `isUnit`, `normUnit`, and normalization behavior to these definitions,
so `Cert.lean` has no dependency on `Gcd.lean`.

## The certificate

The design is one verified checker and several unverified candidate
producers, following design principle 4. All the heuristics below, and
all their prime choices, evaluation points, random draws, and skeleton
guesses, are outside the proof.

### What "greatest" needs

The identities `f = g · f'` and `h = g · h'` are two exact divisions and
they establish `g ∣ f` and `g ∣ h`, nothing more. Any common divisor
whatever, `1` included, satisfies them. Maximality is a separate
obligation, and the usable form of it is that the cofactors `f'` and `h'`
have no nonunit common divisor. This is the case
[future-work](../future-work.md) makes in its own preamble, and the
whole point of the certificate is to carry the second witness.

### Bézout does not witness coprimality here

[future-work](../future-work.md) said of the modular gcd for `ℤ[x]` that
the certificate carries cofactors "together with a Bézout witness that
`f'` and `h'` are coprime", and now records the correction instead. That
witness does not exist, in one variable or in several. `ℤ[x]` is not a Bézout domain: `x` and `2` are coprime
and `u · x + v · 2 = 1` has no solution in `ℤ[x]`. The same holds in
`R[x₁, …, xₙ]` over any base that is not a field, and over a field as
soon as `n ≥ 2` (`x₁` and `x₂` are coprime with no Bézout identity).

Two things do work, and both are supported.

### The modular witness, which is primary when available

Fix a variable `i`, a comparator `cmp'` on the remaining variables, a
bundled bounded prime `P : ZMod64.Prime`, a total homomorphism
`φ_R : CoeffHom R P.m`, and an
evaluation point `a : Fin n → ZMod64 P.m`. The checked image is a concrete
function with no partial or residual-variable case:

```lean
def imageAt (P : ZMod64.Prime)
    (φ_R : @CoeffHom R P.m _ _ _ _ P.bounds)
    (a : Fin n → @ZMod64 P.m P.bounds) (i : Fin (n+1))
    (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
    (f : MvPoly (n+1) R cmp) : @FpPoly P.m P.bounds :=
  letI := P.bounds
  letI := ZMod64.primeModulusOfPrime P.prime
  let q := toUnivariate i cmp' f
  DensePoly.ofList <| (List.range q.size).map fun k =>
    MvPoly.eval a (MvPoly.mapCoeffs φ_R.toField (q.coeff k))
```

If the degrees of `toUnivariate i cmp' f'` and
`imageAt P φ_R a i cmp' f'` agree, and likewise for `h'`, and
`α · imageAt P φ_R a i cmp' f' + β · imageAt P φ_R a i cmp' h' = 1`, then
`f'` and `h'` have no common divisor of positive degree in `xᵢ`.

The degree argument uses totality. A common divisor `d` gives
`f' = d · e`, hence the image equality follows from the ring-homomorphism
laws. Degrees cannot increase under the image and add in both domains;
preservation of the product degree forces preservation of both factor
degrees. The image of `d` divides the checked Bézout identity, so it is a
unit and `d` has degree zero in `xᵢ`. The checked degree equalities already
say that the evaluated leading coefficients do not vanish.

What remains is a common divisor of both coefficient contents. Those
contents and the gcd certificates used to compute them are data in the
certificate rather than fresh calls to `contentIn`.

### The certificate type and the checker

The three certificate types are mutually inductive because a content
certificate is a fold of gcd certificates, while a positive-arity gcd
certificate contains two content certificates. Every occurrence is
strictly positive and every cycle drops the arity before returning to a
coprimality certificate.

```lean
mutual
  inductive CoprimeCert :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type u
    | unit : CoprimeCert n R cmp
    | base (u v : R) : CoprimeCert 0 R cmp
    | split (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
        [IsMonomialOrder cmp'] [One R] [Add R] [Mul R]
        (P : ZMod64.Prime)
        (φ : @CoeffHom R P.m _ _ _ _ P.bounds)
        (a : Fin n → @ZMod64 P.m P.bounds)
        (α β : @FpPoly P.m P.bounds)
        (left right : ContentCert n R cmp')
        (rest : CoprimeCert n R cmp') : CoprimeCert (n+1) R cmp
    | splitBezout (i : Fin (n+1))
        (cmp' : Mono n → Mono n → Ordering) [IsMonomialOrder cmp']
        (u v : MvPoly (n+1) R cmp) (r : MvPoly n R cmp')
        (left right : ContentCert n R cmp')
        (rest : CoprimeCert n R cmp') : CoprimeCert (n+1) R cmp
    | ratLift (scaleL scaleR : Rat) (left right : MvPoly n Int cmp)
        (cert : CoprimeCert n Int cmp) : CoprimeCert n Rat cmp

  inductive GcdCert :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type u
    | mk (gcd cofL cofR : MvPoly n R cmp) (coprime : CoprimeCert n R cmp)

  /-- A checked left fold of gcd over a polynomial's coefficient list.
  `steps[k]` certifies the gcd of the previous accumulator and coefficient
  `k`; `value` is the final accumulator. -/
  inductive ContentCert :
      (n : Nat) → (R : Type u) → [Zero R] →
      (cmp : Mono n → Mono n → Ordering) →
      [Std.TransCmp cmp] → [Std.LawfulEqCmp cmp] → Type u
    | mk (value : MvPoly n R cmp) (steps : List (GcdCert n R cmp))
end

def GcdCert.gcd : GcdCert n R cmp → MvPoly n R cmp
def GcdCert.cofL : GcdCert n R cmp → MvPoly n R cmp
def GcdCert.cofR : GcdCert n R cmp → MvPoly n R cmp
def GcdCert.coprime : GcdCert n R cmp → CoprimeCert n R cmp
def ContentCert.value : ContentCert n R cmp → MvPoly n R cmp

def checkContent (coeffs : List (MvPoly n R cmp)) : ContentCert n R cmp → Bool
def checkCoprime (f h : MvPoly n R cmp) : CoprimeCert n R cmp → Bool
def checkGcd (f h : MvPoly n R cmp) : GcdCert n R cmp → Bool
```

All three declarations use the identical index telescope shown above;
`n`, `R`, `cmp`, and the representation instances are indices rather than
mixing parameters and indices across the mutual block. Every arity-dropping
constructor carries `[IsMonomialOrder cmp']`, which supplies both comparator
instances required to form its lower-arity `MvPoly` values.

`checkContent` starts at zero, requires exactly one `GcdCert` per
coefficient, checks each certificate against the current accumulator and
coefficient, advances to its gcd, and finally compares the accumulator
with `value`. `contentInCert` is the producer and `contentIn` projects its
value; a checker never calls that producer.

`checkCoprime` on `split` checks the two image degrees and the Bézout
identity, checks `left` and `right` against the two coefficient lists,
then checks `rest` against their certified values. The explicit bundled
`P` supplies bounds before `ZMod64 P.m` is formed and installs the field
instance from `P.prime` locally; no runtime-selected prime relies on
typeclass search. Producers try the smallest usable prime because kernel
replay checks its primality proof and the project-local trial proof becomes
expensive near the 31-bit limit.
`splitBezout` checks `r ≠ 0`, `u · f + v · h = constIn i cmp' r`, the two
content certificates, and the same recursive check. `base` checks the
Bézout identity in `R`, and `unit` checks that one side is a unit.
`ratLift` checks `scaleL ≠ 0`, `scaleR ≠ 0`, that the two rational inputs
are the stated scalar multiples of the coefficientwise `Int → Rat` images,
that both integer models have `scalarContent = 1`, and that `cert` checks
for those models. Gauss descent then transports integer coprimality to
rational coprimality without a nonexistent `Rat → ZMod64` homomorphism.

Indexing the certificate by the arity is what makes "each step removes a
variable" true, and it is free: the constructor's result type says so.
An arity-preserving certificate would need a set of remaining variables
carried alongside and an `i ∈ active` check in the checker, purely to
recover the same guarantee.

**Degenerate inputs are certificate completeness cases, not output
conventions.** A coprime pair cannot contain zero unless the other side
is a unit, so the producer must special-case them: `gcd 0 0` returns
`.mk 0 1 1 .unit`; `gcd f 0` returns
`.mk (polyNormalize f) u 0 .unit` with
`u` the unit making the identity hold; arity zero and the
all-variables-eliminated case go through `base`. Without these the
modular constructor has no image Bézout identity to produce.

The `splitBezout` argument is the shorter of the two: a common divisor
`d` divides `constIn i cmp' r`, and a divisor of something constant in
`xᵢ` is constant in `xᵢ` in a domain, so `d` divides both contents. It
needs no prime, point, or homomorphism. It is not primary because `u` and
`v` come from an extended subresultant computation, which suffers the
coefficient swell the modular routes exist to avoid. It nevertheless
remains mandatory as the complete last route.

### Where maximality lives

Certificate replay and gcd-domain algebra are separate obligations. The
certificate proves exact cofactor identities and that the cofactors have
no common nonunit divisor. Turning those facts into gcd maximality uses
`CoprimeCancelLaws (MvPoly n R cmp)`; it does not follow from the
certificate constructors alone.

The Mathlib-free Gauss development establishes that instance before the
checker proof. At each arity it supplies three named pieces: the embedding
into `Fraction (MvPoly n R cmp)`, gcd over the resulting fraction-field
univariate polynomial, and primitive descent back to `MvPoly`. A
proof-only finite fold chooses coefficient gcds from `GcdDomainLaws`; it
does not call the executable `contentIn`. These pieces lift
`GcdDomainLaws` and hence `CoprimeCancelLaws` one variable at a time. This
work is independent of every candidate route and does not call `gcdCert`.

```lean
/-- The semantic property directly witnessed by a coprimality certificate. -/
def CoprimeCofactors (f h : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ f → d ∣ h → ∃ u, d * u = 1

/-- What `checkGcd` establishes without gcd-domain reasoning. -/
def CheckedGcdResult (f h g f' h' : MvPoly n R cmp) : Prop :=
  f = g * f' ∧ h = g * h' ∧ polyNormalize g = g ∧
  CoprimeCofactors f' h'

/-- The checked result plus the separate greatest-divisor conclusion. -/
def IsGcdCertResult (f h g f' h' : MvPoly n R cmp) : Prop :=
  CheckedGcdResult f h g f' h' ∧
  ∀ d, d ∣ f → d ∣ h → d ∣ g

theorem checkCoprime_sound [LawfulGcdOps R] :
    checkCoprime f h c = true → CoprimeCofactors f h

theorem checkContent_sound [LawfulGcdOps R] :
    checkContent coeffs c = true →
      (∀ q ∈ coeffs, c.value ∣ q) ∧
      (∀ d, (∀ q ∈ coeffs, d ∣ q) → d ∣ c.value)

theorem checkGcd_sound [LawfulGcdOps R] :
    checkGcd f h c = true →
      CheckedGcdResult f h c.gcd c.cofL c.cofR

theorem CoprimeCofactors.greatest [CoprimeCancelLaws (MvPoly n R cmp)]
    (hc : CheckedGcdResult f h g f' h') :
    ∀ d, d ∣ f → d ∣ h → d ∣ g

theorem checkGcd_greatest [LawfulGcdOps R] :
    checkGcd f h c = true →
      IsGcdCertResult f h c.gcd c.cofL c.cofR
```

The checker proof is a simultaneous arity induction: either split makes a
common divisor constant in the main variable, the checked content folds
and lower-arity induction show that it divides both certified contents,
and `rest` makes it a unit. Content maximality uses lower-arity
`checkGcd_greatest`, whose common-factor step comes from the independent
Gauss instance. `LawfulBezoutOps` is not a soundness premise because the
checker validates every stored base identity; it is needed by the producer
completeness theorem that obtains those identities from `xgcd`.

The zero conventions are `contentIn 0 = 0`, `content 0 = 0`, and both
primitive parts of zero equal zero. They preserve multiplication; the
content-of-primitive-part theorem consequently needs `p ≠ 0`. The scalar
API has the matching contracts
`C (content p) * primPart p = p`, `content (primPart p) = 1` for
nonzero `p`, and the corresponding multiplicativity theorems.

`checkGcd_greatest` and `gcdCert_checks` then supply
`LawfulGcdOps (MvPoly n R cmp)`, including `dvd_gcd`. The noncircular
order is: Gauss/common-factor algebra, checker soundness, complete
producer, public gcd laws, then the instance.

### What `cancel` actually needs

`CoprimeCofactors` alone does not justify the rewrite. With
`(f, h) = (0, 0)` the certificate `g = 0`, `f' = h' = 1` checks, and
rewriting `0 / 0` to `1 / 1` is false under Lean's total division. The
tactic's obligation is the cofactor identities **plus** `h ≠ 0`, plus
the cancellation law of the target field, which is the same
denominator-nonvanishing side condition
[future-work](../future-work.md) identifies for `Together` and `Apart`
and resolves by matching `field_simp`. Coprimality is what makes the
output fully reduced, which is a quality property of the answer rather
than a soundness property of the rewrite.

## The gcd API

Candidate production is an explicit backend, not an accidental consequence
of whichever coefficient instances happen to be in scope. This is necessary
because `Int` uses modular reduction and CRT, `Rat` first clears
denominators, and finite fields use different image operations. Randomness
and every heuristic limit are also explicit and reproducible:

```lean
namespace Hex.MvPoly

structure GcdConfig where
  rand               : Rand
  heuristicBitBudget : Nat
  brownPrimeFuel     : Nat
  brownPointFuel     : Nat

def GcdConfig.default : GcdConfig := {
  rand := Rand.ofSeed 0
  heuristicBitBudget := 1048576
  brownPrimeFuel := 64
  brownPointFuel := 4096
}

structure GcdRun (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  cert : GcdCert n R cmp
  rand : Rand

/-- The output of an untrusted fast backend. `none` means that every
applicable fast route declined or exhausted its budget. -/
structure GcdProposal (n : Nat) (R : Type u) [Zero R]
    (cmp : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] where
  cert? : Option (GcdCert n R cmp)
  rand  : Rand

/-- Coefficient-specific candidate production. The public wrapper checks
the proposal and owns the complete PRS fallback. -/
class GcdProducer (R : Type u) [Zero R] where
  propose : {n : Nat} → (cmp : Mono n → Mono n → Ordering) →
    [IsMonomialOrder cmp] → GcdConfig →
    MvPoly n R cmp → MvPoly n R cmp → GcdProposal n R cmp

variable [IsMonomialOrder cmp] [DecidableEq R] [BEq R] [LawfulBEq R]
  [BezoutOps R] [GcdProducer R]

def gcdCertWith (cfg : GcdConfig) (f h : MvPoly n R cmp) : GcdRun n R cmp
def gcdCert (f h : MvPoly n R cmp) : GcdCert n R cmp :=
  (gcdCertWith GcdConfig.default f h).cert
def gcdWith (cfg : GcdConfig) (f h : MvPoly n R cmp) :
    MvPoly n R cmp × Rand :=
  let run := gcdCertWith cfg f h
  (run.cert.gcd, run.rand)
def gcd (f h : MvPoly n R cmp) : MvPoly n R cmp := (gcdCert f h).gcd
def cofactors (f h : MvPoly n R cmp) : MvPoly n R cmp × MvPoly n R cmp
def isCoprime (f h : MvPoly n R cmp) : Bool
def gcdList (ps : List (MvPoly n R cmp)) : MvPoly n R cmp
def lcm (f h : MvPoly n R cmp) : MvPoly n R cmp
```

The concrete proposal instances are `intProducer`, `ratProducer`,
`primeProducer`, and `fpPolyProducer`. An abstract coefficient ring does
not silently receive the integer modular algorithm; it may use
the low-priority `noFastProducer`, which returns `none` unless a concrete
instance overrides it. `gcdCertWith` runs the proposal,
accepts `some c` only when `checkGcd f h c = true`, and otherwise calls
the internal `prsCert`, which does not dispatch through `GcdProducer`
again. Consequently a buggy or adversarial backend can affect performance
but not the result or totality theorem. The returned `Rand` is the state
advanced by the proposal even when it is rejected, following the
project-wide randomness convention. `gcd`, and therefore typeclass use,
has stable behaviour through the fixed default seed; callers that need
independent runs use `gcdCertWith`.

The public `isCoprime` is exact: it tests whether the checked `gcd` is a
unit. The one-sided modular probe is an internal producer
`tryCoprimeCert?`; `none` means only that this point or prime was
inconclusive and is never exposed as a false public answer.

The public operations have semantic contracts, not only degenerate-case
examples:

```lean
theorem gcdCertWith_checks [LawfulGcdOps R] [LawfulBezoutOps R] :
    checkGcd f h (gcdCertWith cfg f h).cert = true
theorem gcdCert_checks [LawfulGcdOps R] [LawfulBezoutOps R] :
    checkGcd f h (gcdCert f h) = true
theorem gcd_dvd_left [LawfulGcdOps R] [LawfulBezoutOps R] : gcd f h ∣ f
theorem gcd_dvd_right [LawfulGcdOps R] [LawfulBezoutOps R] : gcd f h ∣ h
theorem dvd_gcd [LawfulGcdOps R] [LawfulBezoutOps R] :
    d ∣ f → d ∣ h → d ∣ gcd f h
theorem gcd_normalized [LawfulGcdOps R] [LawfulBezoutOps R] :
    normalize (gcd f h) = gcd f h
theorem cofactors_spec [LawfulGcdOps R] [LawfulBezoutOps R] :
    f = gcd f h * (cofactors f h).1 ∧ h = gcd f h * (cofactors f h).2
theorem cofactors_coprime [LawfulGcdOps R] [LawfulBezoutOps R] :
    ∀ d, d ∣ (cofactors f h).1 → d ∣ (cofactors f h).2 → GcdOps.isUnit d = true
theorem isCoprime_iff [LawfulGcdOps R] [LawfulBezoutOps R] :
    isCoprime f h = true ↔ ∀ d, d ∣ f → d ∣ h → GcdOps.isUnit d = true
theorem gcdList_dvd [LawfulGcdOps R] [LawfulBezoutOps R] :
    p ∈ ps → gcdList ps ∣ p
theorem dvd_gcdList [LawfulGcdOps R] [LawfulBezoutOps R] :
    (∀ p ∈ ps, d ∣ p) → d ∣ gcdList ps
theorem dvd_lcm_left [LawfulGcdOps R] [LawfulBezoutOps R] : f ∣ lcm f h
theorem dvd_lcm_right [LawfulGcdOps R] [LawfulBezoutOps R] : h ∣ lcm f h
theorem lcm_dvd [LawfulGcdOps R] [LawfulBezoutOps R] :
    f ∣ m → h ∣ m → lcm f h ∣ m
theorem lcm_normalized [LawfulGcdOps R] [LawfulBezoutOps R] :
    normalize (lcm f h) = lcm f h
```

Degenerate contracts are `gcd 0 0 = 0`, `gcd f 0 = normalize f`,
`gcd f h = 1` whenever either side is a unit, `gcdList [] = 0`, and
`lcm f 0 = lcm 0 f = 0`. Each has a matching certificate case above.
The library installs `GcdOps (MvPoly n R cmp)` and its
`LawfulGcdOps` instance from these theorems. The low-priority backend is
always the deterministic fallback, so downstream generic code cannot
accidentally select the integer modular algorithm for an abstract ring.

**Normalisation depends on the monomial order, over `ℤ` as well.** `gcd`
returns the associate whose leading coefficient in `cmp` order is
`normalize`d. This is **not** order-independent over `ℤ`, although the
argument that it should be is tempting: negation does flip the sign of
every coefficient at once, but *which* coefficient is leading changes
with the order, and the two leading coefficients can have different
signs.
For `x - y`, an order with `x` leading normalises to `x - y`, and an
order with `y` leading sees leading coefficient `-1` and normalises to
`y - x`. So there is one transport lemma, not two, and it states the
coefficient-unit witness explicitly:

```lean
theorem gcd_reorder :
    ∃ u v : R, u * v = 1 ∧
      gcd (reorder f) (reorder h) = reorder (gcd f h) * C u
```

An order-independent normalisation would have to fix the sign from
something other than the `cmp`-leading coefficient (the sign of the
coefficient of the lex-least monomial, say). Whether that is worth
having is under "Open questions"; it is not assumed anywhere above.

**Rational coefficients.** Over `ℚ` the content is always a unit, so
`primPart` is useless and the coefficient swell in a PRS is maximal.
`gcdCert` on `MvPoly n Rat cmp` scales both inputs to primitive integer
polynomials, computes there, and scales back. Its cofactor certificate is
`ratLift` with the two nonzero scales, the primitive integer models, and
their checked integer coprimality certificate. This is a requirement
rather than an option, and the benchmark family named below checks that
the extended PRS is not taken merely because the input coefficients are
rational.

## The algorithms

Every route produces a candidate `GcdCert`, and `gcdCert` accepts it only
through `checkGcd`. Rejection falls through to the next route. The last
route is the one whose success must be proved.

**One statement to keep straight throughout.** Trial division shows a
candidate is *a* common divisor. It does not show the candidate is the
greatest one: `1` divides both inputs too. Every stopping rule below is
therefore "stop when `checkGcd` accepts", never "stop when the candidate
divides both inputs". Producing the coprimality witness is part of the
stopping test, and in the modular routes it is nearly free, because the
univariate image gcds the route already computed are exactly what the
`split` constructor needs.

### 0. Structural reductions, always applied

Zero and unit inputs return immediately with the certificate cases named
above. Then, in order: divide out the monomial content of each input and
put the monomial gcd into the answer; divide out the `R`-content of each
input and put `GcdOps.gcd` of the two contents into the answer. Each is
linear in the term count and strictly shrinks the problem without changing
the certificate's arity. Restricting to `vars f ∩ vars h` is deferred until
there is a specified certificate re-embedding operation.

### 1. Coprime detection, the case that dominates

`tryCoprimeCert?` runs, per variable, one evaluation and one univariate
gcd: pick a prime and a random point for all remaining variables,
check the degrees survive, and compute `gcd` in `FpPoly p`. A result of
`1` yields the `split` constructor and the recursion continues on the
contents one arity down. A result other than `1` proves
nothing (the point may be unlucky) and the route falls through.

That asymmetry is the point: the cheap test is conclusive exactly in the
case that occurs most often. The cost is up to one image gcd per
variable, not one in total.

The public `isCoprime` remains the exact wrapper specified above. The
requirement this route places on the implementation is that `gcd f h` must
not compute an interpolation when `f` and `h` are coprime. The benchmark
family "coprime pairs" checks it.

### 2. The heuristic gcd

Evaluate every variable at a single large integer under a **collision-free
mixed-radix (Kronecker) substitution**: with `dⱼ` a bound on the degree
in `xⱼ`, substitute `xⱼ ↦ ξ^(∏_{k<j} (d_k + 1))`. Substituting successive
powers `ξ, ξ², ξ³, …` is wrong, because `x₂` and `x₁²` then receive the
same value and their coefficients add. Take the integer gcd of the two
values with hex-arith's `Int.gcd`, reconstruct a polynomial from the
symmetric mixed-radix digits, take the primitive part, and offer the
result to `checkGcd`.

Two things about this route are easy to state too strongly.
Reconstruction being exact does **not** follow from the input
coefficient sizes: the
input norms do not bound the gcd's coefficients, and the integer gcd may
carry accidental common factors contributed by the evaluated cofactors
rather than by the true gcd. So `ξ` chosen from the input norms is a
heuristic for the success *rate* and nothing is proved from it. The
route proposes a candidate; `checkGcd` decides. A correct proof of the
multivariate heuristic needed a published correction, which is worth
reading before implementing:
[Parisse, "A correct proof of the heuristic GCD algorithm"](https://arxiv.org/abs/cs/0206032).

Retries must be budgeted by projected bit size rather than by a fixed
count. The evaluation point is `ξ^(∏(dⱼ+1))`-sized, so six unconditional
retries with `ξ ← ξ · ⌊√ξ⌋` can build enormous integers before Brown is
ever attempted. The route declines when the projected bit size exceeds
its budget, which is also why it degrades to inapplicable as the number
of variables grows.

### 3. Brown's dense modular algorithm

Two nested evaluation and reconstruction schemes: primes with CRT for the
integer coefficients, and points with dense interpolation for each
variable.

Fix the main variable `i`. Recursion on the remaining variables:

- Reduce both inputs modulo a prime `p` chosen so that the leading
  coefficients in `xᵢ` do not vanish.
- Compute the gcd of the images at each evaluation point `a` for the
  outermost remaining variable.
- **Leading-coefficient correction.** The image gcd is monic and the
  true gcd is not. Compute `γ` as the gcd of the two `DensePoly.leadingCoeff`s
  of `toUnivariate i cmp' f` and `toUnivariate i cmp' h`
  recursively, and scale each image gcd so that its leading coefficient
  in `xᵢ` equals `γ` evaluated at that point. Interpolating uncorrected
  images gives the wrong polynomial.
- **Rejected points** are of two kinds and both must be handled.
  *Bad* points are those where a leading coefficient of an input
  vanishes, or where `γ(a) = 0`, which makes the correction meaningless;
  skip them. *Unlucky* points are those where the image gcd has larger
  degree than the true gcd; detect them by comparing degrees across
  points, keep the images of minimal degree, and restart the
  interpolation whenever a smaller degree appears.
- Interpolate in the outermost remaining variable, take the primitive
  part in `xᵢ`, and multiply back the content gcd.

The prime layer needs the same machinery, one level up: primes must
preserve the input degrees, primes giving a larger modular gcd degree
are unlucky and are discarded with a restart,
primes at which the normalisation data vanish are rejected, and the
support of the reconstructed gcd must stabilise before CRT can be
trusted. Ansari and Monagan set out the three-way distinction between
leading-coefficient-bad, unlucky, and zero-divisor points, and the
scaling by the evaluated leading-coefficient gcd, at
[CASC 2023, pp. 8-10](https://www.cecm.sfu.ca/personal/mmonagan/papers/MahsaCASC23.pdf).

Choosing `i` to have the smallest positive degree reduces the cost of
each univariate image gcd. It does **not** minimise the number of images:
that count is governed by the degrees in the evaluated variables, not by
the main variable.

**On coefficient bounds.** No multivariate Mignotte or Gelfond bound is
needed for soundness, and none is needed for the dispatcher to be total,
because this route carries fuel and falls through to route 4. A bound
*is* what would prove that this route itself eventually succeeds:
`checkGcd` recognises the right answer once the modulus is large enough
and the support has stabilised, but it does not prove that either happens.
Route 3 is therefore specified without a completeness theorem, which is
consistent with its being one of the unverified producers.

### Future extension: Zippel's sparse interpolation

Learn the skeleton (which monomials appear in each coefficient of the
gcd) from one dense image, then determine the coefficients at later
points by solving transposed Vandermonde systems at powers of a random
point, which costs `O(t²)` for `t` terms rather than `O(t³)`.

One image does not reliably learn the skeleton, and a usable sparse gcd
needs more than the sketch above: a term bound or an early-termination
criterion, diversification so that distinct terms are distinguishable,
a field large enough (or an extension) for the random points, collision
handling, and a normalisation strategy for the nonmonic case. Huang and
Gao set out a modern version with those pieces at
[arXiv:2207.13874](https://arxiv.org/abs/2207.13874).

The paragraph above is a research direction, not an implementable route
contract. Zippel is therefore outside the core dispatch and milestones.
Adding it requires a separate SPEC amendment that fixes the term bound or
early-termination theorem, diversification, field-size policy, collision
handling, and restart semantics before assigning it performance claims.

The random point is an explicit argument rather than a monad, following
the pattern [hex-finite-field](hex-finite-field.md) sets under
"Randomness", and drawn from the `Hex.Rand` generator that SPEC
introduces.

### 4. The extended-subresultant fallback

Recurse on the arity. In the main variable `xᵢ`, run
the required `subresultantChainExt` over the coefficient ring
`MvPoly n R cmp'`. Write its terminal nonzero identity as
`U · f + V · h = S`, take `g = primPartIn i cmp' S` once, and obtain the
candidate cofactors `f'` and `h'` by checked exact division. Since
`S = constIn i cmp' c · g` for `c = contentIn i cmp' S`, substituting
`f = g · f'` and `h = g · h'` into the identity and cancelling the
nonzero `g` gives `U · f' + V · h' = constIn i cmp' c`. The terminal
entry is nonzero, so `c ≠ 0`; this is exactly the mandatory
`splitBezout` witness. Multiply the candidate by the recursively
certified gcd of the input contents when rebuilding the structural
reductions.

Running the subresultant chain while taking the primitive part of each
remainder is a third thing, and not a correct one. The subresultant
recurrence's exact divisions are justified by scale
invariants that primitive-part removal destroys, so a primitive PRS is a
separate recurrence with its own completeness theorem, not a variant of
Brown's chain. This SPEC extends Brown's chain only by tracking its
transformation; it does not change the remainder recurrence. The cost is
the coefficient swell inside the chain that a separately proved primitive
PRS would avoid, and that is acceptable because this route exists to be
complete rather than fast.

It is deterministic, needs no prime, no point, and no random draw, and it
is what proves the `gcdCert_checks` postcondition stated with the public
API.

The totality obligation is concentrated in acceptance of route 4 and the
exact transformation invariant supplied by `subresultantChainExt`.
Semantic gcd contracts then combine that accepted certificate with checker
soundness and the independent Gauss/common-factor theorem. Routes 1
through 3 need no correctness proof at all, which is the whole reason for
the architecture.

### Routes not specified here

Neither Zippel interpolation nor sparse Hensel lifting is specified as a
core route. Until one receives its own complete amendment, the performance
claim against FLINT is "competitive on the dense and coprime families",
not "approaching FLINT in general", and the benchmark section says so.

## Squarefree decomposition

### What squarefree means here

Over a field, "no square of a nonunit divides `p`" is the whole story.
Over `ℤ` it is not, and the distinction has to be made before any
signature is written. `12x` is not squarefree in `ℤ[x]`, because
`4 ∣ 12`, so the ring-theoretic predicate over `ℤ[x₁, …, xₙ]` is partly a
question about the integer content. The Mathlib companion can decide that
scalar predicate without factoring the integer; the Mathlib-free API here
deliberately specifies only the polynomial-part convention below.

This library therefore uses the standard computer-algebra convention,
which is also what `HexPolyZ.primitiveSquareFreeDecomposition` and
SymPy's `sqf_list` do: the coefficient content comes out as a scalar and
is not factored, and squarefreeness is a statement about the polynomial
part.

```lean
/-- `p` has no variable in its support. -/
def IsConst (p : MvPoly n R cmp) : Prop := p.vars = []

/-- Every repeated divisor of `p` is a constant. Equivalently, `p` is
squarefree in `K[x₁, …, xₙ]` for `K` the fraction field of `R`. Over a
field this is the ring-theoretic predicate; over `ℤ` it is weaker, and
deliberately so. -/
def Squarefree (p : MvPoly n R cmp) : Prop :=
  p ≠ 0 ∧ ∀ d, d * d ∣ p → IsConst d

/-- Mathlib-free characteristic zero: every positive natural remains
nonzero after casting to `R`. -/
class NatNoZero (R : Type u) [Zero R] [NatCast R] : Prop where
  natCast_ne_zero : ∀ m : Nat, 0 < m → (m : R) ≠ 0

/-- The fraction field used to interpret the relative squarefree predicate
is perfect. Instances cover characteristic zero fields and finite fields. -/
class PerfectFrac (R : Type u) [Lean.Grind.CommRing R] [Div R]
    [ExactDivLaws R] [Fraction.NonzeroOne R] : Prop where
  charZeroOrPerfect :
    (∀ m : Nat, 0 < m → (m : Fraction R) ≠ 0) ∨
    ∃ p : Nat, Nat.Prime p ∧ (p : Fraction R) = 0 ∧
      ∀ a : Fraction R, ∃ b : Fraction R, b ^ p = a

structure SqfFactor (n : Nat) (R : Type u) (cmp : Mono n → Mono n → Ordering) where
  factor       : MvPoly n R cmp
  multiplicity : Nat

structure SqfDecomp (n : Nat) (R : Type u) (cmp : Mono n → Mono n → Ordering) where
  content : R
  factors : List (SqfFactor n R cmp)

def sqfDecomp [NatNoZero R] (p : MvPoly n R cmp) : SqfDecomp n R cmp
def radical [NatNoZero R] (p : MvPoly n R cmp) : MvPoly n R cmp
def isSquarefree (p : MvPoly n R cmp) : Bool
```

The scalar field is `content : R`, not `unit : R`. For `p = 6` at arity
zero, `⟨6, []⟩` is the answer, and `6` is not a unit in `ℤ`. Calling the
field `unit` and asserting that it is one is false for every input with
nonunit content.

The naming follows `FpPoly.SquareFreeFactor` and
`FpPoly.SquareFreeDecomposition` in hex-poly-fp, so a reader who knows
the univariate case reads the multivariate one without translation. The
univariate precedent for the relative predicate is
`HexPolyZ.SquareFreeRat`.

### The decision procedure

Over a field whose characteristic is zero or whose characteristic is `p`
and which is perfect,

```
p is squarefree  ↔  gcd(p, ∂₁p, …, ∂ₙp) is a unit
```

in **both** directions and in **both** characteristics, using all `n`
partial derivatives rather than one. The forward direction is immediate.
For the converse, let a nonunit `d` divide both the input and all its
derivatives, and write the input as `d · e`. If `d` and `e` have a
nonunit common divisor `k`, then `k²` divides the input and it is not
squarefree. Otherwise `CoprimeCancelLaws` applied to
`d ∣ ∂ⱼd · e` gives `d ∣ ∂ⱼd`, so every `∂ⱼd` is zero by degree. In
characteristic zero that makes `d` constant, a contradiction. In perfect
characteristic `ℓ`, it makes `d = q^ℓ`; a nonunit `q` then has `q²`
dividing the input. This factor-free proof uses the Gauss/common-factor
layer already scheduled and does not assume a UFD or irreducible
factorization API.

Over `ℤ` the test is applied to the primitive part, and that is exactly
what the CAS convention above buys. For `p = 2x`, `gcd(2x, 2) = 2` is not
a unit even though `2x` has no nonconstant repeated divisor, so applying
the test to `p` itself reports "not squarefree" and the radical formula
returns `x`, silently dropping the factor `2`. `primPart (2x) = x` and
`gcd(x, 1) = 1` give the right answer. Primitivity
also makes the test exact rather than approximate: a nonunit constant in
the gcd would divide the primitive part, which is impossible.

```lean
def isSquarefree p := GcdOps.isUnit (gcdList (primPart p :: derivatives (primPart p)))
```

**`radical` is characteristic-zero only.** The identity
`gcd(p, ∂₁p, …, ∂ₙp) = ∏ dᵢ^(eᵢ - 1)` requires the characteristic not to
divide any `eᵢ`. In characteristic `3`, `p = x³` has all derivatives zero,
so the gcd is `x³` and the formula returns `1` instead of `x`. The
signature carries the hypothesis. No positive-characteristic `radical`
operation is exposed until the future decomposition is specified.

```lean
theorem isSquarefree_iff [PerfectFrac R] :
    isSquarefree p = true ↔ Squarefree p
theorem radical_squarefree [NatNoZero R] (hp : p ≠ 0) : Squarefree (radical p)
theorem radical_dvd [NatNoZero R] : radical p ∣ p
theorem radical_zero [NatNoZero R] : radical (0 : MvPoly n R cmp) = 0
```

`NatNoZero R` asserts `(m : R) ≠ 0` for `0 < m`, which is characteristic
zero stated Mathlib-free, with instances for `Int` and `Rat`.
`PerfectFrac R` asserts that the fraction field of `R` is perfect, which
holds in characteristic zero and for finite fields, and fails for
`F_p(t)`.

### The decomposition in characteristic zero

Recursion on the arity.

- Zero and constant inputs return `⟨p.constCoeff, []⟩`.
- Split off the `R`-content into the `content` field.
- Pick a variable `i` with `degreeOf i p > 0`.
- Split `p = contentIn i p * primPartIn i p` and decompose the content
  recursively with `i` removed.
- Run Yun's algorithm on `primPartIn i p` with the derivative in `xᵢ`.
- Merge by multiplying factors of equal multiplicity.

```
b₁ ← primPartIn i p / a          where a = gcd(p, ∂p/∂xᵢ)
c₁ ← (∂p/∂xᵢ) / a
d₁ ← c₁ - ∂b₁/∂xᵢ
loop k:  aₖ ← gcd(bₖ, dₖ)        -- the multiplicity-k factor, possibly 1
         bₖ₊₁ ← bₖ / aₖ
         cₖ₊₁ ← dₖ / aₖ
         dₖ₊₁ ← cₖ₊₁ - ∂bₖ₊₁/∂xᵢ
until bₖ is a unit
```

The loop runs one gcd **per level** `k = 1, 2, 3, …` up to the maximum
multiplicity present, emitting `aₖ = 1` at absent levels. It is not one
gcd per distinct multiplicity: an input with a single factor of
multiplicity 7 runs seven iterations, which is what the complexity table
below counts. Yun is still preferred to Musser's variant because the
inputs shrink.

The accumulation discipline from hex-poly-fp applies: build the factor
list with `Array.push` or cons-then-reverse, never `acc ++ [x]`, and take
powers by square-and-multiply.

**Why the content split suffices.** Every repeated factor of
`primPartIn i p` involves `xᵢ`: a repeated factor not involving `xᵢ`
would have its square dividing the content, contradicting primitivity. In
characteristic zero such a factor has nonzero derivative in `xᵢ`, so
`∂/∂xᵢ` detects exactly the repeated factors of the primitive part, and
every other repeated factor is inside the content and is found one
variable down. The two families are automatically coprime, so the merged
decomposition needs no further gcd.

### Future extension: decomposition in positive characteristic

Full positive-characteristic decomposition is deliberately not part of
this library version. A one-variable Yun generalisation is unsound for
multivariate input: over `F_p[x,y]`, `(x^p+y)² · (x+y^p)²` has repeated
factors that require different derivative variables, and the recursive
coefficient ring is not perfect even when the ground field is. The core
therefore exposes only `isSquarefree` in perfect characteristic and keeps
`sqfDecomp` and `radical` behind `NatNoZero`.

A later amendment should follow Gianni and Trager, "Square-free algorithms
in positive characteristic" (AAECC 7, 1996), and must specify the
multi-derivative partition, coefficient Frobenius roots, termination, and
merge contracts before adding an API or milestone. `pthRootIn?`,
`PerfectOps`, and positive-characteristic decomposition files are not
reserved by this SPEC.

### Contract theorems

```lean
theorem sqfDecomp_prod :
    (sqfDecomp p).factors.foldl (fun acc f => acc * f.factor ^ f.multiplicity)
      (C (sqfDecomp p).content) = p
theorem sqfDecomp_squarefree : ∀ f ∈ (sqfDecomp p).factors, Squarefree f.factor
theorem sqfDecomp_primitive  : ∀ f ∈ (sqfDecomp p).factors, content f.factor = 1
theorem sqfDecomp_coprime :
    ∀ f ∈ (sqfDecomp p).factors, ∀ g ∈ (sqfDecomp p).factors,
      f.multiplicity ≠ g.multiplicity →
        ∀ d, d ∣ f.factor → d ∣ g.factor → GcdOps.isUnit d = true
theorem sqfDecomp_multiplicity_pos, sqfDecomp_multiplicity_sorted
theorem sqfDecomp_nonconstant :
    ∀ f ∈ (sqfDecomp p).factors, ¬ IsConst f.factor
```

Multiplicities are positive, pairwise distinct, and returned in
increasing order. Factors are primitive and nonconstant, which is what
makes the content field carry all the coefficient information. The zero
input returns `⟨0, []⟩`.

There is no `sqfDecomp_content_isUnit`. Uniqueness of the decomposition
up to units is a companion theorem because it is most naturally stated
through Mathlib's unique-factorization API; gcd maximality itself is
already Mathlib-free.

## Complexity

These are **probe counts**, not operation counts: they count image gcds,
evaluations, and coefficient gcds rather than machine operations, and
they omit the cost of each probe. A full cost model would have to
multiply through by the univariate gcd, interpolation, and CRT costs at
every level, and this SPEC does not attempt one.

Parameters: `n` variables, `t` terms in the larger input, `d` the maximum
degree in any one variable, `D = ∏(dᵢ + 1)` the
dense size, and `M` the maximum multiplicity in a squarefree
decomposition.

| operation | algorithm | probe count |
|---|---|---|
| `monoContent` | `Mono.gcd` fold over the support | `O(n · t)` machine ops |
| `content` | `GcdOps.gcd` fold | `t` coefficient gcds |
| `toUnivariate` | partition by the exponent of `xᵢ` | `O(n · t log t)` machine ops |
| `contentIn` | `d` gcds on polynomials of `t/d` terms | `d` recursive gcds |
| `divExact?` | leading-monomial cancellation, early failure | `O(n · t_q · t_g · log)` machine ops |
| `tryCoprimeCert?` | one image gcd per variable | `≤ n` image gcds |
| `isCoprime` | exact checked gcd followed by a unit test | dispatcher-dependent |
| heuristic gcd | one `Int.gcd`, integers of `O(t · log ξ · ∏(dⱼ+1))` bits | 1 integer gcd |
| Brown | one image gcd per evaluation point, per prime | `O(D)` image gcds |
| extended PRS | subresultant chain, primitive part once | no useful bound |
| `sqfDecomp` | one gcd per level per variable | `O(n · M)` gcds |
| `radical` | gcd of `p` and `n` derivatives | `n` gcds |

The table makes the dispatch order argument: route 1 costs at most `n`
probes and settles the most common input, route 2 costs one and settles
small inputs, route 3 is bounded by the dense size, and route 4 has no
useful bound and settles the rest.

## Kernel exposure

The kernel replay closure is `checkGcd`, `checkCoprime`, `checkContent`,
and what they call: polynomial multiplication and equality from
hex-mv-poly, `toUnivariate`, `imageAt`, `constIn`, `mapCoeffs`, `eval`,
and `FpPoly` multiplication, addition, degree, and equality. It does not
contain `contentIn`, `gcd`, any `GcdProducer`, or `divExact?`; nested
`ContentCert` and `GcdCert` values carry all producer results needed for
replay. The closure also includes `polyIsUnit`, `polyNormUnit`,
`polyNormalize`, base `GcdOps.isUnit` / `normUnit`, and the coefficient
equality decision (`BEq` with `LawfulBEq`). `ratLift` additionally reaches
the `scalarContent` fold and coefficientwise `Int → Rat` map, neither of
which calls a multivariate producer. Each operation in the closure is
`@[expose]`.

Nothing in routes 1 through 4 is in that closure. Prime search,
interpolation, CRT, and the extended subresultant chain are search; they
never appear in a proof term and should not pay for exposure.

The `cancel` tactic narrows the closure further: its soundness needs the
two cofactor identities and the denominator hypothesis, so the
coprimality half of the certificate can be checked at elaboration time
without entering the proof term. Whether that is worth a separate code
path is under "Open questions".

`Mono` construction and equality reach the same two shims hex-mv-poly
documents (`HexBasic.ArrayDecEq` and `Hex.Vector.ofFn'`, both standing in
for [leanprover/lean4#14270](https://github.com/leanprover/lean4/pull/14270)),
so this library inherits the dependency on `HexBasic` through hex-mv-poly
rather than acquiring a new one.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexMvGcd/EmitFixtures.lean` exposed as
`lean_exe hexmvgcd_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexMvGcd/mvgcd.jsonl`, and an oracle driver at
`scripts/oracle/mvgcd_sympy.py`. One tuple appended to `ORACLES` in
`scripts/ci/run_oracles.sh`, not a new job:

```
"HexMvGcd|hexmvgcd_emit_fixtures|scripts/oracle/mvgcd_sympy.py|conformance-fixtures/HexMvGcd/mvgcd.jsonl"
```

Three fixture kinds. `mvgcd` carries the arity, the comparator name, the
coefficient domain, and two term lists, and its result records the gcd
and both cofactors. `mvsqf` carries one term list and its result records
the content and the `(factor, multiplicity)` list. `mvsquarefree` records
the exact Boolean decision and is the only positive-characteristic
squarefree fixture kind. All three reuse the
`(exponent vector, coefficient)` encoding hex-mv-poly's `mvpoly` fixture
kind defines, so one fixture parser serves all three.

**The oracle suite alone cannot catch the bugs this library is most
likely to have.** Every route's candidate goes through `checkGcd`, and a
rejected candidate falls through to route 4, which returns the right
answer. So an end-to-end fixture passes even if Brown's
leading-coefficient correction is inverted or its bad-point test never
fires. Oracle fixtures check the public
answer; they do not check that any route worked.

The suite therefore has two halves.

**Route-level tests**, in Lean, invoking each producer directly and
asserting on its internals: that the candidate it produced was accepted;
that the intended route succeeded before the fallback ran; that a
constructed bad point or unlucky prime was actually rejected; and that
the interpolation restarted when a smaller image degree appeared. These
are the tests that fail when a route regresses, and they are worth more
than the oracle half.

**Oracle fixtures**, which check the public answer. Cases that must be
present:

- `gcd 0 0`, `gcd f 0`, `gcd f 1`, and gcds of constants.
- Coprime pairs of every size, checking the answer is `1` and the
  cofactors are the inputs.
- A gcd that is a pure monomial, so `monoContent` carries the answer.
- A gcd of degree zero in the chosen main variable, so the answer comes
  entirely from the content recursion.
- Inputs whose gcd is not monic in the main variable and whose leading
  coefficient is a nonconstant polynomial in the other variables.
- Inputs where a leading coefficient, or `γ`, vanishes at a small point.
- Inputs where a small point makes the image gcd larger than the true
  gcd (construct these by making the resultant of the cofactors vanish
  at the point), and the same one level up for an unlucky prime.
- Inputs designed for coefficient swell in the PRS route.
- Squarefree cases: high multiplicity (`g^7 · h`), a multiplicity gap
  (`g · h^5`), repeated factors living entirely in the content, repeated
  factors involving every variable, and a squarefree input.
- **Content cases over `ℤ` specifically**: `2x`, `12x`, `6`, and
  `4x² + 4x`, which are the inputs that distinguish this library's
  squarefree convention from the ring-theoretic predicate.
- Positive-characteristic `mvsquarefree` cases: `x^p + y` (squarefree,
  one vanishing derivative, not a `p`-th power), `(x^p + y)²`, `g^p`,
  and `(x^p+y)² · (x+y^p)²`. No positive-characteristic `mvsqf` fixture
  exists until that decomposition is specified.
- Arity zero and arity one, where the answers must agree with `Int.gcd`
  and with hex-poly's univariate `gcd`. The arity-one agreement is
  checked in Lean rather than against the oracle, since both sides are
  ours.

**Oracle choice.** SymPy's `gcd`, `cofactors`, `sqf_list`, and `sqf_part`
cover the decomposition surface over `ℤ` and `ℚ`, and its `modulus=`
argument covers the positive-characteristic Boolean cases above. Extension
fields `F_q` are not covered by SymPy and are out of scope for the
oracle; `GFq` Boolean cases are checked in Lean, with their arity-one
specializations compared to hex-poly-fp. python-flint's `fmpz_mpoly.gcd` is a
stronger implementation but does not expose cofactors or squarefree
decomposition uniformly, so it appears below as a performance comparator
rather than as the oracle.

The companion adds randomised comparison against
`MvPolynomial (Fin n) ℤ` through hex-mv-poly's `equiv`, checking the
divisibility and coprimality statements directly rather than through the
oracle's normalisation conventions.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexMvGcd/Bench.lean`. Native only for throughput. A separate
`bench/HexMvGcd/Kernel.lean` suite replays valid and one-field-corrupted
certificates through `by decide +kernel`: base, modular split,
`splitBezout`, `ratLift`, nested content folds, zero, and unit cases. Hex-mv-poly's
kernel suite cannot substitute for this recursive checker coverage.

Families chosen to isolate each core route and to expose the known sparse
gap:

- **Coprime pairs**, 2 to 8 variables, dense and sparse. Decides whether
  route 1 works. The required property is that the time is a small
  multiple of the time to evaluate the inputs `n` times. A regression
  means an interpolation is running when it should not.
- **Dense gcds**, 3 to 5 variables, degree 5 to 20 in each. Route 3.
- **Sparse stress**, 5 to 12 variables, high degree, few terms. This
  records the known gap while no sparse route is specified; it does not
  claim to isolate a route.
- **Swell cases**, small inputs whose subresultant remainder sequence has
  enormous coefficients. Route 4, and the argument for having the others.
- **Rational coefficients**, the same inputs over `ℚ`, checking the
  clear-denominators step happens. Times should track the `ℤ` family.
- **Squarefree decomposition**, multiplicity patterns `1`, `1..5`, `7`,
  and `2,3,5,7`, in 2 to 5 variables. The `7` pattern is there because
  Yun runs one level at a time.
- **Cofactor-heavy**, where the gcd is small and the cofactors are large,
  which stresses `divExact?` rather than the interpolation.

**Comparators.** FLINT's `fmpz_mpoly_gcd` is `informational`. It selects
among Brown, Zippel, a sparse Hensel route, and subresultants with tuned
crossovers, while this library specifies Brown and the subresultant
fallback. A required broad ratio would therefore be a check on routes that
do not exist. The written-down
expectation is therefore narrow: on the **coprime**
family the ratio should be within a small constant, since both sides do
one evaluation and one univariate gcd per variable, and a large ratio
there means the fast path is not firing. No advance claim is made on the
sparse family, where FLINT's Hensel route has no counterpart here.
Singular is `informational` for the same reason. SymPy is the oracle and
is not a performance comparator.

## The Mathlib layer

`hex-mv-gcd-mathlib` transports the Mathlib-free soundness and maximality
theorems; it does not supply a missing gcd-domain hypothesis. Writing `e`
for hex-mv-poly's
`equiv : MvPoly n R cmp ≃+* MvPolynomial (Fin n) R`:

```lean
theorem gcd_dvd_left  : e (gcd f h) ∣ e f
theorem gcd_dvd_right : e (gcd f h) ∣ e h
theorem dvd_gcd (d) : d ∣ e f → d ∣ e h → d ∣ e (gcd f h)
theorem gcd_normalized : normalize (e (gcd f h)) = e (gcd f h)

theorem contentIn_dvd_coeff (k) :
    e (contentIn i cmp' p) ∣ e ((toUnivariate i cmp' p).coeff k)
theorem dvd_contentIn (d) :
    (∀ k, d ∣ e ((toUnivariate i cmp' p).coeff k)) → d ∣ e (contentIn i cmp' p)

theorem squarefree_spec :
    Hex.MvPoly.Squarefree p ↔ _root_.Squarefree (e (primPart p))
theorem sqfDecomp_unique : ...   -- up to units, from unique factorization
```

Mathlib has `Polynomial.content` for `R[X]` over a `NormalizedGCDMonoid`
and no multivariate counterpart, so the content correspondence is the two
divisibility facts rather than an equation between named contents.

`dvd_gcd` is proved in the core and merely mapped through `e`. Mathlib's
`MvPolynomial.uniqueFactorizationMonoid` is used for squarefree
correspondence and decomposition uniqueness, not to repair gcd
maximality. Mathlib has no `NormalizedGCDMonoid (MvPolynomial σ D)`
instance, so the transported gcd statements remain in terms of
divisibility; an `Associated` version follows from the three facts.

`squarefree_spec` relates this library's relative predicate to Mathlib's
`Squarefree` **on the primitive part**, which is the honest statement.
The decidability instances follow that split:

```lean
instance : Decidable (a ∣ b)          -- MvPolynomial (Fin n) ℤ
instance : Decidable (Squarefree p)   -- MvPolynomial (Fin n) ℚ
instance : Decidable (Squarefree p)   -- MvPolynomial (Fin n) ℤ
```

Divisibility is decidable over `ℤ` because it is exactly `divExact?`.
Over `ℚ` the content is a unit and the relative and ring-theoretic
predicates agree. Over `ℤ`, the instance combines the checked primitive
part with Mathlib's decision procedure for squarefreeness of the integer
content (`DecidablePred (Squarefree : ℕ → Prop)`). What
[hex-int-factor](hex-int-factor.md) adds is the square divisor and the
squarefree part as witnesses, which the decision procedure does not
produce.

Following the project split, no mathematical theorem about `MvPoly`
belongs in the companion beyond these, plus one correspondence lemma per
public semantic operation: `gcd`, `cofactors`, `contentIn`, `primPartIn`,
`radical`, `sqfDecomp`, and `divExact?`.

## Milestones

1. **Prerequisite and coefficient kernel.** Land
   `Hex.Resultant.subresultantChainExt` with its transformation and exact
   division proofs. Then implement `GcdOps`, `BezoutOps`,
   `LawfulGcdOps`, `LawfulBezoutOps`, `CoeffHom`, `divMod`,
   `divExact?`, the `Dvd` / `Div` / `ExactDivLaws` instances, `constIn`,
   `polyIsUnit`, `polyNormUnit`, `polyNormalize`, `scalarContent`, and the
   base coefficient instances. The `Lean.Grind.CommRing` tower and
   `mapCoeffs` are already in
   hex-mv-poly, so hex-resultant's chain runs over `MvPoly` with its
   correctness theorems applying as soon as `Div` and `ExactDivLaws`
   land here.

2. **Proof-only Gauss and common-factor algebra.** Starting from
   `GcdDomainLaws R`, implement the finite existential coefficient-gcd
   fold, fraction-field polynomial embedding, primitive descent, and the
   arity lifts of `GcdDomainLaws` and `CoprimeCancelLaws`. This milestone
   defines no executable multivariate content or gcd, contains no checker,
   and calls no candidate route; its end theorem is exactly the
   common-factor step maximality will consume.

3. **Certificates and the complete fallback.** `ContentCert`,
   `CoprimeCert` (including `ratLift`), `GcdCert`, all three checkers, the
   executable `monoContent` / content / primitive-part operations and
   their Gauss laws, the simultaneous soundness induction, and route 4.
   End with a correct deterministic producer,
   the public gcd/cofactor/list/lcm contracts, `gcdCert_checks`, and the
   kernel replay suite. This is the first usable core release.

4. **Characteristic-zero squarefree operations.** Yun with content
   recursion, `radical`, `isSquarefree`, their contracts, and oracle
   fixtures. Positive-characteristic decomposition remains outside scope.

5. **The fast paths.** Routes 0, 1, and 2, with explicit `GcdConfig` and
   concrete producers. This is where `cancel` becomes practical on its
   dominant coprime workload, and it needs no new soundness proofs.

6. **Brown.** Route 3, with leading-coefficient correction and the point
   and prime handling. The route-level tests for those traps are written
   before the code.

7. **The companion.** Transport, squarefree correspondence, uniqueness,
   and the divisibility plus `ℚ` and `ℤ` squarefree decidability instances.
   It can begin after milestone 3; gcd maximality is already available in
   the Mathlib-free library.

## File organisation

```
HexMvGcd/
  Coeff.lean        -- GcdOps/BezoutOps and lawful classes, CoeffHom, instances
  Divide.lean       -- divMod, divExact?, Dvd/Div/ExactDivLaws
  View.lean         -- constIn and the degree helpers on the univariate view
  Normalize.lean    -- polyIsUnit, polyNormUnit, polyNormalize, scalarContent
  Gauss.lean        -- proof-only GcdDomainLaws lift and primitive descent
  Cert.lean         -- three certificate types, ratLift, checker soundness
  Content.lean      -- certificate-producing content/primitive parts and Gauss laws
  Prs.lean          -- the extended-subresultant fallback, route 4
  Fast.lean         -- routes 0 and 1, tryCoprimeCert?
  Heu.lean          -- route 2, the Kronecker substitution and its budget
  Brown.lean        -- route 3
  Gcd.lean          -- config/backends, dispatch, public API, GcdOps instance
  Squarefree.lean   -- Yun, the content recursion, radical, isSquarefree
HexMvGcd.lean
HexMvGcdMathlib/
  Gcd.lean          -- transport of divisibility and Associated statements
  Squarefree.lean   -- Squarefree correspondence and uniqueness
  Decide.lean       -- divisibility and ℚ/ℤ squarefree decisions
HexMvGcdMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexMvGcd:
    deps: [HexBasic, HexMvPoly, HexPoly, HexPolyFp, HexResultant, HexArith, HexModArith, HexModular, HexPolyZGcd]
    mathlib: false
    done_through: 0
    status: planned
  HexMvGcdMathlib:
    deps: [HexMvGcd, HexMvPolyMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexPolyZGcd` is the arity-one case, called rather than reimplemented;
see "Scope". `HexPolyFp` and `HexModArith` are for the univariate images
over `F_p`.
`HexBasic` will supply the explicitly threaded `Rand` state specified in
[hex-finite-field](hex-finite-field.md); that file is not landed yet.
`HexModular` supplies CRT and reconstruction. `HexModArith` owns the
bundled bounded-prime stream.
`HexResultant` is for route 4 and for the `ExactDivLaws` interface.
`HexArith` is for the integer gcd and the extended Euclidean algorithm.
`HexPoly` comes in through `DensePoly`, which `toUnivariate` returns.

`HexMvPoly`, `HexMvPolyMathlib`, and `HexResultant` are active.
`HexModular` and `HexPolyZGcd` are planned and not yet registered in
`libraries.yml`; their entries must be added and implemented before the
block above can be applied. Three shared additions are also unlanded:
`HexBasic.Rand`, the bundled modulus supply in `HexModArith`, and the
extended-chain amendment to `HexResultant`.
The new entries are nevertheless `planned`, not `draft`, because this SPEC
fixes their required API and milestones; registration waits until the
dependency entries exist.

## Why gcd and squarefree decomposition are one library

Squarefree decomposition's only nontrivial dependency is the gcd, its
dependency set is identical, and it is a few hundred lines. Splitting it
out would produce a library with one algorithm, the same dependencies,
and a second round of release plumbing.

The natural seam, if one appears, is not between gcd and squarefree
decomposition. It is between verification and fast routes:
`Normalize.lean`, `Gauss.lean`, `Cert.lean`, `Divide.lean`, and
`Content.lean` carry the verification path and no heuristic search;
`Heu.lean` and `Brown.lean` carry fast search and no soundness proofs.

## Open questions

- **Whether an order-independent normalisation is worth defining.**
  Fixing the sign from the lex-least monomial rather than the
  `cmp`-leading one would make `gcd_reorder` an equality over `ℤ`. It
  costs a scan the current definition does not need, and no consumer has
  asked for the equality.
- **Whether `cancel` needs a reduced kernel closure.** Checking only the
  cofactor identities in the kernel shrinks the proof term. Whether it
  matters depends on certificate sizes in practice.
- **Which sparse algorithm merits a later amendment.** Zippel and sparse
  Hensel lifting have different prerequisites and failure policies. The
  sparse stress benchmarks measure the gap, but this SPEC intentionally
  does not choose an underspecified route.
- **Sparse exponent vectors.** hex-mv-poly leaves open whether a large
  arity with few active variables wants a sparse `Mono`. The sparse gcd
  family here, at 12 variables, is one of the two measurements that would
  settle it.
