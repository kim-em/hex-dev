# hex-mv-gcd (multivariate gcd and squarefree decomposition, depends on hex-mv-poly)

Greatest common divisors, cofactors, content, primitive part, exact
division, and squarefree decomposition for `MvPoly n R cmp`. Mathlib-free.
The companion `hex-mv-gcd-mathlib` discharges the gcd-domain hypothesis the
Mathlib-free soundness theorems carry, transports the results onto
`MvPolynomial (Fin n) R`, and supplies the decidability instances that make
them usable from a Mathlib goal.

This SPEC expands the "Multivariate gcd and squarefree decomposition"
entry in [future-work](../future-work.md) and depends on the
representation fixed by [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md). Two things that
entry says need correcting, and both are corrected below: the coprimality
certificate it inherits from the modular-gcd item does not generalise as
written (see "The certificate"), and the recursive view it names drops
the arity, which costs more bookkeeping than it saves here (see "The
recursive view").

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

- What runs unchanged is the *executable* chain. Its correctness
  theorems additionally require `Lean.Grind.CommRing` on the coefficient
  type (`HexResultant/Subresultant.lean:152` and following), and the
  `DensePoly` instance tower that supplies it is built in
  `HexResultant/ExactDiv.lean:351`, `392`, and `434`. No such tower
  exists for `MvPoly`, and hex-mv-poly's SPEC puts `CommRing` only in
  its Mathlib companion. Supplying a Mathlib-free
  `Lean.Grind.CommRing (MvPoly n R cmp)` is a prerequisite, not a
  consequence.
- The instances do not let a caller nest the type. The certificate below
  bottoms out in a Bézout identity in the coefficient ring, and
  `MvPoly n R cmp` is not a Bézout domain for `n ≥ 1`. Nested
  coefficients have to be flattened to `MvPoly (m+n) R` first.

**Divisibility and squarefree tests from Mathlib.** The companion
supplies `Decidable (a ∣ b)` for `MvPolynomial (Fin n) ℤ` and
`Decidable (Squarefree p)` for `MvPolynomial (Fin n) ℚ`, in the same
style as `hex-berlekamp-mathlib`'s `Decidable (Irreducible f)`. The
squarefree instance is over `ℚ` rather than `ℤ` for the reason set out
under "What squarefree means here": over `ℤ` the ring-theoretic
predicate is a question about the integer content, and answering it
needs integer factorization.

**Partial fractions and CAD.** `Apart` in more than one variable and the
projection phase of cylindrical algebraic decomposition both need
squarefree bases and content. They are downstream of factorization, so
they are consumers of this library rather than drivers of its design.

## Scope

In scope: gcd with cofactors, gcd of a list, lcm, content and primitive
part in a named variable, monomial content, exact division and its
`Option` form, divisibility, squarefree decomposition, squarefree part
and radical, and the positive-characteristic variants of the last three.

Not in scope: factorization into irreducibles (that is `hex-mv-factor`,
and it depends on this library), Gröbner bases, resultants themselves
(hex-resultant computes them once this library supplies the instances),
multivariate Hensel lifting, and the sparse Hensel gcd route (see
"Routes not specified here").

Also not in scope: the univariate integer case, which is
[hex-poly-z-gcd](hex-poly-z-gcd.md). That library computes gcds of
`ZPoly` for the consumers that hold `DensePoly Int` and would otherwise
convert, its certificate is the arity-one specialisation of the one
below with an unconditional soundness theorem (the content recursion
bottoms out in `Int.gcd`, so `LawfulContent` does not arise), and this
library should call it for the base case of its recursion in the main
variable rather than reimplement it.

The coefficient rings that matter are `Int`, `Rat`, `ZMod64 p`, and
`FpPoly p`. The algorithms are written against a coefficient interface
rather than against those four, because the recursive `GcdOps` instance
on `MvPoly` is what hands `MvPoly` to hex-resultant.

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

/-- Coefficient rings in which coprimality is witnessed by a Bézout
identity. Required of the base ring only, never of `MvPoly`. -/
class BezoutOps (R : Type u) [Zero R] [One R] [Add R] [Mul R] [Dvd R]
    extends GcdOps R where
  xgcd : R → R → R × R

/-- The algebraic hypotheses the gcd algorithms need of `R`. Separated
from the operations so that a consumer may compute without them. -/
class LawfulGcdOps (R : Type u) [Lean.Grind.CommRing R] [DecidableEq R]
    [Dvd R] [GcdOps R] : Prop where
  dvd_iff        : ∀ a b : R, a ∣ b ↔ ∃ c, b = a * c
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
```

with `normalize a = a * GcdOps.normUnit a`, matching Mathlib's naming so
the companion's transport lemmas do not have to rename anything.

Three of these fields are load-bearing and easy to leave out.
`no_zero_div` is used by every
argument below that multiplies leading coefficients or reasons about the
degree of a divisor. `normalize_mul` is what makes Gauss's lemma an
equality rather than an `Associated` statement. `gcd_normalized` is what
makes `gcd` a function rather than a choice of associate.

`normUnit` returns a unit on **every** input including zero, so the field
instance is `normUnit a = if a = 0 then 1 else a⁻¹`, not `a⁻¹`.

Instances required here: `Int` (gcd through hex-arith, `normUnit` the
sign with `normUnit 0 = 1`, `xgcd` the extended Euclidean algorithm),
`Rat` and any field, `ZMod64 p` for prime `p`, `FpPoly p`,
`DensePoly Int`, and `MvPoly n R cmp` whenever `R` has one.

`BezoutOps` holds for `Int`, for fields, and for `FpPoly p` with `p`
prime. It does not hold for `MvPoly n R cmp` with `n ≥ 1`, and it does
not hold for `DensePoly Int`: neither ring is a Bézout domain. That
failure is not incidental, and it is what makes the certificate design
below the shape it is.

**Modular reduction is a separate interface.** The primary coprimality
certificate reduces coefficients into a small field, and no operation
above provides that. Reduction is not available for a general `R`, and
for `Rat` it is partial (a denominator may vanish modulo `p`). The
interface is therefore an explicit homomorphism carried by the
certificate rather than a class field:

```lean
/-- A ring homomorphism from the coefficient ring into a finite field,
supplied per certificate. `toField? = none` records that this input
cannot be reduced at this prime (a vanishing denominator over `Rat`). -/
structure CoeffHom (R : Type u) (p : Nat) [ZMod64.Bounds p] where
  toField? : R → Option (ZMod64 p)
  map_zero, map_one, map_add, map_mul, map_neg   -- as partial-function laws
```

`Int` supplies a total `CoeffHom` at every prime. `Rat` supplies a
partial one. `ZMod64 p` supplies the identity at its own prime and
nothing at others. `MvPoly` supplies none, which is another reason the
type does not nest.

## Exact division

Exact division is the operation every check in this library runs, so it
is specified before the gcd itself.

```lean
namespace Hex.MvPoly

/-- Division with remainder against a single divisor, in the monomial
order `cmp`: repeatedly cancel the leading monomial of the running
dividend against the leading monomial of `g`, moving a term to the
remainder when `Mono.dvd` fails. -/
def divMod [IsMonomialOrder cmp] (f g : MvPoly n R cmp) :
    MvPoly n R cmp × MvPoly n R cmp

/-- The exact quotient, or `none` when `g = 0` or `g ∤ f`. -/
def divExact? [IsMonomialOrder cmp] (f g : MvPoly n R cmp) :
    Option (MvPoly n R cmp)

instance : Dvd (MvPoly n R cmp)
instance [IsMonomialOrder cmp] (f g : MvPoly n R cmp) : Decidable (g ∣ f)

/-- The total form, for hex-resultant's `[Div R]` interface. -/
instance [IsMonomialOrder cmp] : Div (MvPoly n R cmp)
instance [IsMonomialOrder cmp] : ExactDivLaws (MvPoly n R cmp)
```

`divMod` terminates because `IsMonomialOrder.wf` well-orders the
monomials and each step strictly decreases the leading monomial of the
running dividend. This is the one place the `wf` field of
`IsMonomialOrder` is load-bearing, and it is why the divisibility
operations require the full class rather than `TransCmp` plus
`LawfulEqCmp`.

`divExact?` is not `divMod` followed by a zero test. It fails as soon as
a leading monomial fails to divide, which is the common case when the
answer is "does not divide" and is what makes trial division cheap
enough to run on every candidate.

```lean
theorem divMod_spec : f = (divMod f g).1 * g + (divMod f g).2
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
of the monomial contents, divisibility of the leading coefficients, and
divisibility of the images under one evaluation modulo a small prime.
Each rejects without allocating a quotient. The filter is a prefilter
only, and the division loop remains the decision.

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
`HexResultant/ExactDiv.lean:255-434` builds the same tower for
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
(`HexResultant/Subresultant.lean:65` and `:92`); the quotient is
discarded and no transformation is accumulated.

An extended chain is therefore a new recurrence that tracks the
transformation pair through the pseudo-scaling and the exact scalar
division at every step, with proofs that each cofactor numerator is
divisible by the Brown scalar it is divided by:

```lean
/-- The subresultant chain with the cofactors producing each entry:
`(uₖ, vₖ, Sₖ)` with `uₖ · f + vₖ · g = Sₖ`. -/
def subresultantChainExt [Zero R] [DecidableEq R] [One R] [Add R] [Sub R]
    [Mul R] [Div R] (f g : DensePoly R) :
    Array (DensePoly R × DensePoly R × DensePoly R)
```

That is a substantive development, not a one-line export, and it is not
on this library's required path: the primary certificate needs no
cofactors. It should wait until the benchmark question under "Open
questions" says whether `splitBezout` is worth having.

## Content and primitive part

```lean
def contentIn (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    (p : MvPoly (n+1) R cmp) : MvPoly n R cmp'
def primPartIn (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    (p : MvPoly (n+1) R cmp) : MvPoly (n+1) R cmp
def content (p : MvPoly n R cmp) : R
def primPart (p : MvPoly n R cmp) : MvPoly n R cmp
```

```lean
theorem contentIn_mul_primPartIn :
    constIn i cmp' (contentIn i cmp' p) * primPartIn i cmp' p = p
theorem contentIn_dvd_coeff :
    ∀ k, contentIn i cmp' p ∣ (toUnivariate i cmp' p).coeff k
theorem primPartIn_content : contentIn i cmp' (primPartIn i cmp' p) = 1
theorem contentIn_mul  :
    contentIn i cmp' (p * q) = contentIn i cmp' p * contentIn i cmp' q
theorem primPartIn_mul :
    primPartIn i cmp' (p * q) = primPartIn i cmp' p * primPartIn i cmp' q
```

The last two are Gauss's lemma. They are stated for the normalised
content, so they are equalities rather than `Associated` statements,
which is what `normalize_mul` in `LawfulGcdOps` is for. Their proofs are
the largest piece of algebra in the Mathlib-free layer.

**The universal property of content is the hard one, and it is not on
this list.**

```lean
theorem dvd_contentIn (d) :
    (∀ k, d ∣ (toUnivariate i cmp' p).coeff k) → d ∣ contentIn i cmp' p
```

`contentIn` is computed by folding this library's own multivariate
`gcd`, so `dvd_contentIn` is that gcd's maximality one variable down.
The checker's soundness argument needs it, which makes the Mathlib-free
soundness theorem conditional. See "Where maximality lives".

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

### The modular witness, which is primary

Fix a variable `i`, a comparator `cmp'` on the remaining variables, a
prime `p`, a homomorphism
`φ_R : CoeffHom R p`, and a point `a : Fin n → Option (ZMod64 p)`
assigning values to the remaining variables. Write `φ` for
`partialEval a` composed with `mapCoeffs φ_R.toField?`, followed by
`toUnivariate i cmp'`, landing in `FpPoly p`. The evaluation point lives in the
target field, not in `R`.

If `(toUnivariate i cmp' f').degree? = (φ f').degree?` and the same for `h'`,
and `α · φ f' + β · φ h' = 1` in `FpPoly p`, then `f'` and `h'` have no
common divisor of positive degree in `xᵢ`.

The argument, with its hypotheses named because they are easy to leave
implicit. `R` and `MvPoly n R cmp` are integral domains
(`LawfulGcdOps.no_zero_div` and the leading-term argument below); `p` is
prime, so `FpPoly p` is a domain; `φ` is a ring homomorphism where it is
defined. A common divisor `d` gives `f' = d · e`, hence
`φ f' = φ d · φ e`. Degrees add in both domains, so
`deg φ f' ≤ deg d + deg e = deg f'` with equality exactly when neither
image drops degree. The checked degree equality is that equality, so
`deg φ d = deg_i d`. Then `φ d` divides `α · φ f' + β · φ h' = 1`, so
`φ d` is a unit in `FpPoly p`, so `deg_i d = 0`.

No separate "the point avoids the zeros of the leading coefficient"
hypothesis is needed. The checked degree equality is that condition.

Coprimality in `FpPoly p` is witnessed rather than asserted: `FpPoly p`
is a Bézout domain, `HexPoly.xgcd` produces `α` and `β`, and the check
is one polynomial identity over a small field.

That leaves common divisors of degree zero in `xᵢ`, which divide
`contentIn i f'` and `contentIn i h'`. Those are handled by recursion on
the certificate.

### The certificate type and the checker

```lean
/-- A witness that two elements of `MvPoly n R cmp` have no nonunit
common divisor. The recursion is structural in the arity: each `split`
eliminates one variable and lands one arity down, so progress is a
property of the type rather than a side condition the checker verifies. -/
inductive CoprimeCert : (n : Nat) → (R : Type u) → (cmp : Mono n → Mono n → Ordering) → Type u
  /-- One side is a unit. -/
  | unit : CoprimeCert n R cmp
  /-- Arity zero: both sides are constants, with a Bézout pair in `R`. -/
  | base (u v : R) : CoprimeCert 0 R cmp
  /-- Split on `xᵢ` at the prime `p` and the point `a`, with a Bézout
  pair over `FpPoly p`, and a certificate for the contents one arity
  down under the chosen comparator `cmp'`. -/
  | split (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
          (p : Nat) (φ : CoeffHom R p) (a : Fin n → Option (ZMod64 p))
          (α β : FpPoly p) (rest : CoprimeCert n R cmp') :
      CoprimeCert (n+1) R cmp
  /-- Split on `xᵢ` with `u · f + v · h = constIn i cmp' r`, where
  `r ≠ 0` lives in the remaining variables. -/
  | splitBezout (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
                (u v : MvPoly (n+1) R cmp) (r : MvPoly n R cmp')
                (rest : CoprimeCert n R cmp') :
      CoprimeCert (n+1) R cmp

def checkCoprime (f h : MvPoly n R cmp) : CoprimeCert n R cmp → Bool

structure GcdCert (n : Nat) (R : Type u) (cmp : Mono n → Mono n → Ordering) where
  gcd     : MvPoly n R cmp
  cofL    : MvPoly n R cmp
  cofR    : MvPoly n R cmp
  coprime : CoprimeCert n R cmp

def checkGcd (f h : MvPoly n R cmp) (c : GcdCert n R cmp) : Bool :=
  c.gcd * c.cofL == f && c.gcd * c.cofR == h &&
  checkCoprime c.cofL c.cofR c.coprime &&
  isNormalized c.gcd
```

`checkCoprime` on `split` verifies, cheapest first: that `p` is prime and
within `ZMod64.Bounds`; that `φ` is defined on every coefficient
involved; the two degree equalities on `toUnivariate i cmp'`; the Bézout
identity in `FpPoly p`; and then recursively, one arity down, that
`contentIn i cmp' f` and `contentIn i cmp' h` are coprime. On
`splitBezout` it verifies `r ≠ 0`, `u · f + v · h = constIn i cmp' r`,
and the same recursion. On `base` it verifies that
`u · a + v · b = 1`. On `unit` it verifies that one side satisfies
`GcdOps.isUnit`.

Indexing the certificate by the arity is what makes "each step removes a
variable" true, and it is free: the constructor's result type says so.
An arity-preserving certificate would need a set of remaining variables
carried alongside and an `i ∈ active` check in the checker, purely to
recover the same guarantee.

**Degenerate inputs are certificate completeness cases, not output
conventions.** A coprime pair cannot contain zero unless the other side
is a unit, so the producer must special-case them: `gcd 0 0` returns
`⟨0, 1, 1, .unit⟩`; `gcd f 0` returns `⟨normalize f, u, 0, .unit⟩` with
`u` the unit making the identity hold; arity zero and the
all-variables-eliminated case go through `base`. Without these the
modular constructor has no image Bézout identity to produce.

The `splitBezout` argument is the shorter of the two: a common divisor
`d` divides `constIn i cmp' r`, and a divisor of something constant in
`xᵢ` is constant in `xᵢ` in a domain, so `d` divides both contents. It
needs no
prime, no point, and no homomorphism. It is not primary because `u` and
`v` come from an extended subresultant computation, which suffers the
coefficient swell the modular routes exist to avoid, and because
hex-resultant does not compute them today.

### Where maximality lives

Both split cases finish with "so `d` divides both contents". That step is
`dvd_contentIn`, the universal property of the content, and the content
is computed by this library's own gcd one variable down. So the checker's
soundness rests on gcd maximality rather than establishing it. Putting
maximality entirely in the companion while claiming an unconditional
Mathlib-free `checkCoprime_sound` would be circular.

The resolution is design principle 2 applied where the dependency
actually is. The Mathlib-free layer states the property as a class and
proves soundness conditionally on it:

```lean
/-- The one gcd-domain fact the checker rests on. Discharged for
`Int`, `Rat`, and `ZMod64 p` coefficients in `hex-mv-gcd-mathlib`. -/
class LawfulContent (n : Nat) (R : Type u) (cmp : Mono n → Mono n → Ordering) : Prop where
  dvd_contentIn : ∀ (i : Fin n) (p d : MvPoly n R cmp),
    (∀ k, d ∣ (toUnivariate i cmp' p).coeff k) → d ∣ contentIn i cmp' p

theorem checkCoprime_sound [LawfulContent n R cmp] :
    checkCoprime f h c = true → ∀ d, d ∣ f → d ∣ h → IsUnit d

/-- What the checker establishes: the cofactor identities, and
coprimality of the cofactors. -/
def CoprimeCofactors (f h g : MvPoly n R cmp) : Prop :=
  ∃ f' h', f = g * f' ∧ h = g * h' ∧ ∀ d, d ∣ f' → d ∣ h' → IsUnit d

theorem checkGcd_sound [LawfulContent n R cmp] :
    checkGcd f h c = true → CoprimeCofactors f h c.gcd
```

`hex-mv-gcd-mathlib` discharges `LawfulContent` from
`MvPolynomial.uniqueFactorizationMonoid`, the instance Mathlib supplies
for `MvPolynomial σ D` with `D` a unique factorization domain, and then
proves the unconditional maximality statement
`CoprimeCofactors f h g → ∀ d, d ∣ f → d ∣ h → d ∣ g` on the Mathlib
side.

The consequence, stated so nobody is surprised by it: a Mathlib-free
consumer of this library gets a theorem with a hypothesis it cannot
discharge. Everything that wants the unconditional statement, including
the `cancel` tactic, therefore lives in the companion, in the same way
`factor_poly`'s `Polynomial ℤ` provider does. The alternative, proving
`LawfulContent` Mathlib-free by induction on the arity,
is a genuine option and amounts to proving `MvPoly n R cmp` is a gcd
domain from scratch. It is recorded under "Open questions" rather than
adopted, because it moves the largest proof in the project into
milestone 2.

Two further statements need the same hypothesis, and both look as though
they should not. `Associated (gcd f h) (gcd h f)` does not follow from
`CoprimeCofactors` in a general domain: two elements with coprime
cofactors need not be associate without a gcd-domain or pre-Schreier
argument. And `LawfulGcdOps (MvPoly n R cmp)`, the recursive instance,
has `dvd_gcd` as a field, so it is available only where `LawfulContent`
is.

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

```lean
namespace Hex.MvPoly

variable [IsMonomialOrder cmp] [GcdOps R] [BezoutOps R]

def gcdCert (f h : MvPoly n R cmp) : GcdCert n R cmp
def gcd (f h : MvPoly n R cmp) : MvPoly n R cmp := (gcdCert f h).gcd
def cofactors (f h : MvPoly n R cmp) : MvPoly n R cmp × MvPoly n R cmp
def isCoprime (f h : MvPoly n R cmp) : Bool
def gcdList (ps : List (MvPoly n R cmp)) : MvPoly n R cmp
def lcm (f h : MvPoly n R cmp) : MvPoly n R cmp
```

Contracts on the degenerate inputs: `gcd 0 0 = 0`, `gcd f 0 = normalize f`,
`gcd f h = 1` whenever either side is a unit, `gcdList [] = 0`, and
`lcm f 0 = 0`. Each has a matching certificate case above.

**Normalisation depends on the monomial order, over `ℤ` as well.** `gcd`
returns the associate whose leading coefficient in `cmp` order is
`normalize`d. This is **not** order-independent over `ℤ`, although the
argument that it should be is tempting: negation does flip the sign of
every coefficient at once, but *which* coefficient is leading changes
with the order, and the two leading coefficients can have different
signs.
For `x - y`, an order with `x` leading normalises to `x - y`, and an
order with `y` leading sees leading coefficient `-1` and normalises to
`y - x`. So there is one transport lemma, not two, and it is
`Associated`:

```lean
theorem gcd_reorder : Associated (gcd (reorder f) (reorder h)) (reorder (gcd f h))
```

An order-independent normalisation would have to fix the sign from
something other than the `cmp`-leading coefficient (the sign of the
coefficient of the lex-least monomial, say). Whether that is worth
having is under "Open questions"; it is not assumed anywhere above.

**Rational coefficients.** Over `ℚ` the content is always a unit, so
`primPart` is useless and the coefficient swell in a PRS is maximal.
`gcdCert` on `MvPoly n Rat cmp` scales both inputs to primitive integer
polynomials, computes there, and scales back. This is a requirement
rather than an option, and the benchmark family named below checks it.

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
input and put `GcdOps.gcd` of the two contents into the answer; and
restrict attention to `vars f ∩ vars h`. Each is linear in
the term count and each strictly shrinks the problem.

### 1. Coprime detection, the case that dominates

`isCoprime` runs, per variable, one evaluation and one univariate
gcd: pick a prime and a random point for all remaining variables,
check the degrees survive, and compute `gcd` in `FpPoly p`. A result of
`1` yields the `split` constructor and the recursion continues on the
contents one arity down. A result other than `1` proves
nothing (the point may be unlucky) and the route falls through.

That asymmetry is the point: the cheap test is conclusive exactly in the
case that occurs most often. The cost is up to one image gcd per
variable, not one in total.

The requirement this places on the implementation is that `gcd f h` must
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
because this route carries fuel and falls through to route 5. A bound
*is* what would prove that this route itself eventually succeeds:
`checkGcd` recognises the right answer once the modulus is large enough
and the support has stabilised, but it does not prove that either happens.
Route 3 is therefore specified without a completeness theorem, which is
consistent with its being one of the unverified producers.

### 4. Zippel's sparse interpolation

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
[arXiv:2207.13874](https://arxiv.org/abs/2207.13874). The route as
specified here is sound whatever it produces, because `checkGcd` decides,
but "sound because it is checked" is not the same as "fast", and the
performance claim depends on implementing the pieces above rather than
the sketch.

The random point is an explicit argument rather than a monad, following
the pattern the equal-degree-splitting item in
[future-work](../future-work.md) sets.

### 5. The subresultant fallback

Recurse on the arity. In the main variable `xᵢ`, run
hex-resultant's `subresultantChain` **unchanged** over the coefficient
ring `MvPoly n R cmp'`, take the primitive part in `xᵢ` of the terminal
nonzero entry, and multiply by the recursively computed gcd of the
contents.

Running the subresultant chain while taking the primitive part of each
remainder is a third thing, and not a correct one. The subresultant
recurrence's exact divisions are justified by scale
invariants that primitive-part removal destroys, so a primitive PRS is a
separate recurrence with its own completeness theorem, not a variant of
Brown's chain. This SPEC takes the first option: reuse hex-resultant's
chain as it stands and take the primitive part once, at the end. The
cost is the coefficient swell inside the chain that a primitive PRS would
avoid, and that is acceptable because this route exists to be proved
rather than to be fast.

It is deterministic, needs no prime, no point, and no random draw, and it
is what makes `gcdCert` a total function with a proved postcondition:

```lean
theorem gcdCert_checks [LawfulContent n R cmp] : checkGcd f h (gcdCert f h) = true
```

The proof obligation is concentrated: `checkGcd_sound` (small, and stated
above) plus completeness of route 5, which is the standard subresultant
argument and shares its shape with hex-resultant's existing development.
Routes 1 through 4 need no correctness proof at all, which is the whole
reason for the architecture.

### Routes not specified here

FLINT reaches its performance on multivariate integer gcds with four
routes, and the fourth, a sparse Hensel lifting gcd, is not specified
here. Adding it is a later milestone. Until it exists, the performance
claim against FLINT is "competitive on the dense and coprime families",
not "approaching FLINT in general", and the benchmark section says so.

## Squarefree decomposition

### What squarefree means here

Over a field, "no square of a nonunit divides `p`" is the whole story.
Over `ℤ` it is not, and the distinction has to be made before any
signature is written. `12x` is not squarefree in `ℤ[x]`, because
`4 ∣ 12`, so the ring-theoretic predicate over `ℤ[x₁, …, xₙ]` is partly a
question about the integer content, and deciding it needs integer
factorization, which this project does not yet have (it is its own entry
in [future-work](../future-work.md)).

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
def Squarefree (p : MvPoly n R cmp) : Prop := ∀ d, d * d ∣ p → IsConst d

structure SqfFactor (n : Nat) (R : Type u) (cmp : Mono n → Mono n → Ordering) where
  factor       : MvPoly n R cmp
  multiplicity : Nat

structure SqfDecomp (n : Nat) (R : Type u) (cmp : Mono n → Mono n → Ordering) where
  content : R
  factors : List (SqfFactor n R cmp)

def sqfDecomp (p : MvPoly n R cmp) : SqfDecomp n R cmp
def radical (p : MvPoly n R cmp) : MvPoly n R cmp
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
For the converse, suppose an irreducible `d` divides the gcd. From
`p = d · e` with `d ∤ e` and `d ∣ ∂ⱼp = ∂ⱼd · e + d · ∂ⱼe` it follows
that `d ∣ ∂ⱼd`, so `∂ⱼd = 0` by degree, for every `j`. In characteristic
zero that makes `d` constant. In characteristic `p` it makes `d` a
polynomial in the `p`-th powers of the variables, hence a `p`-th power
over a perfect coefficient field, contradicting irreducibility.

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
signature carries the hypothesis, and the positive-characteristic radical
goes through the decomposition instead.

```lean
theorem isSquarefree_iff [PerfectFrac R] : isSquarefree p = true ↔ Squarefree (primPart p)
theorem radical_squarefree [NatNoZero R] : Squarefree (radical p)
theorem radical_dvd : radical p ∣ p
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

### The decomposition in positive characteristic

This case is harder than the characteristic-zero one in a way that is
not obvious, and the natural generalisation of it is wrong. Over
`F_p[x, y]`, `f = x^p + y` has
`∂f/∂x = 0` while `∂f/∂y = 1`. It is squarefree and it is not a `p`-th
power, so "when every derivative vanishes take the `p`-th root" never
fires, yet a Yun run in main variable `x` divides by a zero derivative.
Choosing a variable whose derivative is nonzero fixes that example and
not the general case: `(x^p + y)² · (x + y^p)²` needs `y` for the first
factor and `x` for the second, and no single main variable finds both.

What makes this hard is not the perfectness of the ground field. It is
that the Yun recursion in `xᵢ` works over the coefficient ring
`F_q[x₁, …, x̂ᵢ, …, xₙ]`, and that ring is **not** perfect, so the
univariate characteristic-`p` fix (when the derivative vanishes, take a
`p`-th root) does not apply level by level. The relevant primitive is
not a `p`-th root at all:

```lean
/-- Divide every `xᵢ`-exponent by `p`, when all of them are divisible by
`p`. This inverts the substitution `xᵢ ↦ xᵢ^p`; it is not a `p`-th root,
since the coefficients are untouched. -/
def pthRootIn? (i : Fin n) (p : Nat) (f : MvPoly n R cmp) : Option (MvPoly n R cmp)

/-- A genuine `p`-th root, available only when the coefficients have
`p`-th roots. -/
class PerfectOps (R : Type u) (p : Nat) : Type u where
  pthRoot : R → R

class LawfulPerfectOps (R : Type u) (p : Nat) [PerfectOps R p] : Prop where
  prime      : Nat.Prime p
  pow_pthRoot : ∀ a : R, (PerfectOps.pthRoot a) ^ p = a
  char       : ∀ a : R, p • a = 0
```

`ZMod64 p` satisfies these with `pthRoot = id` by Fermat's little
theorem. `GFq p k` satisfies them with `a ↦ a^(p^(k-1))`, which needs the
cardinality and so is an instance for that type rather than a formula in
the generic class.

The algorithm is scheduled for milestone 5 and should follow an
established treatment rather than an invented one. Gianni and Trager,
"Square-free algorithms in positive characteristic" (AAECC 7, 1996), is
the standard reference and covers exactly the non-perfect coefficient
ring case that the naive recursion gets wrong. Until it is implemented,
`sqfDecomp` carries the characteristic-zero hypothesis and
`isSquarefree`, whose correctness argument above covers perfect positive
characteristic, is what the positive-characteristic consumers get.

### Contract theorems

```lean
theorem sqfDecomp_prod :
    (sqfDecomp p).factors.foldl (fun acc f => acc * f.factor ^ f.multiplicity)
      (C (sqfDecomp p).content) = p
theorem sqfDecomp_squarefree : ∀ f ∈ (sqfDecomp p).factors, Squarefree f.factor
theorem sqfDecomp_primitive  : ∀ f ∈ (sqfDecomp p).factors, content f.factor = 1
theorem sqfDecomp_coprime :
    ∀ f ∈ (sqfDecomp p).factors, ∀ g ∈ (sqfDecomp p).factors,
      f.multiplicity ≠ g.multiplicity → IsCoprime f.factor g.factor
theorem sqfDecomp_multiplicity_pos, sqfDecomp_multiplicity_sorted
theorem sqfDecomp_nonconstant :
    ∀ f ∈ (sqfDecomp p).factors, ¬ IsConst f.factor
```

Multiplicities are positive, pairwise distinct, and returned in
increasing order. Factors are primitive and nonconstant, which is what
makes the content field carry all the coefficient information. The zero
input returns `⟨0, []⟩`.

There is no `sqfDecomp_content_isUnit`. Uniqueness of the decomposition
up to units is a companion theorem, for the same reason maximality of the
gcd is.

## Complexity

These are **probe counts**, not operation counts: they count image gcds,
evaluations, and coefficient gcds rather than machine operations, and
they omit the cost of each probe. A full cost model would have to
multiply through by the univariate gcd, interpolation, and CRT costs at
every level, and this SPEC does not attempt one.

Parameters: `n` variables, `t` terms in the larger input, `s` terms in
the gcd, `d` the maximum degree in any one variable, `D = ∏(dᵢ + 1)` the
dense size, and `M` the maximum multiplicity in a squarefree
decomposition.

| operation | algorithm | probe count |
|---|---|---|
| `monoContent` | `Mono.gcd` fold over the support | `O(n · t)` machine ops |
| `content` | `GcdOps.gcd` fold | `t` coefficient gcds |
| `toUnivariate` | partition by the exponent of `xᵢ` | `O(n · t log t)` machine ops |
| `contentIn` | `d` gcds on polynomials of `t/d` terms | `d` recursive gcds |
| `divExact?` | leading-monomial cancellation, early failure | `O(n · t_q · t_g · log)` machine ops |
| `isCoprime` | one image gcd per variable | `≤ n` image gcds |
| heuristic gcd | one `Int.gcd`, integers of `O(t · log ξ · ∏(dⱼ+1))` bits | 1 integer gcd |
| Brown | one image gcd per evaluation point, per prime | `O(D)` image gcds |
| Zippel | images plus Vandermonde solves | `O(n · s · d)` image gcds, `O(s²)` per solve |
| PRS | subresultant chain, primitive part once | no useful bound |
| `sqfDecomp` | one gcd per level per variable | `O(n · M)` gcds |
| `radical` | gcd of `p` and `n` derivatives | `n` gcds |

The table makes the dispatch order argument: route 1 costs at most `n`
probes and settles the most common input, route 2 costs one and settles
small inputs, route 3 is bounded by the dense size, route 4 by the term
count, and route 5 has no bound and settles the rest.

## Kernel exposure

The kernel replay closure is `checkGcd` and what it calls: polynomial
multiplication and equality from hex-mv-poly, `divExact?`, `toUnivariate`,
`contentIn`, `mapCoeffs`, `partialEval`, and `FpPoly` multiplication,
addition, and equality. Each is `@[expose]`, and a downstream module
carries a `decide +kernel` test that fails if any of them stops reducing.

Nothing in routes 1 through 5 is in that closure. The modular machinery,
the interpolation, the Vandermonde solves, and the subresultant chain are
search, they never appear in a proof term, and they should not pay for
exposure.

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

Two fixture kinds. `mvgcd` carries the arity, the comparator name, the
coefficient domain, and two term lists, and its result records the gcd
and both cofactors. `mvsqf` carries one term list and its result records
the content and the `(factor, multiplicity)` list. Both reuse the
`(exponent vector, coefficient)` encoding hex-mv-poly's `mvpoly` fixture
kind defines, so one fixture parser serves all three.

**The oracle suite alone cannot catch the bugs this library is most
likely to have.** Every route's candidate goes through `checkGcd`, and a
rejected candidate falls through to route 5, which returns the right
answer. So an end-to-end fixture passes even if Brown's
leading-coefficient correction is inverted, its bad-point test never
fires, and Zippel is entirely broken. Oracle fixtures check the public
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
- Positive characteristic: `x^p + y` (squarefree, one vanishing
  derivative, not a `p`-th power), `(x^p + y)²`, `g^p`, and
  `(x^p+y)² · (x+y^p)²`, which is the input no single main variable
  handles.
- Arity zero and arity one, where the answers must agree with `Int.gcd`
  and with hex-poly's univariate `gcd`. The arity-one agreement is
  checked in Lean rather than against the oracle, since both sides are
  ours.

**Oracle choice.** SymPy's `gcd`, `cofactors`, `sqf_list`, and `sqf_part`
cover the surface over `ℤ` and `ℚ`, and its `modulus=` argument covers
`GF(p)`, which the positive-characteristic cases above require. Extension
fields `F_q` are not covered by SymPy and are out of scope for the
oracle; the `GFq` cases are checked in Lean against hex-poly-fp's
univariate decomposition instead. python-flint's `fmpz_mpoly.gcd` is a
stronger implementation but does not expose cofactors or squarefree
decomposition uniformly, so it appears below as a performance comparator
rather than as the oracle.

The companion adds randomised comparison against
`MvPolynomial (Fin n) ℤ` through hex-mv-poly's `equiv`, checking the
divisibility and coprimality statements directly rather than through the
oracle's normalisation conventions.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexMvGcd/Bench.lean`. Native only. There is no kernel suite: the
kernel path here is certificate checking, which hex-mv-poly's kernel
suite already measures on the same operations.

Families, chosen so that each isolates one route:

- **Coprime pairs**, 2 to 8 variables, dense and sparse. Decides whether
  route 1 works. The required property is that the time is a small
  multiple of the time to evaluate the inputs `n` times. A regression
  means an interpolation is running when it should not.
- **Dense gcds**, 3 to 5 variables, degree 5 to 20 in each. Route 3.
- **Sparse gcds**, 5 to 12 variables, high degree, few terms. Route 4,
  and the family where the dense route's `O(D)` cost is catastrophic.
- **Swell cases**, small inputs whose subresultant remainder sequence has
  enormous coefficients. Route 5, and the argument for having the others.
- **Rational coefficients**, the same inputs over `ℚ`, checking the
  clear-denominators step happens. Times should track the `ℤ` family.
- **Squarefree decomposition**, multiplicity patterns `1`, `1..5`, `7`,
  and `2,3,5,7`, in 2 to 5 variables. The `7` pattern is there because
  Yun runs one level at a time.
- **Cofactor-heavy**, where the gcd is small and the cofactors are large,
  which stresses `divExact?` rather than the interpolation.

**Comparators.** FLINT's `fmpz_mpoly_gcd` is `informational`. It selects
among Brown, Zippel, a sparse Hensel route, and subresultants with tuned
crossovers, and this library specifies three of those four, so a required
ratio would be a check on a route that does not exist. The written-down
expectation is therefore narrow: on the **coprime**
family the ratio should be within a small constant, since both sides do
one evaluation and one univariate gcd per variable, and a large ratio
there means the fast path is not firing. No advance claim is made on the
sparse family, where FLINT's Hensel route has no counterpart here.
Singular is `informational` for the same reason. SymPy is the oracle and
is not a performance comparator.

## The Mathlib layer

`hex-mv-gcd-mathlib` discharges the hypothesis first, then transports.
Writing `e` for hex-mv-poly's
`equiv : MvPoly n R cmp ≃+* MvPolynomial (Fin n) R`:

```lean
instance : LawfulContent n Int cmp        -- from MvPolynomial.uniqueFactorizationMonoid
instance : LawfulContent n Rat cmp

theorem gcd_dvd_left  : e (gcd f h) ∣ e f
theorem gcd_dvd_right : e (gcd f h) ∣ e h
theorem dvd_gcd (d) : d ∣ e f → d ∣ e h → d ∣ e (gcd f h)

theorem coprimeCofactors_greatest (hc : CoprimeCofactors f h g) (d) :
    d ∣ e f → d ∣ e h → d ∣ e g

theorem contentIn_dvd_coeff (k) :
    e (contentIn i cmp' p) ∣ e ((toUnivariate i cmp' p).coeff k)
theorem dvd_contentIn (d) :
    (∀ k, d ∣ e ((toUnivariate i cmp' p).coeff k)) → d ∣ e (contentIn i cmp' p)

theorem squarefree_spec : Squarefree p ↔ _root_.Squarefree (e (primPart p))
theorem sqfDecomp_unique : ...   -- up to units, from unique factorization
```

Mathlib has `Polynomial.content` for `R[X]` over a `NormalizedGCDMonoid`
and no multivariate counterpart, so the content correspondence is the two
divisibility facts rather than an equation between named contents.

`dvd_gcd` is the maximality statement, and its proof consumes
`MvPolynomial.uniqueFactorizationMonoid`, the instance Mathlib supplies
for `MvPolynomial σ D` with `D` a unique factorization domain. Mathlib
has no `NormalizedGCDMonoid (MvPolynomial σ D)` instance, so the
statements are in terms of divisibility, and the `Associated` version is
derived from the three divisibility facts wherever a caller has such an
instance in scope.

`squarefree_spec` relates this library's relative predicate to Mathlib's
`Squarefree` **on the primitive part**, which is the honest statement.
The decidability instances follow that split:

```lean
instance : Decidable (a ∣ b)          -- MvPolynomial (Fin n) ℤ
instance : Decidable (Squarefree p)   -- MvPolynomial (Fin n) ℚ
```

Divisibility is decidable over `ℤ` because it is exactly `divExact?`.
Squarefreeness is stated over `ℚ`, where the content is a unit and the
relative and ring-theoretic predicates agree. The corresponding `ℤ`
instance is a question about the squarefreeness of the integer content.
Mathlib decides that (`DecidablePred (Squarefree : ℕ → Prop)`), so the
`ℤ` instance is available here after all; what
[hex-int-factor](hex-int-factor.md) adds is the square divisor and the
squarefree part as witnesses, which the decision procedure does not
produce.

Following the project split, no mathematical theorem about `MvPoly`
belongs in the companion beyond these, plus one correspondence lemma per
public semantic operation: `gcd`, `cofactors`, `contentIn`, `primPartIn`,
`radical`, `sqfDecomp`, and `divExact?`.

## Milestones

1. **Coefficient interface, exact division, and the recursive view.**
   `GcdOps`, `BezoutOps`, `LawfulGcdOps`, `CoeffHom`, `divMod`,
   `divExact?`, the `Dvd` / `Div` / `ExactDivLaws` instances, `constIn`,
   `monoContent`, `contentIn`, `primPartIn`, and Gauss's lemma. The `Lean.Grind.CommRing` tower and `mapCoeffs` are already in
   hex-mv-poly, so hex-resultant's chain runs over `MvPoly` with its
   correctness theorems applying as soon as `Div` and `ExactDivLaws`
   land here.

2. **The certificate and the fallback.** `CoprimeCert`, `checkCoprime`,
   `GcdCert`, `checkGcd`, `LawfulContent`, `checkGcd_sound`, and route 5. A correct but slow `gcd`, with
   `gcdCert_checks` proved. Squarefree decomposition in characteristic
   zero, `radical`, and `isSquarefree` land here, since they need only a
   working gcd.

3. **The fast paths.** Routes 0, 1, and 2. This is where the library
   becomes usable by `cancel`, and it needs no new proofs.

4. **Brown.** Route 3, with leading-coefficient correction and the point
   and prime handling. The route-level tests for those traps are written
   before the code.

5. **Zippel and positive characteristic.** Route 4 with term bounds and
   diversification, `pthRootIn?`, `PerfectOps`, and the Gianni-Trager
   decomposition.

6. **The companion.** `LawfulContent` instances, transport, maximality,
   uniqueness, and the two decidability instances. Begins as soon as
   milestone 2 is done, in parallel with 3 through 5. Anything that needs
   the unconditional maximality theorem, including `cancel`, waits for
   this milestone rather than for milestone 2.

## File organisation

```
HexMvGcd/
  Coeff.lean        -- GcdOps, BezoutOps, LawfulGcdOps, CoeffHom, base instances
  Divide.lean       -- divMod, divExact?, Dvd/Div/ExactDivLaws, Grind ring tower
  View.lean         -- constIn and the degree helpers on the univariate view
  Content.lean      -- monoContent, content, contentIn, primPartIn, Gauss
  Cert.lean         -- CoprimeCert, checkCoprime, GcdCert, checkGcd, LawfulContent
  Prs.lean          -- the subresultant fallback, route 5
  Fast.lean         -- routes 0 and 1, isCoprime
  Heu.lean          -- route 2, the Kronecker substitution and its budget
  Brown.lean        -- route 3
  Zippel.lean       -- route 4
  Gcd.lean          -- the dispatch, gcd, cofactors, gcdList, lcm, GcdOps instance
  Squarefree.lean   -- Yun, the content recursion, radical, isSquarefree
  PthRoot.lean      -- PerfectOps, pthRootIn?, the positive-characteristic branch
HexMvGcd.lean
HexMvGcdMathlib/
  Content.lean      -- the LawfulContent instances
  Gcd.lean          -- divisibility, maximality, the Associated statements
  Squarefree.lean   -- Squarefree correspondence and uniqueness
  Decide.lean       -- Decidable (a ∣ b), Decidable (Squarefree p)
HexMvGcdMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexMvGcd:
    deps: [HexMvPoly, HexPoly, HexPolyFp, HexResultant, HexArith, HexModArith, HexPolyZGcd]
    mathlib: false
    done_through: 0
    status: draft
  HexMvGcdMathlib:
    deps: [HexMvGcd, HexMvPolyMathlib, HexResultantMathlib, HexPolyMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

`HexPolyZGcd` is the arity-one case, called rather than reimplemented;
see "Scope". `HexPolyFp` and `HexModArith` are for the univariate images
over `F_p`.
`HexResultant` is for route 5 and for the `ExactDivLaws` interface.
`HexArith` is for the integer gcd and the extended Euclidean algorithm.
`HexPoly` comes in through `DensePoly`, which `toUnivariate` returns.

Every dependency is `active`, `HexMvPoly` and `HexMvPolyMathlib` at
`done_through: 7`, so nothing here waits on another library's status.
The two new entries stay `draft` until the three additions under
"Additions needed in hex-mv-poly" have landed, since without them
milestone 1 cannot start.

## Why gcd and squarefree decomposition are one library

Squarefree decomposition's only nontrivial dependency is the gcd, its
dependency set is identical, and it is a few hundred lines. Splitting it
out would produce a library with one algorithm, the same dependencies,
and a second round of release plumbing.

The natural seam, if one appears, is not between gcd and squarefree
decomposition. It is between the checker and the routes: `Cert.lean`,
`Divide.lean`, and `Content.lean` carry all the proofs and none of the
search, and `Brown.lean` and `Zippel.lean` carry all the search and none
of the proofs.

## Open questions

- **Whether `LawfulContent` should be proved Mathlib-free.** The SPEC
  takes it as a hypothesis discharged by the companion, which keeps
  milestone 2 small at the cost of leaving Mathlib-free consumers with an
  undischargeable hypothesis. Proving it by induction on the
  arity is the alternative, and it amounts to proving
  `MvPoly n R cmp` is a gcd domain from scratch. Worth revisiting if a
  Mathlib-free consumer appears; nothing currently on the roadmap is one.
- **Which coprimality certificate to make primary.** The modular witness
  is primary above, because its producer is the computation the routes
  already run and its checker touches only small univariate polynomials.
  `splitBezout` needs no prime and no homomorphism, so its soundness
  proof is shorter, but its producer needs the hex-resultant amendment.
  Both constructors are in the type so the decision can be measured.
- **Whether an order-independent normalisation is worth defining.**
  Fixing the sign from the lex-least monomial rather than the
  `cmp`-leading one would make `gcd_reorder` an equality over `ℤ`. It
  costs a scan the current definition does not need, and no consumer has
  asked for the equality.
- **Whether `cancel` needs a reduced kernel closure.** Checking only the
  cofactor identities in the kernel shrinks the proof term. Whether it
  matters depends on certificate sizes in practice.
- **The crossover between routes 3 and 4**, and whether a sparse Hensel
  route should be added as route 6. Both are measurements. Until they are
  taken, the dispatch tries route 3 first for at most four variables and
  route 4 first above that, and the FLINT comparison is scoped to the
  families where the routes correspond.
- **Sparse exponent vectors.** hex-mv-poly leaves open whether a large
  arity with few active variables wants a sparse `Mono`. The sparse gcd
  family here, at 12 variables, is one of the two measurements that would
  settle it.
