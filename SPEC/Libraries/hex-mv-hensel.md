# hex-mv-hensel (multivariate Hensel lifting, depends on hex-mv-poly and hex-mv-gcd)

Lifting a factorization of `MvPoly (n+1) Int cmp` from its univariate
image at an evaluation point back to all `n+1` variables, in the form
Wang's EEZ factorization algorithm needs. Mathlib-free. The companion
`hex-mv-hensel-mathlib` states the evaluation ideal and the ideal-adic
congruences in Mathlib's language, transports the checked identities onto
`MvPolynomial (Fin (n+1)) ℤ`, and discharges the coefficient bound that
the Mathlib-free completeness theorem takes as a hypothesis.

This SPEC expands the "Multivariate Hensel lifting" entry in
[future-work](../future-work.md). It depends on the representation fixed
by [hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) and on the exact
division and gcd contract accepted in [hex-mv-gcd](hex-mv-gcd.md). It
does not depend on [hex-hensel](../../HexHensel/SPEC/hex-hensel.md).
"Why hex-hensel is a design model" says exactly why.

## Why this library exists

**Wang's EEZ factorization.** Factoring `f ∈ ℤ[x₁, …, x_v]` in the
standard way means: make `f` squarefree and primitive in a chosen main
variable, evaluate the other variables at an integer point, factor the
resulting univariate polynomial over `ℤ`, and then reconstruct the
multivariate factors from that univariate splitting. The last step is
this library, and it is the only step of the four that has no existing
Hex implementation. Squarefree decomposition, content, and primitive part
are in [hex-mv-gcd](hex-mv-gcd.md). Univariate factorization over `ℤ` is
in
[hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md).

**Specifying the lift before the factorizer.** The lift is where every
hypothesis of the factorization algorithm is actually consumed: which
coprimality is needed, which leading-coefficient data has to be prepared
in advance, how much precision is enough, and which failures mean "try
another point" rather than "the input was wrong". Writing those contracts
down first is what lets `hex-mv-factor` be a search loop over a checked
primitive rather than an algorithm whose correctness argument is spread
across two libraries.

**A decision procedure, not a heuristic.** With the modulus large enough,
`lift` decides whether `f` factors compatibly with the univariate
splitting it was given, and returns the unique such factorization when
one exists. That is a sharper contract than "an attempt that usually
works", and it is what makes the caller's retry policy simple: a rejected
lift is information about the evaluation point, not about the lifting
code.

## Scope

In scope: the evaluation ideal and the coordinate shift that puts it at
the origin, the seeding of starting factors from a univariate image and
prescribed leading coefficients, the univariate and multivariate
polynomial diophantine solvers, the stagewise ideal-adic lift with its
truncation bookkeeping, reconstruction of integer factors by symmetric
representatives, the certificate and its checker, uniqueness, and the
conditional completeness theorem.

Not in scope, and each is named again under "What stays in the downstream
consumer": searching for an evaluation point, factoring the univariate
image, factoring the leading coefficient and deciding how to distribute
it among the factors, the retry policy when a lift is rejected, and
complete multivariate factorization.

Also not in scope: coefficient rings other than `Int`, sparse
interpolation inside the diophantine solver (see "Future extension:
sparse Hensel lifting"), and lifting a factorization of more than two
factors by a product tree, which is what
[hex-hensel](../../HexHensel/SPEC/hex-hensel.md) does univariately and
which the multivariate diophantine solver makes unnecessary here.

**Why `Int` and not a general coefficient ring.** Over a field `K` the
whole modular apparatus below disappears: `K[x_i]` is a principal ideal
domain, the univariate diophantine problem is an ordinary extended
Euclidean solve, and there is no reconstruction step at all. The prime
`p`, the exponent `l`, symmetric representatives, and the coefficient
bound exist solely because `ℤ` is not a field. Generalising later is
therefore a matter of deleting the coefficient direction rather than
abstracting over it, so version one commits to `Int` and states the
field case as an open question instead of paying for an interface that
would have one nontrivial instance.

## Why hex-hensel is a design model

[hex-hensel](../../HexHensel/SPEC/hex-hensel.md) lifts a factorization of
a dense integer polynomial from `mod p^k` to `mod p^(k+1)` or `mod p^(2k)`,
with linear, quadratic, and multifactor entry points. The shape of the
recursion here is the same shape, and reading that library first is the
right way to understand this one. None of its code applies.

**The prime and the lifting direction are decoupled here.** In hex-hensel
the prime does two jobs at once. It makes the residue ring `𝔽_p`, which
is a field, so the Bézout solve behind each correction has a solution.
And it is also the direction the lift moves along. Multivariately those
two jobs come apart. The lift moves along the evaluation ideal
`I = (x_j - a_j : j ≠ i)`, and the prime is still needed, but only for
the first job, to make the univariate coefficient arithmetic invertible.
The working modulus `q = p^l` is therefore **fixed for the whole lift**
and the ideal-adic precision is what grows. Every hex-hensel signature
takes the current exponent `k` as the thing being advanced, so no
hex-hensel entry point has a parameter in the position this library needs
one.

The consequences are concrete, and each is a place where a "just call
hex-hensel" implementation would fail:

1. **The ideal is not principal.** For `v ≥ 3` variables, `I` needs at
   least two generators, so there is no single element to divide the
   error by and no `ZPoly.reduceModPow` analogue. Truncation modulo
   `I^(k+1)` is a linear projection that deletes terms of high degree in
   the non-main variables, not a reduction of coefficients into a range.
   hex-hensel's `ZPoly.Canonical f m` ("every coefficient lies in
   `[0, m)`"), the invariant its whole quadratic path is built on, has no
   counterpart: an ideal-adic residue has no canonical representative
   picked out by an interval.

2. **The correction is a diophantine solve, not a Bézout multiplication.**
   hex-hensel corrects with `s`, `t` satisfying `s g + t h = 1` in
   `𝔽_p[x]`, one multiplication and one monic division per step. The
   correction here has to solve
   `Σ_j Δ_j ∏_{m ≠ j} F_m ≡ c` in a *truncated multivariate* ring, which
   recurses on the number of variables and bottoms out in `r`
   simultaneous univariate divisions. That recursion is the bulk of this
   library and has nothing to correspond to in hex-hensel.

3. **The Bézout data does not change during the lift.** Because the
   modulus is fixed, the univariate witness `(σ_1, …, σ_r)` computed
   once at the start is valid at every step. hex-hensel's `linearLift`
   must update `s` and `t` at every step, and its `quadraticLift` records
   updated Bézout polynomials as part of its output. Reusing that
   machinery would pay for updates that are not needed.

4. **Leading coefficients are not normalised away.** In the univariate
   Berlekamp-Zassenhaus setting the target is made monic first
   (`ZPoly.monicTarget`), so monicity and degree carry the whole
   invariant. Here `lc_{x_i}(f)` is a polynomial in the other variables,
   evaluation does not make it `1`, and it must be *distributed* among
   the factors before the lift starts. "Leading coefficients" below shows
   that this distribution is not a convenience: it is exactly what keeps
   each correction equation inside the degree range where it is solvable.

5. **Quadratic doubling buys much less.** Doubling the ideal-adic
   precision is possible, but the diophantine data it would need is the
   same at every precision (point 3), so doubling saves only the
   per-step product update, while it costs arithmetic on polynomials
   truncated at twice the degree. The linear scheme is what
   implementations use, and this SPEC specifies only the linear scheme.

6. **Failure is a normal outcome.** hex-hensel with coprime input modulo
   `p` always succeeds; the caller chooses `k` and gets a lift. Here the
   lift can be rejected on correct, well-formed input, because the
   evaluation point may split `f` more finely than `f` actually splits.
   The API therefore returns `Except Failure _` where hex-hensel returns
   data, and "Failure cases" says which failures are the caller's to act
   on.

The one place where hex-hensel is close enough to be tempting is the
`p`-adic lift of the univariate witness, under "Producing the witness".
That is thirty lines, hex-hensel does not export the object in the shape
needed, and taking the dependency would import `ZPoly.congr`,
`ZPoly.Canonical`, `WordMod`, and the quadratic path for it. "Open
questions" records the amendment that would change this.

## The evaluation ideal, and shifting it to the origin

Fix the main variable `i : Fin (n+1)`, a comparator `cmp'` on the
remaining `n` variables, and a point `a : Fin n → Int`. The evaluation
ideal is

```text
I = (x_{i.succAbove j} - a j  :  j : Fin n)
```

and `MvPoly (n+1) Int cmp / I` is the univariate ring in `x_i`. The
reindexing `Fin.succAbove i` between the remaining `n` variables and the
original `n+1` is the same one
[hex-mv-poly](../../HexMvPoly/SPEC/hex-mv-poly.md) uses for
`toUnivariate`, and it appears in every statement below that relates a
coefficient back to the polynomial it came from.

The library moves the point to the origin once and works there:

```lean
namespace Hex.MvHensel

/-- Substitute `x_{i.succAbove j} ↦ x_{i.succAbove j} + a j`, fixing the
main variable `x_i`. -/
def shift (i : Fin (n+1)) (a : Fin n → Int)
    (p : MvPoly (n+1) Int cmp) : MvPoly (n+1) Int cmp

/-- `shift i (-a)`. -/
def unshift (i : Fin (n+1)) (a : Fin n → Int)
    (p : MvPoly (n+1) Int cmp) : MvPoly (n+1) Int cmp

/-- The univariate image at the point: evaluate every coefficient of the
recursive view at `a`. -/
def imageAt (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (a : Fin n → Int)
    (p : MvPoly (n+1) Int cmp) : ZPoly

/-- The leading coefficient in the main variable, which is a polynomial
in the remaining variables: `(toUnivariate i cmp' p).leadingCoeff`. -/
def lcIn (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (p : MvPoly (n+1) Int cmp) : MvPoly n Int cmp'
```

```lean
theorem shift_unshift : unshift i a (shift i a p) = p
theorem unshift_shift : shift i a (unshift i a p) = p
theorem shift_mul     : shift i a (p * q) = shift i a p * shift i a q
theorem shift_add     : shift i a (p + q) = shift i a p + shift i a q
theorem degreeOf_shift (j) : degreeOf j (shift i a p) = degreeOf j p
theorem lcIn_shift    : lcIn i cmp' (shift i a p) = shift' a (lcIn i cmp' p)
theorem imageAt_shift : imageAt i cmp' 0 (shift i a p) = imageAt i cmp' a p
```

where `shift'` is the same substitution one arity down. `shift` is a ring
homomorphism and preserves the degree in every variable, both of which
the lift uses constantly. After shifting, `I` is the ideal generated by
the non-main variables, truncation modulo `I^(k+1)` is a restriction on
monomials, and the image at the point is the constant term of the
recursive view.

**The shift is materialised, and that is a cost worth stating.** A
polynomial that is sparse before the substitution is usually dense after
it: each term `x_j^d` becomes `(x_j + a_j)^d`, contributing `d + 1`
terms. So `shift` can multiply the term count by `∏_j (d_j + 1)` in the
worst case, and it is applied to `f` once at the start and inverted on
each returned factor at the end. The intended implementation is a
per-variable Taylor shift by repeated synthetic division, which makes one
pass over the coefficients in the variable being shifted rather than
forming and multiplying out a power of a binomial for every term. That is
why `shift` is defined here rather than left as hex-mv-poly's
`subst (fun j => X j + C (a j))`, which is the same function and a
materially slower way to compute it.

The alternative, keeping the point where it is and extracting Taylor
coefficients at `a` on demand, avoids materialising a dense intermediate
but pays for the coordinate change inside every step of the lift instead.
Which is better depends on the sparsity of the answer and not of the
input, so it is under "Open questions" rather than decided here.

## Truncation and the working modulus

```lean
/-- Delete every term whose degree in the non-main variable `j` exceeds
`d j`. -/
def truncate (i : Fin (n+1)) (d : Fin n → Nat)
    (p : MvPoly (n+1) Int cmp) : MvPoly (n+1) Int cmp

/-- Replace every coefficient by its symmetric representative modulo
`m`, deleting the terms that become zero. -/
def reduceMod (m : Nat) (p : MvPoly (n+1) Int cmp) : MvPoly (n+1) Int cmp

/-- Every coefficient lies in `(-m/2, m/2]`. -/
def SymCanonical (m : Nat) (p : MvPoly (n+1) Int cmp) : Prop

/-- `p` and `q` agree modulo `m` on every monomial whose total degree in
the non-main variables is at most `k`. This is congruence modulo the
ideal `(I^(k+1), m)` in the shifted coordinates. -/
def CongrAt (i : Fin (n+1)) (k : Nat) (m : Nat)
    (p q : MvPoly (n+1) Int cmp) : Prop

/-- `p` and `q` agree modulo `m` on every monomial inside the box
`deg_{y_j} ≤ d j`. This is congruence modulo the ideal
`(y_1^(d 1 + 1), …, y_n^(d n + 1), m)`, which is what `truncate`
computes with. -/
def BoxCongr (i : Fin (n+1)) (d : Fin n → Nat) (m : Nat)
    (p q : MvPoly (n+1) Int cmp) : Prop
```

**The two relations are not the same, and the algorithm achieves the
weaker one.** `truncate` bounds each variable separately, so the ring it
computes in is the box quotient, not `MvPoly / I^(k+1)`. Every monomial
of total degree above `Σ_j d_j` lies outside the box, by pigeonhole, so

```lean
theorem boxCongr_of_congrAt : CongrAt i (Σ_j d j) m p q → BoxCongr i d m p q
```

and the converse fails: with `n = 2` and `d = (1, 1)`, the monomial
`y_1²` is outside the box but has total degree `2 = Σ_j d_j`, so
`CongrAt i 2` still observes it while `BoxCongr i d` does not. Products
of box-truncated factors routinely carry such terms. The stage invariant,
`diophantine_spec`, and the final modular statement are therefore all in
terms of `BoxCongr`. `CongrAt` is kept for the genuinely ideal-adic
statements, which is where the companion's `Ideal.span` phrasing lives.

Nothing is lost by the weaker relation. The true factors lie inside the
box, by the degree argument under "Truncation is sound", and the decision
is the exact product test over `ℤ` rather than any congruence.

`truncate` is `restrictBy` with a monomial predicate, and `reduceMod` is
`mapCoeffs` composed with hex-modular's `symMod`, which deletes cancelled
terms as hex-mv-poly requires. `SymCanonical` is the analogue of
hex-hensel's `ZPoly.Canonical`, with symmetric rather than nonnegative
representatives, because the answer this library reconstructs has
negative coefficients and there is no monic normalisation to hide them
behind.

`reduceMod` is not a ring homomorphism into `MvPoly _ Int _`, so the laws
it satisfies are stated as congruences rather than as equalities of
images:

```lean
theorem congrAt_refl, congrAt_symm, congrAt_trans
theorem congrAt_add  : CongrAt i k m p p' → CongrAt i k m q q' →
    CongrAt i k m (p + q) (p' + q')
theorem congrAt_mul  : CongrAt i k m p p' → CongrAt i k m q q' →
    CongrAt i k m (p * q) (p' * q')
theorem congrAt_reduceMod : CongrAt i k m (reduceMod m p) p
theorem congrAt_mono (h : k' ≤ k) : CongrAt i k m p q → CongrAt i k' m p q
theorem boxCongr_add, boxCongr_mul, boxCongr_reduceMod   -- the same laws
theorem reduceMod_symCanonical : SymCanonical m (reduceMod m p)
theorem reduceMod_id (h : SymCanonical m p) : reduceMod m p = p
```

The working modulus is `q = p^l` for a bounded prime `p` and an exponent
`l ≥ 1`, held as `Nat` and applied to `Int` coefficients. `ZMod64 q` is
not the representation: `l` grows until the reconstruction succeeds, so
`q` routinely exceeds 64 bits. `ZMod64 p` is used, at the residue prime
only, for the `FpPoly p` computation that produces the univariate
witness.

## The input contract

```lean
/-- Where the lift happens: which variable stays, where the others are
evaluated, and the working modulus `prime.m ^ exponent`. -/
structure Setup (n : Nat) where
  main     : Fin (n+1)
  point    : Fin n → Int
  prime    : ZMod64.Prime
  exponent : Nat

def Setup.modulus (s : Setup n) : Nat := s.prime.m ^ s.exponent

/-- The starting data for one lift. `images` is the univariate
factorization at the point, `leading` is the intended leading
coefficient of each factor in the main variable, and `witness` is the
coprimality witness specified below. The three lists have equal length
`r`. -/
structure Input (n : Nat) (cmp : Mono (n+1) → Mono (n+1) → Ordering)
    (cmp' : Mono n → Mono n → Ordering) where
  setup   : Setup n
  target  : MvPoly (n+1) Int cmp
  images  : List ZPoly
  leading : List (MvPoly n Int cmp')
  witness : List ZPoly
```

Write `f` for `target`, `i` for `setup.main`, `a` for `setup.point`,
`p` for `setup.prime.m`, `l` for `setup.exponent`, `q` for
`setup.modulus`, `F_j` for the `j`-th
entry of `images`, `L_j` for the `j`-th entry of `leading`, `σ_j` for the
`j`-th entry of `witness`, and `b_j` for `∏_{m ≠ j} F_m`. Set
`d₁ = degreeOf i f` and `d_j = degreeOf (i.succAbove j) f`.

`valid inp` checks the following, and each check has a `Failure`
constructor:

- **V1 (nondegenerate).** `images.length = leading.length`,
  `images.length = witness.length`, `r ≥ 1`, `l ≥ 1`, `d₁ ≥ 1`, and
  `(F_j).degree ≥ 1` for every `j`.
- **V2 (no degree drop).** `(imageAt i cmp' a f).degree = d₁`.
- **V3 (the image factors).** `∏_j F_j = imageAt i cmp' a f` in `ZPoly`.
- **V4 (leading coefficients).** `∏_j L_j = lcIn i cmp' f` in
  `MvPoly n Int cmp'`, and `MvPoly.eval a L_j = (F_j).leadingCoeff` for
  every `j`.
- **V5 (units at the prime).** `p ∤ (F_j).leadingCoeff` for every `j`.
- **V6 (coprimality).** `Σ_j σ_j b_j ≡ 1 (mod q)` in `ZPoly`, and
  `(σ_j).degree < (F_j).degree` for every `j`.

V1 to V6 are the whole contract. Everything below is proved from them,
and "Are the hypotheses sufficient?" walks the chain.

**The three list lengths are checked, not assumed.** `Input` holds three
independent `List`s, and every indexed statement below is meaningless
without the equalities, so V1 carries them rather than leaving them to
the docstring.

**V2 is redundant and checked anyway.** It follows from V1 and V4:
evaluation is a ring homomorphism, so
`eval a (lcIn i cmp' f) = ∏_j eval a L_j = ∏_j lc F_j`, and each
`lc F_j` is nonzero because `deg F_j ≥ 1`, so the product is nonzero and
the `x_i`-degree cannot drop. It is nevertheless checked first, because
it is one evaluation, and because its failure names the *evaluation
point* while a V4 failure names the *distribution*. Those are different
things for a caller to fix, and merging them would lose the distinction
the `Failure` type exists to carry. `d₁ ≥ 1` is redundant in the same
way, following from V2, V3, and `deg F_j ≥ 1`.

**V5 is not redundant.** V6 alone does not stop `p` from dividing an
individual leading coefficient: `1 + 2x` has a mod-2 unit witness while
losing its degree modulo 2. Division by `F_j` in `(ℤ/q)[x_i]` is what
the univariate solver does, and it needs `lc F_j` invertible.

**V6's degree bound is a normalisation requirement, not a correctness
one.** `solveUni` reduces `σ_j · c` modulo `F_j` regardless, so an
unreduced witness would still give a correct answer. The bound is
required because it keeps the witness the size of the factors rather
than the size of whatever produced it, and because the producer's lift
maintains it for free.

`r = 1` is admitted and degenerate: `b_1 = 1`, the witness is `[1]`, the
solver is the identity, and the only compatible lift is `f` itself. It is
admitted rather than excluded because a caller trying coarser groupings
works its way down to one group.

`deg F_j ≥ 1` is a real restriction. A constant `F_j` makes V6's bound
say `(σ_j).degree < 0`, which no polynomial satisfies. A constant factor
belongs in the content, which hex-mv-gcd's `contentIn` removes before the
lift is called.

**V3 is an identity over `ℤ`, not up to content.** A univariate
factorization routine returns factors together with a leading unit or an
integer content; folding that scalar into one of the `F_j` is the
caller's job, and doing it in the caller is what keeps V4's second
condition an equality rather than a divisibility with a distribution
search attached.

## Coprimality witnesses

The witness is the **partial-fraction tuple**: `(σ_1, …, σ_r)` with

```text
Σ_j σ_j · b_j ≡ 1  (mod q),      deg σ_j < deg F_j,      b_j = ∏_{m ≠ j} F_m.
```

This is one polynomial identity in `ZPoly` after reduction modulo `q`,
so checking it is a multiplication, a sum, and an equality test.

**Why this and not pairwise Bézout identities.** For `r` factors there
are `r(r-1)/2` pairs, and the correction equation is a single equation in
`r` unknowns, so pairwise data would have to be recombined into the tuple
at every solve. The tuple is also strictly the right amount of
information: it *implies* pairwise coprimality, because reducing
`Σ_j σ_j b_j = 1` modulo `F_k` leaves `σ_k b_k ≡ 1`, making `b_k` a unit
modulo `F_k` and hence each `F_m` with `m ≠ k` a unit modulo `F_k`.

**Why a modulus appears at all.** `ℤ[x_i]` is not a Bézout domain, which
is the same fact
[hex-mv-gcd](hex-mv-gcd.md) records under "Bézout does not witness
coprimality here": `x` and `2` are coprime in `ℤ[x]` and
`u · x + v · 2 = 1` has no solution. Over `ℤ/q` with `p` not dividing the
relevant leading coefficients, the identity does have a solution, which
is the entire reason `p` and `l` are part of the setup.

**Checking modulo `q` is stronger than checking modulo `p`.** Reducing
the checked identity from `q` to `p` gives the mod-`p` identity, so the
mod-`p` coprimality that the classical presentation assumes is a
consequence of V6 rather than a separate hypothesis. The converse holds
too, by the usual nilpotence argument that
[hex-hensel-mathlib](../../HexHenselMathlib/SPEC/hex-hensel-mathlib.md)
records as `coprime_mod_p_lifts`, but this library never needs the
converse: the producer computes the tuple at `p` and lifts it, and the
checker replays the lifted identity.

**Coprimality over `ℚ`, which uniqueness needs.** V5 and V6 give more
than they appear to. Reduce V6 modulo `p`; then `F̄_j` and `F̄_k` are
coprime in `𝔽_p[x_i]` for `j ≠ k`. Suppose `F_j` and `F_k` had a common
factor of positive degree over `ℚ`. Clearing denominators and taking the
primitive part (Gauss's lemma, which hex-mv-gcd proves at arity one)
gives a primitive `d ∈ ℤ[x_i]` of positive degree dividing both. Then
`lc(d)` divides `lc(F_j)`, which V5 says is not divisible by `p`, so
`d̄` still has positive degree and divides both `F̄_j` and `F̄_k`, a
contradiction. So:

Writing `ratOf` for the coefficientwise `Int → Rat` map on `DensePoly`:

```lean
theorem coprimeRat_of_witness (h : valid inp = true) (j k) (hjk : j ≠ k) :
    ∃ u v : DensePoly Rat,
      u * ratOf inp.images[j] + v * ratOf inp.images[k] = 1
```

No resultant is needed for this, which is why hex-resultant is not a
dependency. The Gauss's-lemma step is hex-mv-gcd's, at arity one.

Pairwise coprimality over `ℚ` is what `lift_unique` actually uses,
through the tuple it implies: `ℚ[x_i]` is a principal ideal domain, so
pairwise coprime `F_j` have `gcd(b_1, …, b_r) = 1` and a rational
partial-fraction tuple exists. The degree-bounded map is then injective
over `ℚ` by the same Chinese remainder argument `solveUni_unique` uses
over `ℤ/q`.

### Producing the witness

```lean
/-- The partial-fraction tuple modulo `p ^ l`, or `none` when the images
are not pairwise coprime modulo `p` or some leading coefficient is
divisible by `p`. -/
def witnessOf? (s : Setup n) (images : List ZPoly) : Option (List ZPoly)
```

Compute the tuple modulo `p` from `DensePoly.xgcd` over `ZMod64 p`,
accumulating `Σ_{m<j} σ_m b_m` and solving one two-term Bézout problem
per factor, then lift the tuple from `p^k` to `p^(k+1)` by the same
linear correction hex-hensel uses on factors: with
`e = (1 - Σ_j σ_j b_j) / p^k mod p`, solve `Σ_j τ_j b_j ≡ e (mod p)` with
`deg τ_j < deg F_j` using the mod-`p` tuple, and set
`σ_j ← σ_j + p^k τ_j`.

**Do not reduce `σ_j` modulo `F_j` between steps.** That would change
`σ_j` by a multiple of `F_j`, hence change `Σ_j σ_j b_j` by a multiple of
`F = ∏_j F_j`, which is not a multiple of `q` and so breaks the very
identity being lifted. No reduction is needed: each `τ_j` already
satisfies `deg τ_j < deg F_j`, so `σ_j + p^k τ_j` does too, and the
degree bound is maintained for free.

This is a producer in the sense of [design
principle 4](../design-principles.md): `witnessOf?` is unverified, and
`valid` checks its output on every call. A caller that already has the
tuple supplies it directly.

## Leading coefficients

The lift never corrects a leading coefficient. It fixes them at the start
and preserves them exactly, which is what makes every correction equation
solvable.

```lean
/-- Replace the coefficient of `x_i ^ degreeOf i p` in `p` by `L`. -/
def setLc (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (L : MvPoly n Int cmp')
    (p : MvPoly (n+1) Int cmp) : MvPoly (n+1) Int cmp

/-- The starting factor: the univariate image embedded as a polynomial
constant in the non-main variables, with its leading coefficient replaced
by `L`. -/
def seed (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    [IsMonomialOrder cmp'] (L : MvPoly n Int cmp') (F : ZPoly) :
    MvPoly (n+1) Int cmp
```

`seed i cmp' L F` is `ofUnivariate i cmp'` applied to the dense
polynomial whose degree-`k` coefficient is `constIn (F.coeff k)` for
`k < F.degree` and `L` at `k = F.degree`. Under V4 it satisfies

```lean
theorem imageAt_seed  (h : MvPoly.eval a L = F.leadingCoeff) :
    imageAt i cmp' a (seed i cmp' L F) = F
theorem lcIn_seed     (h : L ≠ 0) : lcIn i cmp' (seed i cmp' L F) = L
theorem degreeOf_seed (h : L ≠ 0) : degreeOf i (seed i cmp' L F) = F.degree
```

and the hypothesis on the first is exactly V4's second condition.

**The invariant, and what installs it.** Write `L_j|_t` for `L_j` with
the not-yet-introduced variables `y_{t+1}, …, y_n` set to zero. Every
factor the lift holds during stage `t` satisfies

```text
lcIn i cmp' F_j = L_j|_t        (exactly, at every step of stage t)
degreeOf i F_j  = deg F_j       (exactly, at every step of stage t)
```

A correction has degree in `x_i` strictly below `deg F_j`, so it can
never change the leading coefficient. The `y_t`-dependence of the leading
coefficient is therefore not lifted at all: it is **installed**, by one
`setLc i cmp' (L_j|_t)` at the start of stage `t`, from the `L_j` the
caller supplied. That assignment changes only terms carrying `y_t`, since
`(L_j|_t)|_{y_t = 0} = L_j|_{t-1}`, so it preserves the stage-`t`
precondition. At the start of stage `1`, `L_j|_0` is the constant
`L_j(a) = lc F_j` and the assignment is `seed` itself. After the last
stage `L_j|_n` is `L_j`.

Leaving the leading coefficient to be produced by the corrections is not
an option, and this is the single most common way to get multivariate
Hensel lifting wrong: the corrections are degree-bounded below
`deg F_j` precisely so that they cannot, and relaxing that bound breaks
the solvability argument below.

**Why this makes the correction equations solvable.** With the invariant
in force, at every step of stage `t`,

```text
lcIn i cmp' (∏_j F_j) = ∏_j (L_j|_t) = (∏_j L_j)|_t = lcIn i cmp' f_t
```

by V4, so the leading `x_i`-coefficients of `f_t` and of the current
product cancel identically. Both have `x_i`-degree exactly `d₁`, since
`lcIn f_t` evaluates at `a` to `lcIn(f)(a) ≠ 0` by V2, so

```text
degreeOf i (f_t - ∏_j F_j) < d₁ = deg (∏_j F_j) .
```

The right-hand side of every diophantine problem is a coefficient of that
difference, so it inherits the strict degree bound, and "The univariate
solve" shows the degree-bounded partial-fraction map is a bijection onto
exactly the polynomials with that bound. Drop the leading-coefficient
contract and the error can have degree `d₁` in `x_i`, which is outside
the image of that map, and the lift stalls on a correct input.

**Where the `L_j` come from, and what to do when they cannot be found.**
Wang's method factors `lcIn i cmp' f` multivariately, then uses the
integer values `L_j(a)` and divisibility among the numerical leading
coefficients of the univariate factors to decide which factor of the
leading coefficient belongs to which. Two things follow. The search is
recursive multivariate factorization, so putting it in this library would
make the dependency graph circular. And the search can fail on a given
point even when the point is otherwise fine, in which case the standard
responses are to rescale the univariate factors, to replace `f` by the
monicised `lcIn(f)^(r-1) · f` under the substitution that makes every
factor's leading coefficient equal to `lcIn(f)`, or to choose a different
point. All three are the caller's decisions. The second of them is
expressible as a call to this library on a different input, so nothing is
lost by keeping it outside.

## The correction equations

Work in shifted coordinates, so the point is the origin and `I` is
generated by the non-main variables. Number those variables
`y_1, …, y_n` in the order the lift introduces them.

### The stage loop

The lift introduces one variable at a time, which is Wang's EEZ
arrangement. Write `f_t` for `f` with `y_{t+1}, …, y_n` set to zero, so
that `f_0` is the univariate image and `f_n = f`. The stage-`t`
precondition is

```text
∏_j F_j ≡ f_{t-1}   (mod q),   and every F_j involves only x_i, y_1, …, y_{t-1}.
```

Stage `t` restores the same statement one index up. It first installs the
leading coefficients for this stage, `F_j ← setLc i cmp' (L_j|_t) F_j`,
which changes only terms carrying `y_t` and so preserves the
precondition. Then it runs `k = 0, 1, …, d_t - 1`:

- Form the error `E = f_t - ∏_j F_j`, reduced modulo `q` and truncated to
  the degree bounds `d`.
- Take `c`, the coefficient of `y_t^(k+1)` in `E`, a polynomial in
  `x_i, y_1, …, y_{t-1}`. The precondition and the previous `k` steps say
  every lower coefficient of `E` in `y_t` is zero modulo `q`.
- Solve the multivariate diophantine problem
  `Σ_j Δ_j · b_j ≡ c (mod q)` with `deg_{x_i} Δ_j < deg F_j`, where
  `b_j = ∏_{m ≠ j} F_m|_{y_t = 0}` is built from the factors as they
  stood at the start of the stage.
- Set `F_j ← F_j + y_t^(k+1) · reduceMod q (truncate i d Δ_j)`.

**Only the correction is reduced modulo `q`.** Reducing the whole updated
factor would be wrong twice over. `L_j` may have a coefficient outside
`(-q/2, q/2]`, and then `reduceMod q` changes the leading coefficient,
breaking the invariant the solvability argument rests on. The same
reduction applied to the `y = 0` slice would break `imageAt a F_j = F_j`,
which is checked condition C3 and the `hb` hypothesis of
`diophantine_spec`. Reducing only the correction keeps both exact for
free: the correction carries `y_t^(k+1)`, so it never touches the `y = 0`
slice, and it has `x_i`-degree below `deg F_j`, so it never touches the
leading coefficient. What ends up canonical modulo `q` is the correction
part of each factor, which is exactly the part the lift does not already
know.

Adding `y_t^(k+1) · Δ_j` changes the coefficient of `y_t^(k+1)` in the
product by exactly `Σ_j Δ_j b_j`, since every cross term between two
corrections carries `y_t` to a power of at least `k + 2`. That is why the
`b_j` are taken at `y_t = 0` and why one solve settles one power.

After `d_t` steps the stage-`t` statement holds, and after the last stage
`BoxCongr i d q (∏_j F_j) f` holds, which is the strongest modular
statement the box truncation supports.

Only the base-level witness is fixed data. The `b_j` used at stage `t`
are recomputed from the current factors, because the ring the equation is
solved in changes from stage to stage.

**Truncation is sound, not an approximation.** Any integer factor `g` of
`f` satisfies `deg_{y_j} g ≤ deg_{y_j} f = d_j`, because degrees are
additive in an integral domain and the shift preserves them. So deleting
terms above the bound `d` can never delete part of the answer, and it
bounds the size of every intermediate. The same fact gives the
termination count: stage `t` needs at most `d_t` steps, and the whole
lift needs at most `Σ_{t} d_t` steps, with no coefficient bound involved
in the ideal-adic direction at all.

### The univariate solve

At the base of the recursion the equation is over `ℤ/q`:

```lean
/-- Given `Σ_j σ_j b_j ≡ 1 (mod q)` with unit leading coefficients,
return the unique `(τ_1, …, τ_r)` with `deg τ_j < deg F_j` and
`Σ_j τ_j b_j ≡ c (mod q)`. -/
def solveUni (q : Nat) (images witness : List ZPoly) (c : ZPoly) :
    List ZPoly
```

`τ_j` is the remainder of `σ_j · c` on division by `F_j` in `(ℤ/q)[x_i]`,
which is defined because V5 makes `lc F_j` a unit modulo `q`.

```lean
theorem solveUni_spec (h : valid inp = true)
    (hc : (reduceMod q c).degree < d₁) :
    Σ_j (solveUni q images witness c)[j] * b_j ≡ c  (mod q)
theorem solveUni_degree : ((solveUni q images witness c)[j]).degree < (F j).degree
theorem solveUni_symCanonical : SymCanonical q ((solveUni q images witness c)[j])
theorem solveUni_unique (h : valid inp = true)
    (hτ : ∀ j, (τ j).degree < (F j).degree)
    (hsum : Σ_j τ j * b_j ≡ c (mod q)) :
    ∀ j, τ j ≡ (solveUni q images witness c)[j]  (mod q)
```

**Uniqueness is modulo `q`, and it cannot be an equality of `ZPoly`
values.** The solution is unique as a tuple of residue classes, not as a
tuple of integer polynomials. At `q = 5`, `F_1 = x`, `F_2 = x + 1`,
`σ = (1, -1)`, and `c = 0`, the solver returns `(0, 0)`, but `(5, -5)`
satisfies both degree bounds and `5(x+1) - 5x = 5 ≡ 0`. An equality
conclusion would be false on that input. `solveUni` returns the
symmetric-canonical representative, so the equality *does* hold under the
extra hypothesis `∀ j, SymCanonical q (τ j)`, and that is the form the
lift uses.

The degree hypothesis is stated on `reduceMod q c` rather than on `c`
itself for the same reason: `q · x^(d₁)` has `ZPoly` degree `d₁` and
reduces to zero, so raw degree is the wrong measurement.

The proof is the Chinese remainder argument. Pairwise comaximality (from
V6) gives `(ℤ/q)[x_i]/(F) ≅ ∏_j (ℤ/q)[x_i]/(F_j)` for `F = ∏_j F_j`.
Modulo `F_k` every term of `Σ_j τ_j b_j` except the `k`-th vanishes,
and `τ_k b_k ≡ σ_k c b_k ≡ c (mod F_k)` because `F_k` divides every
other `σ_j b_j`. So `Σ_j τ_j b_j ≡ c (mod F)`. Both sides have degree
below `deg F = d₁`, and `lc F` is a unit, so representatives of that
degree are unique and the congruence modulo `F` is an equality in
`(ℤ/q)[x_i]`. The same uniqueness of low-degree representatives gives
`solveUni_unique`.

Two things about the non-field ring are worth saying, because they look
like obstacles and are not. Division by `F_j` is well defined because
`lc F_j` is a unit, and multiplication by a unit leading coefficient
still adds degrees, so `deg (F h) = deg F + deg h` whenever `h ≠ 0` and
`lc F` is a unit. And the Chinese remainder decomposition needs only
pairwise comaximality, which holds over any commutative ring, not
primality of the modulus.

`solveUni_spec`'s degree hypothesis is not decoration. The map
`(τ_1, …, τ_r) ↦ Σ_j τ_j b_j` on degree-bounded tuples is a bijection
onto the polynomials of degree below `d₁` and not onto all of
`(ℤ/q)[x_i]`, so for a right-hand side whose reduction has degree `d₁` or
more there is no degree-bounded solution at all and the conclusion is
false. That is the hypothesis the leading-coefficient contract exists to
supply.

### The multivariate recursion

```lean
/-- Solve `Σ_j Δ_j b_j ≡ c (mod q)` with `deg_{x_i} Δ_j < deg F_j`, in
the non-main variables truncated by `d`. `none` when a right-hand side
falls outside the solvable degree range. -/
def diophantine (q : Nat) (i : Fin (n+1)) (cmp' : Mono n → Mono n → Ordering)
    (d : Fin n → Nat) (bs : List (MvPoly (n+1) Int cmp))
    (images witness : List ZPoly) (c : MvPoly (n+1) Int cmp) :
    Option (List (MvPoly (n+1) Int cmp))
```

Recursion on the number of non-main variables actually present in the
current stage. With none present the problem is `solveUni`. With `m`
present, set `y_m = 0` to get a problem in `m - 1` variables, solve it,
and then correct in powers of `y_m`: at power `s`, the right-hand side is
the coefficient of `y_m^s` in `c - Σ_j Δ_j b_j` for the partial solution
`Δ` so far, and the correction is another `(m-1)`-variable solve. Stop at
`s = d_m`.

This is the same linear scheme as the stage loop one level down, which is
why the two share `BoxCongr` and the truncation bookkeeping.

```lean
theorem diophantine_spec (h : valid inp = true) (hc : degreeOf i c < d₁)
    (hb    : ∀ j, imageAt i cmp' 0 (bs[j]) = b_j)
    (hbdeg : ∀ j, degreeOf i (bs[j]) + (F j).degree ≤ d₁) :
    ∃ Δ, diophantine … c = some Δ ∧
      BoxCongr i d q (Σ_j Δ[j] * bs[j]) c ∧
      ∀ j, degreeOf i (Δ[j]) < (F j).degree
```

**`hbdeg` is load-bearing and easy to omit.** Agreeing with `b_j` at
`y = 0` says nothing about the higher `y`-coefficients of `bs[j]`, and
those feed the recursion's later right-hand sides. Over `ℤ/5` with
`F_1 = x`, `F_2 = x + 1`, so `d₁ = 2`, take
`bs = [x + 1 + y·x³, x]` and `c = 1`. The images at `y = 0` are the
required `b_j`, and the constant solve returns `(1, -1)`, but the next
residual coefficient is `-x³`, which no pair of constants `δ_1, δ_2` can
write as `δ_1(x+1) + δ_2 x`. The equation is unsolvable within the degree
bounds even though `hb` and `hc` both hold. In the stage loop `hbdeg`
is automatic, since `bs[j] = ∏_{m ≠ j} F_m|_{y_t = 0}` has `x_i`-degree
exactly `d₁ - deg F_j` by the leading-coefficient invariant, but the
public theorem has to say so.

The `none` branch is not reachable from the lift: every right-hand side
the stage loop constructs has `degreeOf i c < d₁` by the
leading-coefficient invariant, and `hb` and `hbdeg` hold by the stage
invariant. The
`Option` is nevertheless in the signature, because `diophantine` is also
a public entry point that the conformance fixtures exercise directly, and
a caller passing an arbitrary `c` has to be told when the equation is
unsolvable rather than handed a junk value.

**There is no total form to classify.** [Design
principle 8](../design-principles.md) requires a total form of a partial
helper to be classified as unreachable or audited, and offers as a third
remedy propagating the `Option` upward until the public API takes
responsibility. This library takes that third route everywhere: no
`diophantine` without the `Option` exists, `lift` discharges the `none`
branch with `diophantine_spec` rather than with a fallback value, and the
one failure that survives to the public API is a `Failure` constructor
rather than a junk result. The same holds of `witnessOf?`, whose `none`
becomes `.notCoprime`.

## Reconstruction and the modulus

After the last stage the factors satisfy `BoxCongr i d q (∏_j F_j) f`,
with every *correction* coefficient in `(-q/2, q/2]` and the `y = 0`
slice and the leading coefficient exact. The reconstruction step is then
just the product test:

```lean
def reconstruct (i) (a) (fs : List (MvPoly (n+1) Int cmp)) :
    List (MvPoly (n+1) Int cmp) := fs.map (unshift i a)
```

and `lift` returns `.ok ⟨reconstruct …⟩` when `∏_j` of the result equals
`f` in `MvPoly (n+1) Int cmp`, and `.error (.reconstruct q)` otherwise.
The test is an exact identity over `ℤ`, so a successful lift needs no
bound at all to be *sound*. The bound is needed only to know when a
failure is final.

**The coefficient bound, and where it is proved.** If a compatible
integer factorization exists, the coefficients the lift has to recover
are bounded in terms of `f`, and once `q` exceeds twice that bound the
symmetric representatives are the true ones and the product test
succeeds. The Mathlib-free layer states the bound as a hypothesis and the
companion discharges it, which is the arrangement [design
principle 2](../design-principles.md) prescribes and the one
[hex-poly-z](../../HexPolyZ/SPEC/hex-poly-z.md) already uses for
Mignotte:

```lean
/-- Every factorization compatible with `inp` has all coefficients of its
*shifted* factors bounded by `B` in absolute value. -/
def BoundsFactors (inp : Input n cmp cmp') (B : Nat) : Prop :=
  ∀ gs, IsLiftOf inp gs → ∀ g ∈ gs, ∀ m,
    (coeff m (shift i a g)).natAbs ≤ B

/-- The computed bound. Mathlib-free arithmetic on the norms and degrees
of the *shifted* target; its correctness is a companion theorem. -/
def coeffBound (inp : Input n cmp cmp') : Nat
```

**The bound is on the shifted factors, and getting that wrong is not a
technicality.** The lift computes in shifted coordinates, so what it has
to distinguish modulo `q` are the coefficients of `shift i a g_j`, not of
`g_j`. Shifting amplifies: with main variable `x`, one other variable
`y`, and `a = 10`, the factors `g = x + y²` and `h = x + 1` have all
coefficients at most `1`, while `shift g = x + y² + 20y + 100` has a
coefficient of `20`. A bound of `1` with `q = 5` would satisfy
`2 · B < q` and still leave `20y` indistinguishable from `0`, so a
completeness theorem stated about the unshifted factors would be false.
`coeffBound` is therefore computed from the *shifted* target, and the
sharper form bounds only the correction `shift i a g_j - seed …`, which
is the part the lift actually reconstructs.

Two derivations are available and they differ enormously in quality.

The one this project can already discharge is **Kronecker substitution
plus the univariate Mignotte bound**. With `D = d₁` and `e_t` the degree
of the shifted target in `y_t`, substitute

```text
x_i ↦ z,      y_t ↦ z^((D + 1) · ∏_{s < t} (e_s + 1)) .
```

The weights must include the main variable's radix. Omitting it sends
both `x_i` and `y_1` to `z` and the substitution is not injective at all:
`x_i - y_1` maps to zero. With the weights above the map is injective on
the monomials of the shifted target and, because a divisor has degree at
most `e_t` in each variable and at most `D` in `x_i`, on the monomials of
every divisor as well. So a factorization maps to a factorization of a
univariate integer polynomial with the same coefficients, and
hex-poly-z's Mignotte bound applies. It is valid and it is very weak: the
image has degree `(D + 1) · ∏_t (e_t + 1) - 1`, so the binomial factor in
Mignotte's bound is astronomically large as soon as there are several
variables.

The one worth having is **Mahler's length inequality**, which bounds the
product of the one-norms of the factors by `2^(D + Σ_t e_t)` times the
one-norm of the shifted target, with the exponent linear in the sum of
the partial degrees rather than in their product. The companion should
prove that form, from
[Mahler, "On some inequalities for polynomials in several variables"](https://ems.press/content/book-chapter-files/27423?nt=1).
The related height inequality that Mahler attributes to Gel'fond is a
different statement, and the two are often conflated under Gel'fond's
name; the length form is the one this library wants.

**The bound does not choose `l` in practice.** Even the length
inequality's exponent is linear in `D + Σ e_t`, so lifting to the proved
bound is not something a caller wants to do. `liftWith` therefore doubles
the exponent on a reconstruction failure and gives up after a configured
number of doublings:

```lean
structure Config where
  doublings : Nat

def Config.default : Config := { doublings := 6 }
```

**The exponent lives in one place.** `inp.setup.exponent` is the exponent
of the first attempt, and it is the one the supplied `witness` is checked
against. On a `.reconstruct` failure, `liftWith` builds a fresh `Input`
at exponent `2 * l` and re-derives the witness with `witnessOf?`, because
a witness valid modulo `p^l` is not valid modulo `p^(2l)`. If
`witnessOf?` declines, the escalation stops and the original
`.reconstruct` failure is returned. A `Config` field naming a second
starting exponent would contradict `setup.exponent` and is deliberately
absent.

A failure after the last doubling is reported as `.reconstruct q` with
the modulus reached, and the caller decides whether to keep doubling or
to change the point.

**The two causes of a reconstruction failure are not separable in
practice.** Either `q` is still too small, or no compatible factorization
exists because the point split `f` more finely than `f` splits. The
proved bound separates them in principle: past `2 · coeffBound inp` a
failure is conclusive, and the point is bad. Since reaching that modulus
is not affordable, the separation is a policy decision rather than a
computation, and it is exactly why the retry policy belongs in the
consumer.

## The certificate and the checker

```lean
/-- The lifted factorization. This is the only data a checker replays. -/
structure Cert (n : Nat) (cmp : Mono (n+1) → Mono (n+1) → Ordering) where
  factors : List (MvPoly (n+1) Int cmp)

def check (inp : Input n cmp cmp') (c : Cert n cmp) : Bool
def valid (inp : Input n cmp cmp') : Bool
def lift (inp : Input n cmp cmp') : Except Failure (Cert n cmp)
def liftWith (cfg : Config) (inp : Input n cmp cmp') : Except Failure (Cert n cmp)
```

`check inp c` requires all of:

- **C1.** `c.factors.length = inp.images.length`.
- **C2.** `∏_j c.factors[j] = inp.target`, an exact identity in
  `MvPoly (n+1) Int cmp`.
- **C3.** `imageAt i cmp' a (c.factors[j]) = F_j` for every `j`.
- **C4.** `lcIn i cmp' (c.factors[j]) = L_j` for every `j`.

`check` does **not** re-run `valid`, and in particular it never mentions
`p`, `l`, or `q`. The working modulus is search: it is how the factors
were found, and it plays no part in the statement that they are correct.

```lean
/-- What a checked certificate witnesses. -/
def IsLiftOf (inp : Input n cmp cmp') (fs : List (MvPoly (n+1) Int cmp)) : Prop :=
  fs.length = inp.images.length ∧
  fs.foldl (· * ·) 1 = inp.target ∧
  (∀ j, imageAt i cmp' a fs[j] = inp.images[j]) ∧
  (∀ j, lcIn i cmp' fs[j] = inp.leading[j])

theorem check_sound : check inp c = true → IsLiftOf inp c.factors
theorem lift_checks : lift inp = .ok c → check inp c = true
```

`check_sound` is immediate: the checked conditions are the definition.
The content of this library is in the theorems that follow.

**Progress.** Under V1 to V6 the lift never stalls: every diophantine
problem it forms is solvable, so the loop always reaches full precision
and the only failure it can report is `.reconstruct`.

```lean
theorem lift_progress (h : valid inp = true) :
    (∃ c, lift inp = .ok c) ∨ (∃ m, lift inp = .error (.reconstruct m))
```

**Uniqueness.** At most one factorization is compatible with the given
data, so the answer does not depend on how it was found.

```lean
theorem lift_unique (h : valid inp = true)
    (h1 : IsLiftOf inp fs) (h2 : IsLiftOf inp gs) : fs = gs
```

The proof is induction on the ideal-adic degree. If `fs` and `gs` agree
modulo `I^(k+1)`, their degree-`(k+1)` differences `Δ_j` satisfy
`Σ_j Δ_j b_j = 0` with `deg_{x_i} Δ_j < deg F_j`, because C4 makes the
leading coefficients agree exactly. The degree-bounded partial-fraction
map over the fraction field of the coefficient ring is injective by
`coprimeRat_of_witness`, so every `Δ_j` is zero. Both sides have bounded
degree in the non-main variables, so the induction terminates. Note that
this argument runs over `ℚ` and needs no coefficient bound, which is why
uniqueness is unconditional while completeness is not.

**Completeness, conditional on the bound.** With a large enough modulus,
`lift` decides whether a compatible factorization exists.

```lean
theorem lift_complete (h : valid inp = true)
    (hB : BoundsFactors inp B) (hq : 2 * B < inp.setup.modulus)
    (hex : ∃ fs, IsLiftOf inp fs) :
    ∃ c, lift inp = .ok c

theorem lift_none (h : valid inp = true)
    (hno : ¬ ∃ fs, IsLiftOf inp fs) :
    ∃ m, lift inp = .error (.reconstruct m)

/-- Past the bound, a reconstruction failure is final: no compatible
factorization exists, and raising the modulus will not find one. -/
theorem no_lift_of_reconstruct (h : valid inp = true)
    (hB : BoundsFactors inp B) (hq : 2 * B < inp.setup.modulus)
    (hfail : lift inp = .error (.reconstruct m)) :
    ¬ ∃ fs, IsLiftOf inp fs
```

`lift_none` needs no bound: `lift_checks` and `check_sound` say that a
successful lift exhibits a compatible factorization, so if none exists
the lift cannot succeed, and `lift_progress` says the failure is
`.reconstruct`. `no_lift_of_reconstruct` is `lift_complete`
contrapositive and does need the bound. The three together are the
decision statement, and the third is the one a caller's retry policy
reads: it is what turns "this failed" into "this point is bad".

### What a checked lift does not prove

C2 is a decomposition, not a factorization into irreducibles. Any `f`
admits the trivial decomposition, and a decomposition into `r` pieces
says nothing about whether those pieces split further. In particular the
lift succeeding does not make the returned factors irreducible, and the
lift failing does not make `f` irreducible: it can equally mean the point
was bad.

That said, the gap is smaller than it sounds, and it is worth recording
exactly, because a consumer that has the extra data should not repeat
work:

```lean
/-- No factorization into two nonunits, stated Mathlib-free so that it
applies to both `ZPoly` and `MvPoly`. The companion identifies it with
Mathlib's `Irreducible`. -/
def Irred [One α] [Mul α] (p : α) : Prop :=
  (¬ ∃ u, p * u = 1) ∧
    ∀ g h, p = g * h → (∃ u, g * u = 1) ∨ (∃ u, h * u = 1)

/-- With a valid input, `f` primitive in the main variable, and every
univariate image irreducible over `ℤ`, a checked lift is a factorization
into irreducibles. -/
theorem irreducible_of_image_irreducible
    (hv : valid inp = true)
    (h : check inp c = true)
    (hprim : contentIn i cmp' inp.target = 1)
    (hirr : ∀ j, Irred (inp.images[j])) :
    ∀ j, Irred (c.factors[j])
```

**`valid` is not droppable here, even though `check_sound` does not need
it.** `check` alone leaves the returned factors free to lose degree in
the main variable at the point, and then the argument below breaks at its
first step. Concretely, with main variable `x` and one other variable
`y`, take `H = x + y·x²` and `K = x + 1`, so
`f = H·K = y·x³ + (1 + y)·x² + x`. Then `f` is primitive in `x` (one
coefficient is `1`), the images at `y = 0` are `x` and `x + 1`, both
irreducible of positive degree, and `L = (y, 1)` makes C1 through C4 all
true. But `H = x · (1 + y·x)` is a product of two nonunits. What fails is
V4's second condition: `eval 0 y = 0` is not `lc x = 1`, so this input is
not `valid`, and `valid` is what rules the case out. The `deg F_j ≥ 1`
hypothesis is part of V1 and so does not need restating.

The argument: suppose `c.factors[j] = g · h` with neither a unit.
`imageAt i cmp' a` is a ring homomorphism, so
`imageAt a g · imageAt a h = F_j`, which is irreducible, and one of the
two, say `imageAt a g`, is `±1`. The leading coefficients satisfy
`lcIn(g) · lcIn(h) = lcIn(c.factors[j]) = L_j` in the domain
`MvPoly n Int cmp'`, and `L_j(a) = lc F_j ≠ 0` by V4 and V1's
`deg F_j ≥ 1`, so `lcIn(g)` does not vanish at `a` and the degree in
`x_i` does not drop under evaluation. Hence `deg_{x_i} g = 0`. A divisor
of `f` that is constant in `x_i` divides every coefficient of
`toUnivariate i cmp' f`, so hex-mv-gcd's `dvd_contentIn` makes it divide
`contentIn i cmp' inp.target = 1`, and `g` is a unit after all.

The two extra hypotheses beyond `valid` are data the library does not
produce. Primitivity comes from hex-mv-gcd, univariate irreducibility
from hex-berlekamp-zassenhaus, and both are inputs the consumer already
has when it is doing a factorization rather than a bare lift. What this
theorem rules out is the reverse reading: the checked certificate alone,
without those hypotheses, certifies a decomposition and nothing more.

## Are the hypotheses sufficient?

Collected, because it is the question this SPEC most needs to have
answered rather than asserted. Every theorem above traces back to V1
through V6 along this chain:

1. V6 gives the tuple identity modulo `q`, hence pairwise comaximality of
   the `F_j` modulo `q`, hence the Chinese remainder decomposition of
   `(ℤ/q)[x_i]/(F)`.
2. V5 makes each `lc F_j` a unit modulo `q`, which is what allows
   division by `F_j` in `(ℤ/q)[x_i]` and what makes degree-bounded
   representatives unique. Both are used in `solveUni_spec`, and the
   second is used again in `solveUni_unique`.
3. V1's `deg F_j ≥ 1` makes the degree bound `deg τ_j < deg F_j`
   satisfiable, and its length equalities make every indexed statement
   meaningful.
4. V4 fixes `lcIn F_j = L_j|_t` through `setLc` and `∏_j L_j = lcIn f`,
   so the `x_i`-leading coefficients cancel identically at every stage
   and `degreeOf i (f_t - ∏_j F_j) < d₁`. That is the hypothesis
   `solveUni_spec` needs on its right-hand side, so it is the
   leading-coefficient contract that makes the correction equations
   solvable rather than merely well-typed. The same invariant gives
   `hbdeg`, since `∏_{m ≠ j} F_m` then has `x_i`-degree exactly
   `d₁ - deg F_j`.
5. V4 with V1 also gives V2, so `d₁ = deg (imageAt i cmp' a f)`, which is
   what identifies the degree bound in step 4 with the degree of the
   modulus `F` in step 1. Without it the two numbers differ and step 4's
   conclusion no longer lands inside step 1's uniqueness range.
6. V3 gives the stage-zero congruence that the loop's induction starts
   from.
7. V5 and V6 together give coprimality over `ℚ`, which is what makes
   `lift_unique` unconditional.

Two conclusions the chain does **not** support, and which earlier drafts
of this design get wrong. Uniqueness at the base is uniqueness of residue
classes, so `solveUni_unique` concludes congruence modulo `q` and only
becomes an equality of `ZPoly` values under the extra
`SymCanonical q` hypothesis. And `lift_complete` needs a bound on the
*shifted* factors, not on the factors themselves, because shifting
amplifies coefficients by a factor depending on the point.

`irreducible_of_image_irreducible` needs `valid` on top of `check`, for
the reason given with the theorem: `check` does not rule out a factor
whose degree in the main variable drops at the point.

Nothing in the chain uses squarefreeness of the univariate image, and the
library deliberately does not require it. What the classical presentation
gets from squarefreeness is pairwise coprimality of the factors, which V6
states directly and more weakly: a caller may lift a coarse splitting
into two coprime blocks just as well as the full splitting into
irreducibles, and `hex-mv-factor` will want that when it recurses.

Nothing in the chain uses primitivity of `f` in the main variable either.
That hypothesis appears once, in `irreducible_of_image_irreducible`,
where it is doing real work.

## Failure cases

```lean
inductive Failure
  | arity
  | degreeDrop
  | imageProduct
  | leadingProduct
  | leadingImage    (j : Nat)
  | primeDividesLc  (j : Nat)
  | notCoprime
  | witnessDegree   (j : Nat)
  | reconstruct     (modulus : Nat)
```

| failure | detected by | what it means | who acts |
|---|---|---|---|
| `.arity` | V1 | mismatched list lengths, degenerate degree, or a constant image | caller built the input wrongly |
| `.degreeDrop` | V2 | `lcIn i cmp' f` vanishes at the point | caller: new point |
| `.imageProduct` | V3 | the images do not multiply to the image of `f` | caller: fold the content or unit into a factor |
| `.leadingProduct` | V4 | `∏_j L_j ≠ lcIn i cmp' f` | caller: redo the distribution |
| `.leadingImage j` | V4 | `L_j(a) ≠ lc F_j` | caller: rescale `F_j`, or redo the distribution |
| `.primeDividesLc j` | V5 | `p ∣ lc F_j` | caller: new prime |
| `.notCoprime` | V6 | the witness identity fails modulo `q` | caller: new prime, or the images are genuinely not coprime |
| `.witnessDegree j` | V6 | `deg σ_j ≥ deg F_j` | producer bug, or a witness supplied by the caller is not reduced |
| `.reconstruct m` | product test | full precision reached, product test failed at modulus `m` | caller: raise `l`, or new point |

The first eight are input validation and are decided before any lifting
happens. `.reconstruct` is the only failure that can occur after work has
been done, and by `lift_progress` it is the only one that can occur at
all once `valid` returns `true`. The middle column is the whole reason
the return type is `Except Failure _` rather than `Option`: the
distinctions in it are what a retry policy dispatches on, and collapsing
them to `none` would force the caller to rediscover them.

`.notCoprime` deserves a note because it has two very different causes.
A prime dividing the resultant of two images makes coprime images look
non-coprime, and a different prime fixes it. Images that share a factor
over `ℤ` are non-coprime at every prime, which usually means the
evaluation point made `f(x_i, a)` non-squarefree, and a different point
is the fix. The library cannot tell these apart from one failed check,
and trying a second prime is the cheap way to find out, which is why the
policy is the caller's.

## What stays in the downstream consumer

`hex-mv-factor` owns all of the following, and this SPEC names them so
that neither library grows into the other:

- **Evaluation-point search.** Choosing `a`, preferring small entries,
  and rejecting points that drop the degree or make the image
  non-squarefree.
- **Univariate factorization.** Calling
  [hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md)
  on `imageAt i cmp' a f` and normalising the result so that V3 holds.
- **Leading-coefficient distribution.** Factoring `lcIn i cmp' f`,
  assigning its factors to the univariate factors, and rescaling so that
  V4 holds. This is recursive multivariate factorization, so it cannot
  live below the factorizer.
- **Retry policy.** Deciding, on `.reconstruct` or `.notCoprime`, whether
  to raise the exponent, change the prime, or change the point, and how
  many times.
- **Recombination.** When the lift of the full univariate splitting
  fails, deciding which coarser groupings to try. A group of univariate
  factors multiplied together is a legitimate `Input` for this library.
- **Content, squarefree decomposition, and the main-variable choice**,
  all of which are hex-mv-gcd calls the factorizer makes before it builds
  an `Input`.

## The API

```lean
namespace Hex.MvHensel

variable {n : Nat} {cmp : Mono (n+1) → Mono (n+1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

-- Coordinates
def shift      (i : Fin (n+1)) (a : Fin n → Int) : MvPoly (n+1) Int cmp → MvPoly (n+1) Int cmp
def unshift    (i : Fin (n+1)) (a : Fin n → Int) : MvPoly (n+1) Int cmp → MvPoly (n+1) Int cmp
def imageAt    (i : Fin (n+1)) (cmp') (a : Fin n → Int) : MvPoly (n+1) Int cmp → ZPoly
def lcIn       (i : Fin (n+1)) (cmp') : MvPoly (n+1) Int cmp → MvPoly n Int cmp'
def truncate   (i : Fin (n+1)) (d : Fin n → Nat) : MvPoly (n+1) Int cmp → MvPoly (n+1) Int cmp
def reduceMod  (m : Nat) : MvPoly (n+1) Int cmp → MvPoly (n+1) Int cmp
def SymCanonical (m : Nat) (p : MvPoly (n+1) Int cmp) : Prop
def CongrAt    (i : Fin (n+1)) (k m : Nat) (p q : MvPoly (n+1) Int cmp) : Prop
def BoxCongr   (i : Fin (n+1)) (d : Fin n → Nat) (m : Nat)
               (p q : MvPoly (n+1) Int cmp) : Prop

-- Setting up
structure Setup (n : Nat)
structure Input (n : Nat) (cmp) (cmp')
structure Cert (n : Nat) (cmp)
structure Config
inductive Failure
def Setup.modulus : Setup n → Nat
def setLc      (i : Fin (n+1)) (cmp') : MvPoly n Int cmp' → MvPoly (n+1) Int cmp → MvPoly (n+1) Int cmp
def seed       (i : Fin (n+1)) (cmp') : MvPoly n Int cmp' → ZPoly → MvPoly (n+1) Int cmp
def witnessOf? (s : Setup n) (images : List ZPoly) : Option (List ZPoly)
def coeffBound (inp : Input n cmp cmp') : Nat

-- Solving
def solveUni     (q : Nat) (images witness : List ZPoly) (c : ZPoly) : List ZPoly
def diophantine  (q : Nat) (i) (cmp') (d : Fin n → Nat)
                 (bs : List (MvPoly (n+1) Int cmp)) (images witness : List ZPoly)
                 (c : MvPoly (n+1) Int cmp) : Option (List (MvPoly (n+1) Int cmp))

-- Lifting
def valid      (inp : Input n cmp cmp') : Bool
def check      (inp : Input n cmp cmp') (c : Cert n cmp) : Bool
def lift       (inp : Input n cmp cmp') : Except Failure (Cert n cmp)
def liftWith   (cfg : Config) (inp : Input n cmp cmp') : Except Failure (Cert n cmp)
def IsLiftOf   (inp : Input n cmp cmp') (fs : List (MvPoly (n+1) Int cmp)) : Prop
def BoundsFactors (inp : Input n cmp cmp') (B : Nat) : Prop
def Irred [One α] [Mul α] (p : α) : Prop
```

`List` rather than `Array` for every piece of certificate data, for the
reason hex-mv-poly records under "Kernel exposure": `Array`'s derived
`DecidableEq` delegates to an unexposed implementation and stalls
`decide`, while `List` equality reduces. The factor count is small, so
the asymptotic argument for `Array` does not apply.

## Complexity

These are **probe counts** in the sense
[hex-mv-gcd](hex-mv-gcd.md) uses: they count univariate diophantine
solves and coefficient operations rather than machine operations, and
they omit the cost of each probe. Multiplying through would require the
cost of arithmetic modulo `q` at `l` words, which depends on the modulus
schedule and is not modelled here.

Parameters: `r` factors, `v = n + 1` variables, `d₁` the degree in the
main variable, `d_j` the degree in non-main variable `j`, `t` terms in
`f`, and `l` the exponent with `q = p^l`.

| operation | algorithm | probe count |
|---|---|---|
| `shift` | per-variable Taylor shift by synthetic division | `O(Σ_j t_j · d_j)` coefficient operations, `t_j` the term count before shifting `y_j` |
| `imageAt` | Horner per `x_i`-slice of the recursive view | `O(t · n)` coefficient operations |
| `lcIn` | the top slice of `toUnivariate` | `O(n · t log t)` machine operations |
| `truncate` | `restrictBy` on the exponent vector | `O(n · t)` machine operations |
| `witnessOf?` | one `FpPoly` xgcd per factor, then `l` linear steps | `r` xgcds plus `r · l` divisions |
| `solveUni` | `r` multiplications and remainders modulo `F_j` | `r` divisions of degree `d₁` |
| `diophantine` at `m` variables | recursion, `d_m + 1` right-hand sides per level | `∏_{k ≤ m} (d_k + 1)` univariate solves |
| one stage-`t` step | one product update and one solve | `∏_{k < t} (d_k + 1)` univariate solves |
| `lift` | `Σ_t d_t` steps | `O(∏_j (d_j + 1))` univariate solves |
| `check` | `r - 1` multiplications and `r` evaluations | `O(r)` polynomial multiplications |

The `shift` row is output-sensitive on purpose. `t_j` grows as variables
are shifted, up to `t · ∏_j (d_j + 1)` in the worst case, so a bound
written in terms of the input term count alone would understate the cost
of a step that has to write its own output.

The last two rows are the design argument. The lift costs the dense size
of the non-main variables, which is the same bound Brown's algorithm
carries in hex-mv-gcd and for the same reason: every route that
interpolates densely pays `∏(d_j + 1)`. The check costs `r`
multiplications and does not depend on `q`, `l`, or the number of steps,
which is what makes replay in the kernel affordable.

## Kernel exposure

The kernel replay closure is `check` and what it calls: `MvPoly`
multiplication and equality, `imageAt`, `lcIn`, `toUnivariate`,
`constIn`, `MvPoly.eval`, `DensePoly` equality and degree, `List` length
and indexing, and the `Mono` operations underneath all of them. Each is
`@[expose]`. Everything hex-mv-poly documents about `Mono n = Vector Nat n`
under its "Kernel exposure" applies unchanged, and this library inherits
its dependency on `HexBasic` through hex-mv-poly rather than acquiring a
new one.

Nothing in `shift`, `unshift`, `truncate`, `reduceMod`, `witnessOf?`,
`solveUni`, `diophantine`, or the stage loop is in that closure. The
whole modular apparatus is search, and it never appears in a proof term.
`SymCanonical`, `CongrAt`, and `BoxCongr` are Props about the search and
are likewise outside.

Two operations that look as though they should be in the closure are
not. `valid` is not: it is the precondition of `lift_progress` and
`lift_complete`, not of `check_sound`, so a consumer replaying a
certificate in the kernel never needs it. And `coeffBound` is not: it
appears only in the hypothesis of `lift_complete`, and a checked
certificate is sound at any modulus.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexMvHensel/EmitFixtures.lean` exposed as
`lean_exe hexmvhensel_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexMvHensel/mvhensel.jsonl`, and an oracle driver
at `scripts/oracle/mvhensel_sympy.py`. One tuple appended to `ORACLES` in
`scripts/ci/run_oracles.sh`, not a new job, per
[SPEC/CI.md](../CI.md):

```
"HexMvHensel|hexmvhensel_emit_fixtures|scripts/oracle/mvhensel_sympy.py|conformance-fixtures/HexMvHensel/mvhensel.jsonl"
```

Two fixture kinds. `mvhensel` carries the arity, the comparator name, the
main variable, the point, the prime and exponent, the target's term list,
the univariate images, and the intended leading coefficients; its result
records either the lifted factors or the `Failure` constructor. `mvdioph`
carries a modulus, the images, and a right-hand side; its result records
the solution tuple or its absence. Both reuse the
`(exponent vector, coefficient)` encoding hex-mv-poly's `mvpoly` fixture
kind defines, so one fixture parser serves them and hex-mv-gcd's three
kinds.

**Oracle choice.** SymPy's `sympy.polys.factortools` exposes exactly the
intermediate functions this library computes: `dup_zz_diophantine` and
`dmp_zz_diophantine` for the two solvers, and
`dmp_zz_wang_hensel_lifting` for the lift itself. That makes the oracle
comparison a per-operation comparison rather than an end-to-end one,
which matters here for the reason hex-mv-gcd gives about its own routes:
a fixture that only checks the final factor list passes even when an
intermediate solve is wrong, since a wrong solve usually makes the lift
fail loudly rather than silently. Comparing the diophantine solutions
directly is what catches a sign error or an off-by-one in the degree
bound.

These are internal SymPy names rather than public API, so the driver
tests one known case at startup and fails with a clear message if the
names have moved, rather than silently reporting a skip. That is the same
policy the `HEX_REQUIRE_ORACLES=1` preflight applies to the SymPy
dependency itself.

**Cases that must be present**, since these are what a plausible
implementation gets wrong:

- `r = 2` through `r = 5`, and `v = 2` through `v = 5`.
- Nonconstant `L_j`, including `L_j` that share a common factor, which is
  the case the distribution search exists for and the case where a lift
  that quietly renormalises leading coefficients gives the wrong answer.
- A target whose leading coefficient in the main variable is a unit, so
  the degenerate monic case is covered beside the general one.
- `d₁ = 1`, where the main variable is linear and every `σ_j` is
  constant.
- A point at which the image is non-squarefree, so V6 fails and the
  reported failure is `.notCoprime`.
- A prime dividing the resultant of two images, where the same input
  succeeds at the next prime. This distinguishes the two causes of
  `.notCoprime`.
- An unlucky point where the image splits but `f` does not: `x₁² + x₂` at
  `x₂ = -1` gives `(x₁ - 1)(x₁ + 1)` while `f` is irreducible. The lift
  must reach full precision and then fail the product test.
- An input whose true factors have coefficients larger than the starting
  modulus allows, so reconstruction fails once and succeeds after
  doubling. The fixture records both the failure at the small exponent
  and the success at the large one.
- A point far from the origin whose shift amplifies coefficients, so that
  a modulus adequate for the unshifted factors is not adequate for the
  shifted ones. `g = x₁ + x₂²`, `h = x₁ + 1` at `x₂ = 10` is the smallest
  case: `shift g` carries a coefficient of `20` while both factors have
  coefficients at most `1`.
- An `L_j` with a coefficient larger than the working modulus, which is
  the case that fails if the stage loop reduces the whole factor instead
  of only the correction.
- A `bs` tuple satisfying the `y = 0` condition but violating the
  main-variable degree bound, exercising `diophantine`'s `none` branch
  directly rather than through the lift.
- Coarse splittings: the same `f` lifted with the images grouped into two
  coprime blocks rather than into all its irreducible factors.
- `r = 1`, the degenerate grouping, where the answer is `f` itself.
- A sparse target whose intermediate products are dense, recording the
  known gap while no sparse route is specified.
- Arity one (`n = 0`), where there is nothing to lift and `lift` returns
  the seeds unchanged, and where the answer must agree with the
  univariate factorization it was handed.

The companion adds randomised comparison against
`MvPolynomial (Fin (n+1)) ℤ` through hex-mv-poly's `equiv`, checking
`IsLiftOf` and the ideal-adic congruences directly rather than through
SymPy's normalisation conventions.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexMvHensel/Bench.lean`. Native only for throughput. A separate
`bench/HexMvHensel/Kernel.lean` suite replays valid and
one-field-corrupted certificates through `by decide +kernel`: two
factors, five factors, nonconstant leading coefficients, and a
certificate whose product identity is off by one coefficient.

Families chosen to isolate the two costs the complexity table separates,
the diophantine recursion and the coefficient arithmetic:

- **Factor count**, `r` from 2 to 8 at fixed degrees. Isolates the `r`
  factor in `solveUni`.
- **Variable count**, `v` from 2 to 6, dense, at low degree. Isolates the
  `∏(d_j + 1)` recursion, and is the family that will move if a sparse
  route is ever added.
- **Main-variable degree**, `d₁` from 5 to 40 at `v = 3`. Isolates the
  univariate divisions.
- **Coefficient size**, the same shapes with coefficients large enough to
  force several doublings of `l`. Times should grow with `l²` and not
  faster; growing faster means a reduction is being redone inside a loop.
- **Nonconstant leading coefficients**, where `lcIn i cmp' f` has many
  terms. Stresses `seed` and the invariant maintenance rather than the
  solver.
- **Sparse target**, where `f` is sparse but the shifted intermediates are
  dense. This records the known gap while no sparse route is specified;
  it does not claim to isolate a route.

**Comparators.** All are `informational`. SymPy is the oracle and is not
a performance comparator, and its `dmp_zz_wang_hensel_lifting` is Python,
so a favourable ratio against it would measure the language and not the
algorithm. FLINT and Singular expose multivariate *factorization*
(`fmpz_mpoly_factor` and `factorize`) but no comparable public
multivariate-Hensel entry point, so any ratio against them compares this
library against a whole factorizer. A required ratio therefore waits for
`hex-mv-factor`, where an end-to-end comparison is meaningful, and this
SPEC assigns none. That is the same reasoning
[hex-mv-gcd](hex-mv-gcd.md) applies to FLINT's `fmpz_mpoly_gcd`.

## The Mathlib layer

`hex-mv-hensel-mathlib` states in Mathlib's language the objects the
Mathlib-free layer computes with, transports the checked identities, and
discharges the coefficient bound. Writing `e` for hex-mv-poly's
`equiv : MvPoly (n+1) Int cmp ≃+* MvPolynomial (Fin (n+1)) ℤ`:

```lean
/-- The evaluation ideal as a Mathlib ideal. -/
def evalIdeal (i : Fin (n+1)) (a : Fin n → Int) :
    Ideal (MvPolynomial (Fin (n+1)) ℤ) :=
  Ideal.span (Set.range fun j => X (i.succAbove j) - C (a j))

/-- The box ideal the truncation actually computes with. -/
def boxIdeal (i : Fin (n+1)) (a : Fin n → Int) (d : Fin n → Nat) :
    Ideal (MvPolynomial (Fin (n+1)) ℤ) :=
  Ideal.span (Set.range fun j => (X (i.succAbove j) - C (a j)) ^ (d j + 1))

theorem congrAt_iff (k m) :
    CongrAt i k m p q ↔
      e p - e q ∈ evalIdeal i a ^ (k+1) ⊔ Ideal.span {(m : MvPolynomial _ ℤ)}

theorem boxCongr_iff (d m) :
    BoxCongr i d m p q ↔
      e p - e q ∈ boxIdeal i a d ⊔ Ideal.span {(m : MvPolynomial _ ℤ)}

theorem evalIdeal_pow_le_boxIdeal : evalIdeal i a ^ (Σ_j d j + 1) ≤ boxIdeal i a d

theorem isLiftOf_iff :
    IsLiftOf inp fs ↔
      (fs.map e).prod = e inp.target ∧
      ∀ j, MvPolynomial.eval (pointOf i a) (e fs[j]) = … ∧ …

theorem quotient_evalIdeal :
    (MvPolynomial (Fin (n+1)) ℤ ⧸ evalIdeal i a) ≃+* Polynomial ℤ

theorem lift_unique' : …    -- lift_unique transported
theorem irreducible_of_image_irreducible' : …

/-- The bound the Mathlib-free `lift_complete` takes as a hypothesis. -/
theorem boundsFactors_coeffBound : BoundsFactors inp (coeffBound inp)
```

`quotient_evalIdeal` is the statement that makes the whole design legible
in Mathlib terms: the evaluation ideal's residue ring is the univariate
polynomial ring, so "lift along `I`" means what it appears to mean. It is
proved from hex-mv-poly-mathlib's `finSuccEquiv` and
`MvPolynomial.eval` rather than reproved from scratch.

`boxIdeal` is the second ideal the design needs, and naming it here is
what stops the two being confused. The truncation bounds each variable
separately, so it is not a power of the evaluation ideal; the containment
runs one way only, which is `evalIdeal_pow_le_boxIdeal` and the
Mathlib-side form of `boxCongr_of_congrAt`.

`boundsFactors_coeffBound` is the one theorem here that is not transport.
It needs a factor-coefficient inequality, which is analysis, so it is on
this side of the boundary by [design
principle 2](../design-principles.md). The Kronecker route reduces it to
[hex-poly-z-mathlib](../../HexPolyZMathlib/SPEC/hex-poly-z-mathlib.md)'s
Mignotte bound and needs, in addition, the combinatorial fact that the
corrected mixed-radix substitution is injective on the monomials of every
divisor of the shifted target. That fact is Mathlib-free and belongs in
the computational library; only the inequality it feeds crosses the
boundary. Whichever route is taken, the statement is about `shift i a g`
rather than `g`, for the reason under "Reconstruction and the modulus".

Following the project split, no other mathematical theorem about
`MvPoly` belongs in the companion, plus one correspondence lemma per
public semantic operation: `shift`, `imageAt`, `lcIn`, `truncate`,
`seed`, `setLc`, `solveUni`, `diophantine`, and `lift`.

## Future extension: sparse Hensel lifting

The dense recursion in `diophantine` costs `∏_j (d_j + 1)` univariate
solves regardless of how many terms the answer has, which is the same
shape of gap
[hex-mv-gcd](hex-mv-gcd.md) records for Zippel interpolation. The known
improvement is to solve each multivariate diophantine problem by sparse
interpolation: learn the support of each `Δ_j` from one solve, then
determine coefficients at later points by solving transposed Vandermonde
systems. Monagan and Tuncer set out a complete version in "Sparse
Multivariate Hensel Lifting: A High-Performance Design and
Implementation" (ICMS 2018) and analyse it in "The complexity of sparse
Hensel lifting and sparse polynomial factorization" (Journal of Symbolic
Computation, 2020).

That paragraph is a research direction and not an implementable route
contract. As with Zippel in hex-mv-gcd, adding it requires a separate
SPEC amendment that fixes the support-learning criterion, the
diversification that makes distinct terms distinguishable, the field-size
policy for the random points, collision handling, and the restart
semantics when a learned support turns out to be wrong, before assigning
it any performance claim. The "sparse target" benchmark family measures
the gap in the meantime.

## Milestones

1. **Coordinates and modulus.** `shift`, `unshift`, `imageAt`, `lcIn`,
   `truncate`, `reduceMod`, `SymCanonical`, `CongrAt`, `BoxCongr`, and
   their laws, including `boxCongr_of_congrAt`.
   This milestone touches no factorization concept and can be built
   against hex-mv-poly alone.

2. **The univariate layer.** `solveUni`, `witnessOf?`, the `p`-adic lift
   of the tuple, and `solveUni_spec` / `solveUni_degree` /
   `solveUni_unique`. The Chinese remainder argument is the substantial
   piece, and it is where V5 and V6 are first consumed.

3. **The multivariate diophantine solver.** `diophantine`, the recursion
   on variables, and `diophantine_spec`. The route-level tests for the
   degree bounds are written before the code.

4. **The lift.** `Setup`, `Input`, `Cert`, `Failure`, `setLc`, `seed`,
   `valid`, the stage loop with its truncation bookkeeping,
   the per-stage leading-coefficient installation, `reconstruct`, `lift`,
   `liftWith`, `check`, `check_sound`, `lift_checks`, and
   `lift_progress`. This is the first usable release.

5. **Uniqueness and conditional completeness.** `coprimeRat_of_witness`,
   `lift_unique`, `BoundsFactors`, `coeffBound`, `lift_complete`,
   `lift_none`, and `irreducible_of_image_irreducible`.

6. **Conformance and benchmarks.** Both fixture kinds, the SymPy oracle
   driver, the kernel replay suite, and the six benchmark families.

7. **The companion.** `evalIdeal`, `quotient_evalIdeal`, `congrAt_iff`,
   the transported statements, and `boundsFactors_coeffBound`. It can
   begin after milestone 4; only the last theorem needs milestone 5.

## File organisation

```
HexMvHensel/
  Shift.lean        -- shift, unshift, imageAt, lcIn, truncate, degree laws
  Modulus.lean      -- reduceMod, SymCanonical, CongrAt, BoxCongr, coeffBound
  Uni.lean          -- solveUni, witnessOf?, the p-adic tuple lift
  Diophantine.lean  -- the multivariate solver and its recursion
  Seed.lean         -- setLc, seed, Setup/Input/Failure, valid
  Lift.lean         -- the stage loop, reconstruction, lift, liftWith
  Cert.lean         -- Cert, check, soundness, uniqueness, irreducibility
HexMvHensel.lean
HexMvHenselMathlib/
  Ideal.lean        -- evalIdeal, quotient_evalIdeal, congrAt_iff
  Correspondence.lean -- transport of IsLiftOf and the per-operation lemmas
  Bound.lean        -- boundsFactors_coeffBound
HexMvHenselMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexMvHensel:
    deps: [HexBasic, HexMvPoly, HexMvGcd, HexPoly, HexPolyZ, HexPolyFp, HexModArith, HexModular, HexArith]
    mathlib: false
    done_through: 0
    status: planned
  HexMvHenselMathlib:
    deps: [HexMvHensel, HexMvPolyMathlib, HexPolyMathlib, HexPolyZMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexMvGcd` supplies exact division, the `GcdOps` and `LawfulGcdOps`
contract on the coefficient ring, `constIn`, and the arity-one Gauss
lemma that `coprimeRat_of_witness` uses; the factorizer above this
library uses it for content and squarefree decomposition as well.
`HexPoly` comes in through `DensePoly`, which `toUnivariate` and every
univariate image return. `HexPolyZ` supplies `ZPoly` and the Mignotte
bound computation behind `coeffBound`. `HexPolyFp` and `HexModArith`
supply the `FpPoly p` extended gcd and the bundled bounded prime that
`witnessOf?` needs. `HexModular` supplies `symMod`. `HexArith` supplies
the integer extended gcd underneath the `ZMod64` inverses.

`HexHensel` is deliberately absent; "Why hex-hensel is a design model"
gives the reasons and "Open questions" records the amendment that would
add it.

`HexMvPoly`, `HexMvPolyMathlib`, `HexPoly`, `HexPolyZ`, `HexPolyFp`,
`HexModArith`, and `HexArith` are active. `HexMvGcd` and `HexModular` are
planned and not yet registered in `libraries.yml`; their entries must be
added and implemented before the block above can be applied. The new
entries are `planned` rather than `draft`, because this SPEC fixes their
required API and milestones. Registration waits until the dependency
entries exist, which is the same position
[hex-mv-gcd](hex-mv-gcd.md) records for itself.

## Why the lift and the diophantine solver are one library

The multivariate diophantine solver has no consumer other than the lift,
its dependency set is identical, and it is a few hundred lines. Splitting
it out would produce a library with one algorithm, the same dependencies,
and a second round of release plumbing.

If a seam appears it is between the coordinate and modulus bookkeeping
(`Shift.lean`, `Modulus.lean`) and the algorithm proper. The first pair
is about `MvPoly` and integer congruences and knows nothing about
factorization; a sparse route would replace `Diophantine.lean` and leave
them untouched.

## Open questions

- **Whether to materialise the shift.** Working in Taylor coordinates at
  the point, without translating `f`, avoids a dense intermediate but
  moves the coordinate change inside every step. Which wins depends on
  the sparsity of the answer rather than of the input, and the "sparse
  target" benchmark family is what would settle it.
- **Whether the coefficient direction should be lifted too.** Starting at
  a small `l` and doubling it *during* the ideal-adic lift, rather than
  restarting, would avoid redoing the early stages. It costs updating the
  witness at every doubling, which is exactly the work point 3 of "Why
  hex-hensel is a design model" observes the fixed-modulus scheme avoids.
  No measurement exists yet.
- **Whether hex-hensel should export the partial-fraction tuple.** If it
  gains a public `r`-factor tuple lifted to `p^l`, this library should
  consume it and delete `witnessOf?`. That is an amendment to hex-hensel
  with one consumer, so it waits for a second one.
- **Which sparse route merits an amendment.** Shared with hex-mv-gcd's
  open question of the same name, and the two should be decided together:
  sparse Hensel lifting is also one of the candidate gcd routes, so a
  single sparse interpolation layer might serve both.
- **Whether a field coefficient version is worth a separate entry
  point.** Over a field the modulus disappears and the algorithm is
  strictly simpler. Whether that is a second entry point here or a
  separate library depends on whether `hex-mv-factor` ever wants to
  factor over `ℚ` or `F_q` directly rather than by clearing denominators.
```
