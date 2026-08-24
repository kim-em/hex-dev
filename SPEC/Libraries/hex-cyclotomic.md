# hex-cyclotomic (dense integer cyclotomic polynomials, depends on hex-poly-z + hex-int-factor)

`Φₙ` for positive `n` as a dense `ZPoly`, together with the divisor
family `{Φ_d : d ∣ n}` and the factorization `xⁿ − 1 = ∏_{d ∣ n} Φ_d`.
Mathlib-free. The companion `hex-cyclotomic-mathlib` identifies the
computed value with `Polynomial.cyclotomic n ℤ` and transports
irreducibility, the degree formula, and the factorization from Mathlib.

This SPEC expands the "Cyclotomic polynomials" bullet of
[future-work](../future-work.md). The index is always a
`CheckedFactorization` from
[hex-int-factor](hex-int-factor.md), never a bare `Nat`, for the reasons
in "The index is a checked factorization" below.

## Why this library exists

**Cyclotomic polynomials are already in the tree as literals.** They
appear as hard-coded factorisation fixtures, as benchmark inputs for
`hex-berlekamp-zassenhaus`, and as the shape the sparse representation
of [hex-sparse-poly](../../HexSparsePoly/SPEC/hex-sparse-poly.md) is designed around. Nothing
constructs them. A fixture that spells out all 49 coefficients of the
degree-48 `Φ₁₀₅`
is a fixture nobody can extend, and an irreducibility benchmark whose
inputs stop at the degrees somebody was willing to type is a benchmark
with an accidental ceiling.

**They are a standard hard family for integer factorisation of
polynomials.** `Φₙ` is irreducible over `ℚ` of degree `φ(n)`, and for
`p ∤ n` its reduction mod `p` splits into `φ(n)/ord_n(p)` factors of
equal degree, where `ord_n(p)` is the multiplicative order of `p` mod
`n`. When the chosen reduction prime has small `ord_n(p)` that is the
worst case for Berlekamp-Zassenhaus recombination: many modular factors,
no small true factor, and a lattice step that has to run to the end
before it can report "irreducible". The hardness is a property of the
pair `(n, p)` and not of `n` alone. `ord₇(3) = 6`, so `Φ₇` stays
irreducible mod `3` and is an easy input at that prime.

The families the benchmark suite would draw from here combine a large
degree with coefficients that are usually small, which is the shape that
stresses recombination rather than coefficient arithmetic. "Usually" is
the honest word: the heights are not uniformly small, as the Erdős
result recorded under "Complexity" says. Generating these inputs from an
index rather than from a table is what makes the family extensible.

**`xⁿ − 1` is the identity two other libraries want.**
[hex-int-factor](hex-int-factor.md) splits `bⁿ ± 1` before factoring it
and needs the *values* `Φ_d(b)`, which it computes in `Nat` by its own
recursion. The two computations are independent, so they cross-check
each other, and the conformance boundary below is where that happens.

**The construction is small and the index is the expensive part.**
Every route below is a handful of polynomial operations over a divisor
lattice. What is expensive is knowing the divisors, the radical, and
`φ(n)`, all of which are factorization questions. So the whole API is
built on data that has already been factored, and the one entry point
that factors says so in its type.

## Scope

In scope: `xPowSubOne`; the squarefree-kernel construction of `Φₙ` and
the prime-by-prime ladder underneath it; the divisor-recursion route as
the reference specification; the shared divisor family
`cyclotomicDivisors`; the checked forms of both routes and the
reflection of the factorization identity; monicity, the degree formula,
and the normalization statements; evaluation at an integer, which is
inherited from `DensePoly`; and one convenience entry point that factors
its index.

Not in scope: cyclotomic polynomials over coefficient rings other than
`ℤ` (reducing `Φₙ` mod `p` is `DensePoly`'s coefficient map at the call
site, and the result is generally reducible, so there is nothing to
specify here); the values `Φ_d(b)` in `Nat`, which stay in
[hex-int-factor](hex-int-factor.md); cyclotomic fields and their rings
of integers, which are Mathlib's `NumberTheory.Cyclotomic` and have no
executable content here; irreducibility *proofs* in the Mathlib-free
layer, which are not available and are not claimed; and sparse output,
which is an adapter at a consumer and is discussed under "Sparse output
is an adapter, not a dependency".

## The index is a checked factorization

```lean
namespace Hex.ZPoly
open Hex.Nat

def cyclotomic {n : Nat} (F : CheckedFactorization n) : ZPoly
```

Every public function that constructs a cyclotomic polynomial or the
divisor family takes `F : CheckedFactorization n`, and none of them
takes a bare `Nat`. The one public function that does take a bare index
is `xPowSubOne`, which is not a cyclotomic construction: it is
`xⁿ − 1`, it is total, and at `n = 0` it returns `x⁰ − 1 = 0`, which is
the right answer rather than a degenerate one. Three separate things
follow from the rule, and each of them is a requirement the issue behind
this SPEC names.

**Positivity is a consequence, not a hypothesis.**
`checkFactorization` requires `0 < F.subject` as its first condition, so
`CheckedFactorization 0` is uninhabited and no function here has to
answer at `0`. The extraction is one lemma, listed as a prerequisite
below:

```lean
theorem CheckedFactorization.pos {n : Nat} (F : CheckedFactorization n) : 0 < n
```

This is why the API needs neither `0 < n` as an argument nor
`[NeZero n]` as an instance, which is what
[future-work](../future-work.md) proposed before this SPEC existed. Both
would be redundant: the certificate already carries the fact, and a
second copy of it is a second thing a caller has to supply.

`Φ₀` is therefore not defined. Mathlib defines `cyclotomic 0 R = 1`, and
that convention is a choice made at an index where the divisor product
`∏_{d ∈ Nat.divisors 0} Φ_d` is the empty product `1` (Mathlib's
`Nat.divisors 0` is empty by convention, not because `0` has no positive
divisors) while `x⁰ − 1` is `0`, so the
factorization identity fails there whatever value is chosen. The
companion states no correspondence at `0` and does not need one. The
degree formula happens to survive Mathlib's convention, since
`Nat.totient 0 = 0` and `natDegree 1 = 0`, but that agreement is a
coincidence of two definitions rather than a fact about roots of unity.

**`n = 1` is the base case and needs no special handling.** `Φ₁ = x − 1`.
The checked factorization of `1` is the one with an empty factor list,
so `radical F = 1`, the prime ladder is empty, the kernel exponent
`n / radical F` is `1`, and the substitution is the identity. The
divisor recursion agrees: the proper divisors of `1` are none, the empty
product is `1`, and `(x¹ − 1) / 1 = x − 1`. Both routes return `x − 1`
by running their general code, and the conformance list below checks
this rather than trusting it, because an implementation that special-cases
`n = 1` and gets the sign wrong (`1 − x`) would still satisfy the degree
formula and the divisor-count checks.

**Nothing refactorizes.** `cyclotomic` calls no search routine. It reads
the distinct primes and the exponents out of `F`, and the divisor family
below derives a `CheckedFactorization d` for each divisor `d` from `F`
rather than factoring `d` again. The one entry point that factors is
named for it and returns the failure channel that factoring has:

```lean
/-- Factor `n` and construct `Φₙ`. The factorization is the expensive
step and this is the only function here that performs one. -/
def cyclotomicOf? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (ZPoly × Rand)
```

`Rand`, `FactorFailure`, and `defaultFuel` are hex-int-factor's, and the
generator is threaded back out exactly as `factor?` threads it. A
convenience wrapper that swallowed the failure or silently retried would
hide the one cost in this library that is not linear in the output size.

## The two identities

Write `rad n = ∏_{p ∣ n} p` for the squarefree kernel and `φ` for the
totient. Everything below rests on two facts about `Φ`, both stated for
`p` prime and `0 < m`. The positivity is not decoration: `Φ₀` is not
defined here, so an identity mentioning `Φ_m` has to say that `m` is
positive, and every use below satisfies it.

```
(1)  0 < m,  p ∤ m   ⟹   Φ_m(x^p) = Φ_{mp}(x) · Φ_m(x)
(2)  0 < m,  p ∣ m   ⟹   Φ_m(x^p) = Φ_{mp}(x)
```

Identity (2) iterated gives the squarefree-kernel form, which is the one
that makes a large powerful index cheap:

```
0 < n   ⟹   Φₙ(x) = Φ_{rad n}(x^{n / rad n})
```

Identity (1) run over the distinct primes of `n` in ascending order
gives the ladder that computes `Φ_{rad n}` from `Φ₁ = x − 1`: writing
`p₁ < ⋯ < p_k` for those primes and `m_i = p₁ ⋯ p_i`,

```
Φ_{m₀} = Φ₁ = x − 1        Φ_{m_i}(x) = Φ_{m_{i-1}}(x^{p_i}) / Φ_{m_{i-1}}(x)
```

and `m_k = rad n`. Each step is one substitution of `x^{p_i}` and one
division by a monic polynomial. The third identity, the one the
factorization is stated as, is the divisor product:

```
(3)  xⁿ − 1 = ∏_{d ∣ n} Φ_d(x)          for 0 < n
```

Identity (3) rearranged is the reference route: `Φₙ` is the quotient of
`xⁿ − 1` by the product of the `Φ_d` for the proper divisors `d`.

None of (1), (2), or (3) is proved in the Mathlib-free layer at the
point the implementation lands. What the layer has instead is the
checked forms below, which reflect a single run's arithmetic into a
theorem, and the correspondence in the companion, which imports all
three from Mathlib. The Mathlib-free proofs are milestone 4 and the
route to them is sketched under "The identities the Mathlib-free layer
owes".

## The routes

### The ladder, which is the implementation

```lean
/-- `xⁿ − 1`. -/
def xPowSubOne (n : Nat) : ZPoly

/-- `Φ_{rad n}`, the cyclotomic polynomial of the squarefree kernel. -/
def cyclotomicRadical {n : Nat} (F : CheckedFactorization n) : ZPoly

/-- `Φₙ = Φ_{rad n}(x^{n / rad n})`. -/
def cyclotomic {n : Nat} (F : CheckedFactorization n) : ZPoly :=
  (cyclotomicRadical F).substPow (n / radical F)
```

`cyclotomicRadical` runs the ladder over `primes F`, the distinct primes
of `n` in ascending order. Each step substitutes `x^{p_i}` into the
running value and divides by it. `cyclotomic` then applies identity (2)
once, as a single substitution, and that last substitution is where the
output size appears: the ladder works at degree `φ(rad n)` and only the
final spread reaches degree `φ(n)`.

Ascending prime order is what the implementation does, and it is optimal
for the cost model in the complexity table below rather than an
arbitrary choice. The adjacent-exchange argument is under "Open
questions", where what remains open is only whether measured time agrees
with the operation count.

### The divisor recursion, which is the specification

```lean
/-- `Φₙ` by identity (3): the quotient of `xⁿ − 1` by the product of the
`Φ_d` over the proper divisors of `n`. This is the reference route. It
is not the implementation. See the complexity table. -/
def cyclotomicRec {n : Nat} (F : CheckedFactorization n) : ZPoly

theorem cyclotomic_eq_rec {n : Nat} (F : CheckedFactorization n) :
    cyclotomic F = cyclotomicRec F
```

The recursion is over the divisors of `n`, which are enumerated once
from `F` and memoised, so `Φ_d` for a shared divisor `d` is computed
once rather than once per path through the lattice. Without the memo the
recursion is exponential in the number of distinct primes.

`cyclotomic_eq_rec` is the agreement of the two routes and is the
Mathlib-free content of milestone 4. Until it is proved, the conformance
suite checks it on every fixture, which is the ordering design principle
9 prescribes: the two routes agree by measurement first and by proof
last.

### The divisor family

```lean
/-- `(d, Φ_d)` for every divisor `d` of `n`, ascending in `d`, computed
in one pass with shared subresults. -/
def cyclotomicDivisors {n : Nat} (F : CheckedFactorization n) :
    Array (Nat × ZPoly)

theorem cyclotomicDivisors_eq {n : Nat} (F : CheckedFactorization n) :
    cyclotomicDivisors F =
      (divisorsChecked F).map (fun ⟨d, Fd⟩ => (d, cyclotomic Fd))
```

This is what the `bⁿ ± 1` consumer actually wants, and computing the
family together is cheaper than calling `cyclotomic` once per divisor,
because the ladders for the divisors share their prefixes.
`divisorsChecked` is the hex-int-factor prerequisite that supplies a
`CheckedFactorization d` per divisor without a second search. It is
described under "Prerequisite changes in other libraries".

### Routes not taken, and why they are recorded

**The Möbius power-series route.** `Φₙ = ∏_{d ∣ rad n} (x^{n/d} − 1)^{μ(d)}`
can be evaluated as a truncated power series quotient at precision
`φ(n) + 1`, which is the method the fast external implementations use.
It needs a truncated series division, which is
[hex-truncated-series](hex-truncated-series.md), and adding that
dependency for a route whose advantage over the ladder has not been
measured is premature. The bench families below are what decide it. Note
that the term-by-term form is only valid as a single final quotient, the
same caveat [hex-int-factor](hex-int-factor.md) records for the `Nat`
version.

**The sparse power-series route** of Arnold and Monagan, which computes
only the nonzero terms and is the method of choice when `n` is a product
of many odd primes and the degree runs into the millions. It presupposes
the sparse representation and a sparse series division, and it is worth
revisiting only if the squarefree-index bench family shows the ladder
running out of room.

**`Φ_{2m}(x) = Φ_m(−x)` for odd `m > 1`.** A cheap special case that
halves the work when `n` is twice an odd number. The ladder already
handles `p = 2` as its first step, so this identity would only pay if
the primes were taken in a different order, and the SPEC records it as
an optimisation to measure rather than a route. It is false at `m = 1`:
`Φ₁(−x) = −x − 1` is `−Φ₂(x)`, not `Φ₂(x)`, which is the kind of sign
error a "for odd `m`" statement without the `m > 1` invites.

## Exact division, and what is checked

Every division in every route has a monic divisor: `Φ_m` is monic, and
so is a product of monic polynomials. That is what makes the divisions
possible over `ℤ` at all. Two different things could be meant by
discharging the exactness obligation, and this library does both, in two
different functions.

**The total constructor takes `DensePoly.divMod`'s quotient and checks
nothing.** `divMod` is a total function with a defined meaning on every
input, so taking its first component introduces neither an `Option` nor
a fallback value, and design principle 8 does not apply: there is no
`none` branch to classify. Over `ℤ` the field-style `divMod` divides
each leading coefficient by the divisor's, which is `1` here, so the
truncating `Int` division is exact at every step and the quotient is the
true one. What is deferred is a correctness theorem, which is the
ordinary situation, and not a hidden failure case. This is why
`cyclotomic` has the type a mathematical object should have.

`divMod` rather than `divModMonic` because `divModMonic` takes the
monicity proof as an argument (`HexPoly/Euclid/DivGcd.lean:1001`), so a
recursion that called it would have to carry monicity of every
intermediate value at definition time, and monicity of `Φ_m` is a
milestone-4 theorem.

**The two facts this route needs about integer division already exist**,
which is worth stating because it means milestone 4 owes only cyclotomic
theory and no new division theory:

```lean
theorem Hex.ZPoly.divMod_reconstruction_of_monic (target candidate : ZPoly)
    (hmonic : DensePoly.Monic candidate) :
    (DensePoly.divMod target candidate).1 * candidate
      + (DensePoly.divMod target candidate).2 = target

theorem Hex.ZPoly.divMod_eq_mul (target candidate quotient : ZPoly)
    (hpos_lc : 0 < DensePoly.leadingCoeff candidate)
    (hmul : quotient * candidate = target) :
    DensePoly.divMod target candidate = (quotient, 0)
```

(`HexPolyZ/IntegerPolynomial.lean:1359` and `:1470`.) The first is the
unconditional division identity for a monic integer divisor. The second
is the one the correctness proof actually uses: once the cyclotomic
identity supplies an exact factorization `q * Φ_m = Φ_m(x^p)`, this says
the executable `divMod` returns exactly that `q` with zero remainder. So
the obligation "the ladder computes the cyclotomic polynomial" reduces
to the identity and nothing else.

Neither routes through `DensePoly.DivModLaws`, and that matters: there
is no `DivModLaws Int` instance and there cannot be one, since `Int`
division truncates. The whole reason the divisors here are monic is that
it does. The generic
`divModMonic_eq_divMod_of_monic_of_scale`
(`HexPoly/Euclid/DivGcd.lean:1633`) also applies, with `a / 1 = a`
discharging its scale hypothesis, but it carries the extra
`¬ p.degree < q.degree` side condition for `divMod`'s early shortcut, so
the two integer lemmas above are the better citations.

**The checked constructor divides with hex-poly-z's `divExact?`**, which
divides and then verifies, returning `some q` only when `q * g = f`
holds as a checked equality. Its soundness theorem `divExact?_eq` needs
one hypothesis, `g ≠ 0`, and a monic divisor is nonzero, so nothing here
has to carry it further. Since the divisor is monic, that function's
leading-coefficient prefilter never rejects, so its `none` branch is
unreachable on the inputs this library passes. That unreachability is a
theorem about cyclotomic polynomials rather than about division, and it
is not available until milestone 4, which is exactly why the `Option`
is propagated to the caller here instead of being collapsed with a
fallback.

The checked constructor exists for callers who want the arithmetic
verified at run time before the general theorems land, and for the
conformance emitter:

```lean
/-- `Φₙ` with every division in the run verified by one multiplication.
`none` when some division was not exact, which the theory says cannot
happen and this library does not yet prove. -/
def cyclotomicChecked? {n : Nat} (F : CheckedFactorization n) : Option ZPoly

theorem cyclotomicChecked?_eq {n : Nat} {F : CheckedFactorization n} {f : ZPoly}
    (h : cyclotomicChecked? F = some f) : f = cyclotomic F

/-- Reflect identity (3) at this `n`: `∏_{d ∣ n} Φ_d = xⁿ − 1`. -/
def checkCyclotomicProd {n : Nat} (F : CheckedFactorization n) : Bool

theorem prod_cyclotomic_eq {n : Nat} (F : CheckedFactorization n)
    (h : checkCyclotomicProd F = true) :
    ((cyclotomicDivisors F).map (·.2)).foldl (· * ·) 1 = xPowSubOne n
```

`prod_cyclotomic_eq` is a reflection of a decidable equality and nothing
more, so it is available on the day the library compiles. What it buys
is a proof of the factorization of `xⁿ − 1` **for one `n`**, at the cost
of forming a product of degree `n`. A consumer that needs the identity
for a specific modest `n` can have it now. A consumer that needs it for
all `n` waits for milestone 4 or uses the companion. The cost of the
check is stated in the complexity table so that nobody reaches for it
inside a loop.

The extra multiplication per division that `cyclotomicChecked?` performs
costs the same order as the division itself, so the checked route is a
constant factor slower and not asymptotically worse. That is why it is
usable as the fixture emitter's route.

## Normalization

`Φₙ` as returned here is the monic, primitive, integer-coefficient
representative, and it is the only one, so there is no normalization
convention to choose and no associate ambiguity to resolve:

```lean
theorem monic_cyclotomic {n : Nat} (F : CheckedFactorization n) :
    (cyclotomic F).Monic
theorem content_cyclotomic {n : Nat} (F : CheckedFactorization n) :
    ZPoly.content (cyclotomic F) = 1
theorem degree_cyclotomic {n : Nat} (F : CheckedFactorization n) :
    (cyclotomic F).degree? = some (totient F)
```

Three remarks, each of which is a place an implementation or a consumer
can go wrong.

**Monicity is what pins the sign.** `x − 1` and `1 − x` generate the
same ideal and either could be called "the" first cyclotomic
polynomial. Monic picks the first. The whole ladder preserves it:
`Φ₁` is monic, `substPow k` of a monic polynomial is monic for `0 < k`
because the exponent map is then strictly monotone and fixes the leading
term, and the
exact quotient of a monic by a monic is monic because `ℤ` has no zero
divisors and the leading coefficients multiply. That chain is what
`monic_cyclotomic` proves, and it needs the exactness of the division,
so it lands with milestone 4 for the total route and earlier for the
checked route.

**Content one is a consequence of monicity**, not a separate
normalization step. `ZPoly.primitivePart` and `ZPoly.content` are
hex-poly-z's, and nothing here calls them. The statement is recorded
because a caller who reaches this library from
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md) or from Berlekamp-Zassenhaus is used
to content-normalising every integer polynomial it holds, and here that
is a no-op.

**The degree is `φ(n)` and the totient comes from the certificate.**
`totient F` is hex-int-factor's, computed from the exponents in `O(k)`,
so the degree statement needs no second arithmetic function and no
second factorization. This is the reason the degree formula can be
stated in the Mathlib-free layer at all: both sides are executable.

Two further normalization facts are conformance checks rather than
theorems in the first version, because they are cheap to check and their
Mathlib-free proofs are not on the critical path: `Φₙ(0) = 1` for
`n ≥ 2` with `Φ₁(0) = −1`, and `Φₙ` is self-reciprocal for `n ≥ 2`, so
its coefficient list reads the same forwards and backwards. Both catch
the same class of implementation error, an off-by-one in the substitution
or in the divisor set, and neither is caught by the degree formula alone.

## The identities the Mathlib-free layer owes

Milestone 4 is the Mathlib-free proof of `cyclotomic_eq_rec`,
`monic_cyclotomic`, `degree_cyclotomic`, and identity (3). Following
"push sorries earlier", the decomposition is:

1. `squarefree_xPowSubOne`: over `ℚ`, `xⁿ − 1` is coprime to its
   derivative `n·x^{n-1}` for `0 < n`, so it is squarefree. This is the
   one step with existing infrastructure behind it: `DensePoly Rat` has
   `DivModLaws` and `GcdLaws` instances (`HexPolyZ/Rational.lean:1361`
   and `:1434`), so the gcd computation and its maximality are available
   without new machinery.
2. `coprime_cyclotomic`: distinct `Φ_d` and `Φ_e` for `d, e ∣ n` have no
   common nonunit factor over `ℚ`.
3. `dvd_xPowSubOne`: the product of `Φ_d` over the proper divisors of
   `n` divides `xⁿ − 1`. This is the fact that makes the recursion's
   division exact, and it is the hard step. Each factor divides, since
   `Φ_d ∣ x^d − 1 ∣ xⁿ − 1`, and **that is not enough on its own**: a
   product of divisors need not divide. What closes it is 1 and 2
   together, which say the proper-divisor product is the least common
   multiple of the `x^d − 1` rather than merely a common multiple of the
   individual factors. Neither hex-poly nor hex-poly-z exposes a
   polynomial `lcm` API today, so the combining step is stated over
   pairwise coprime factors rather than through an `lcm`, and adding
   `lcm` is a decision for hex-poly rather than a hidden assumption
   here.
4. `substPow_mul` and `degree_substPow`: substitution of `x^k` is a ring
   homomorphism, and for `0 < k` it multiplies degrees by `k`. These are
   hex-poly facts about the new `DensePoly.substPow` and belong there,
   not here.
5. `ladder_step`: identity (1), by induction from 3 and 4.
6. `kernel_step`: identity (2), likewise.
7. `cyclotomic_eq_rec` and the degree formula follow from 5 and 6
   together with two facts about the totient: it is multiplicative on
   coprime arguments, which is what makes the ladder's degrees come out
   as `φ(m_i)`, and `Σ_{d ∣ n} φ(d) = n`, which is what makes the
   proper-divisor product have degree `n − φ(n)`. Neither is currently
   promised by hex-int-factor's divisor API, so both are listed as
   prerequisites below rather than assumed.

Steps 2, 3, 5, and 6 are cyclotomic theory and are real work. The SPEC
records them here rather than leaving them implicit, because the
alternative is a Mathlib-free layer whose only semantics is "whatever
the ladder computes", and the project rule is that the Mathlib-free
library says what its results mean. Until they are proved, the meaning
is carried by the reflected checks and by conformance, and the companion
carries the general statement.

Proof debt does not cross the layer boundary: the companion's proofs
must not cite a `sorry`-carrying Mathlib-free lemma from this list.
Since the companion proves the correspondence directly from Mathlib's
own cyclotomic development and from the executable division and
substitution lemmas, it does not need any of the steps above, and the
two milestones are independent.

## Complexity

`n` the index, `k` the number of distinct primes, `τ` the number of
divisors, `r = rad n`, and costs in coefficient operations on `Int`.
Coefficient sizes are discussed after the table.

| operation | cost |
|---|---|
| `xPowSubOne n` | `O(n)` to write the array |
| ladder step `i` | `O(φ(m_i) · φ(m_{i-1}))` |
| `cyclotomicRadical`, `k ≥ 1` | `O(Σ_i φ(m_i) · φ(m_{i-1}))`, dominated by the last step, `O(φ(r)² / (p_k − 1))` |
| `cyclotomicRadical`, `k = 0` | `O(1)`: the ladder is empty and the answer is `x − 1` |
| final substitution, `1 ≤ k'` where `k' = n / r` | `O(φ(n))`, which is the output size |
| `cyclotomic` | `O(φ(r)² + φ(n))` |
| `cyclotomicRec` at one divisor `d` | `O(d²)`: the proper-divisor product has degree `d − φ(d)` and the division costs `O(φ(d) · (d − φ(d)))` |
| `cyclotomicRec` | `O(n²)`, since `Σ_{d ∣ n} d² < 1.65 n²` |
| `cyclotomicDivisors` | `O(Σ_{d ∣ n} (φ(rad d)² + φ(d)))`, at most `O(τ · φ(r)² + n)` |
| `checkCyclotomicProd` | `O(n²)`: it forms a product of degree `n` |
| `eval` at an integer `b` | `O(φ(n))` `Int` operations, on values of `O(log H(Φₙ) + φ(n) · log(2 + |b|))` bits |

**The ladder against the recursion is the whole design.** For
`n = 2²⁰` the radical is `2`, the ladder computes `Φ₂ = x + 1` and
substitutes once, so the cost is the `2¹⁹ + 1` coefficients of the
answer `x^{524288} + 1`. The recursion at the same index forms products
of degree up to `n` at each of the 21 divisors, which is about `10¹²`
coefficient operations for the same output. That is why `cyclotomicRec`
is the specification and not the implementation, and why
`cyclotomic_eq_rec` is a theorem rather than a definitional unfolding.

**Coefficient growth is written `H(Φₙ)` above rather than bounded,
because it is not bounded by anything simple.** The coefficients of `Φₙ`
are `±1` and `0` whenever `n` has at most two distinct odd prime factors
(Migotti), the first index with a coefficient of absolute value `2` is
`105`, and the height of `Φₙ` is not bounded by any polynomial in `n`
(Erdős). The squarefree-index bench family below is the one where the
family stops being flat and the heights start to matter:
`H(Φ₂₅₅₂₅₅) = 532` and `H(Φ₄₈₄₉₈₄₅) = 669606`. Both still fit a machine
word, so the point of that family is the arithmetic on growing values
rather than a crossing into big-integer territory. For every other
family the coefficients are `0` and `±1` and the cost model above is the
whole story.

**The number of nonzero terms of `Φₙ` equals that of `Φ_{rad n}`**,
because the final substitution only spreads them. That is the fact the
sparse adapter below exploits, and it is also why the dense output can
be almost entirely zeros: `Φ_{2²⁰}` stores 524289 coefficients of which
two are nonzero.

## Sparse output is an adapter, not a dependency

`hex-cyclotomic` does not depend on
[hex-sparse-poly](../../HexSparsePoly/SPEC/hex-sparse-poly.md). Dense `ZPoly` is the default
output because every consumer in the tree today (Berlekamp-Zassenhaus
inputs, the evaluation the factorization split wants, the conformance
fixtures) holds dense polynomials, and because the sparse library's own
SPEC records that dense stays the default.

The adapter is one function at a consumer that already depends on both
libraries, and it is worth writing down because it is the reason
`cyclotomicRadical` is public:

```lean
def cyclotomicSparse {n : Nat} (F : CheckedFactorization n) : SparsePoly Int :=
  (SparsePoly.ofDense (ZPoly.cyclotomicRadical F)).substPow (n / radical F)
```

It runs the same ladder, so its time is the ladder's plus one `O(φ(r))`
scan, and what it saves is the final substitution: it stores at most
`φ(r) + 1` terms and never allocates a `φ(n)`-sized array, against the
dense constructor's `O(φ(n))` for that step. For
`n = 2²⁰` that is two terms against half a million coefficients. The
agreement with the dense constructor is one application of
hex-sparse-poly's `substPow_toDense`:
`(cyclotomicSparse F).toDense = cyclotomic F`.

**Why the adapter is not a module in this library.** Lake has no
conditional dependencies, so a module here that imported
`HexSparsePoly` would make every consumer of `hex-cyclotomic` depend on
it, which is exactly the "hard dependency" this arrangement avoids. It
cannot go in `hex-sparse-poly` either: that library sits below this one
and its SPEC states that nothing in it knows what a cyclotomic
polynomial is. So the adapter belongs to whichever consumer wants it,
and if a second consumer appears, it belongs in a small
`hex-cyclotomic-sparse` library above both. That decision is recorded as
an open question and not taken here.

## Agreement with hex-int-factor's `cyclotomicSplit?`

[hex-int-factor](hex-int-factor.md) splits `bⁿ ± 1` using

```
bⁿ − 1 = ∏_{d ∣ n} Φ_d(b)        bⁿ + 1 = ∏_{d ∣ 2n, d ∤ n} Φ_d(b)
```

and computes each `Φ_d(b)` in `Nat` by its own recursion with one
truncating division per index, checking only the final product. This
library computes the polynomial and evaluates it. The two never call
each other, and where they overlap they must agree:

```
(cyclotomic F_d).eval (b : Int) = (part.value : Int)
```

for every `part` that `cyclotomicSplit? b n sign` returns, where `F_d`
is the checked factorization of `part.index` that `divisorsChecked`
supplies.

**Which parent certificate supplies `F_d` differs by sign.** In the
minus case every part index divides `n`, so one `CheckedFactorization n`
and one `divisorsChecked` call cover the whole split. In the plus case
the indices divide `2n` and generally not `n`, so the driver factors
`2n` once instead and derives the parts from that. Either way the
conformance driver performs one factorization per `(b, n, sign)` row and
no per-divisor search, which is the same discipline the library itself
follows.

This is a differential test of two genuinely different algorithms, and
it is the sharpest one either library has. hex-int-factor's route can
be wrong in a way its own product check does not catch only if two
errors cancel in the product. This comparison is per part, so it does
not have that hole. Conversely a sign error or an off-by-one in the
divisor set here shows up immediately, because the parts are indexed.

Three details the check has to get right:

- **The index sets are part of the claim.** The minus case's part
  indices must be exactly the divisors of `n`, and the plus case's must
  be exactly the divisors of `2n` that do not divide `n`. Checking only
  the values would pass a split that dropped a part whose value is `1`,
  since dropping it leaves the product unchanged, and `Φ_d(b) = 1` does
  happen: `Φ₁(2) = 1`.
- **`Nat` against `Int`.** `Φ_d(b) > 0` for every `b ≥ 2` and `d ≥ 1`,
  so the comparison converts the evaluated `Int` to `Nat` after checking
  positivity, and a non-positive value is a test failure rather than a
  conversion.
- **The driver lives here.** hex-cyclotomic depends on hex-int-factor,
  so its conformance project can import both without a new pin, while
  the reverse would be a dependency cycle. hex-int-factor's own
  `cyclotomic` fixture kind stays as it is.

## Kernel exposure

There is no tactic consumer today, so the kernel requirement is design
principle 11's always-on cross-check discipline plus one real consumer:
`prod_cyclotomic_eq` is a reflection, so a proof that uses it reduces
`checkCyclotomicProd` in the kernel.

What must reduce under `decide`: `xPowSubOne`, `substPow`, the ladder,
`cyclotomic`, `cyclotomicDivisors`, `checkCyclotomicProd`, and the
`DecidableEq` on `ZPoly` that the final comparison uses. Each is
`@[expose]` and a downstream module carries a `decide`-based test that
fails if any of them stops reducing.

The always-on cross-check uses small indices only, `n ≤ 30`, where the
polynomials have degree at most 8 and the products are small. Larger
indices are native-only: reducing a product of degree `10⁴` in the
kernel is not something this library asks anyone to do, and the
complexity table is where a reader sees why.

Equality on `ZPoly` routes through hex-poly's own `DecidableEq` for
`DensePoly`, which already carries the array-equality workaround
recorded in
[progress/lean4-array-decidableeq-module-repro.md](../../progress/lean4-array-decidableeq-module-repro.md).
Nothing new is needed here, and no second instance is declared.

`cyclotomicRec` is in the reduction closure as well, since the
conformance module compares the two routes at small indices with
`#guard`. `cyclotomicOf?` is not: it factors, and search never appears
in a proof term.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). Two Lean drivers:
`conformance/HexCyclotomic/Conformance.lean` for the `#guard` property
checks, registered in `HexConformance`, and
`conformance/HexCyclotomic/EmitFixtures.lean` exposed as
`lean_exe hexcyclotomic_emit_fixtures`. A committed snapshot at
`conformance-fixtures/HexCyclotomic/cyclotomic.jsonl`, an oracle at
`scripts/oracle/cyclotomic_pari.py`, and one tuple appended to `ORACLES`
in `scripts/ci/run_oracles.sh`:

```
"HexCyclotomic|hexcyclotomic_emit_fixtures|scripts/oracle/cyclotomic_pari.py|conformance-fixtures/HexCyclotomic/cyclotomic.jsonl"
```

Fixture kinds: `cyclo` (an index and the coefficient list of `Φₙ`),
`cycloprod` (an index, the divisor list, and the product `∏ Φ_d`), and
`cycloeval` (a base `b`, an index `d`, and `Φ_d(b)`).

**Oracle choice.** PARI's `polcyclo`, which returns `Φₙ` and, given a
second argument, `Φₙ(b)`, so one oracle covers both the polynomial and
the evaluation fixtures. cypari2 is installed by the existing CI
dependency step, so no install change is needed. SymPy's
`cyclotomic_poly` is the second opinion and is also installed. Neither
oracle knows about the factorization identity, so `cycloprod` is checked
against `xⁿ − 1` computed by the oracle rather than against a second
cyclotomic implementation.

**Boundary cases**, which are the ones this SPEC was asked to pin down:

- `n = 1`: `Φ₁ = x − 1`, checked against the literal coefficient array,
  so that a sign error is caught. Also `Φ₁(b) = b − 1` for the
  evaluation kind.
- `n = 2`: `Φ₂ = x + 1`, the first ladder step, and the smallest case
  where the division is not by `1`.
- `CheckedFactorization 0` is uninhabited, so there is no `n = 0`
  fixture and no value to check. What is checked instead is that the
  library exposes no entry point taking a bare index other than
  `cyclotomicOf?`, and that `cyclotomicOf? 0` reports hex-int-factor's
  `FactorStop.zero` rather than returning a polynomial.
- Prime indices `p ≤ 31`: all `p` coefficients equal `1` and the degree
  is `p − 1`.
- Prime powers `2^k` for `k ≤ 12` and `3^k` for `k ≤ 7`: the family
  where the substitution does almost all the work, checked for the
  right degree `φ(n)` and the right two nonzero terms in the `2^k` case.
  The cap is a fixture-size cap and not an interesting boundary: the
  coefficient list *is* the fixture, so `2²⁰` would commit half a
  million entries. Larger indices of this shape are exercised by the
  powerful-index bench family, where the answer is not stored.
- `n = 105`, the first index with a coefficient of absolute value `2`,
  and `n = 385` and `n = 1365`, further squarefree indices with three
  and four odd prime factors.
- `n = 2m` for odd `m > 1`, checking the `Φ_m(−x)` relation as a
  property rather than as a route.
- Self-reciprocity for every fixture with `n ≥ 2`, and `Φₙ(0) = 1` for
  `n ≥ 2` with `Φ₁(0) = −1`.
- `Φₙ(1) = p` when `n = p^k` is a prime power with `n ≥ 2`, and
  `Φₙ(1) = 1` for every other `n ≥ 2`. This is a one-line check that
  catches a wrong divisor set, since it depends on the whole lattice.

**Route-agreement cases.** `cyclotomic` against `cyclotomicRec` for
every `n ≤ 200` and for the selected large indices where the recursion
is still affordable, and `cyclotomicChecked?` returning `some` on all of
them, so that a division that stopped being exact is a test failure and
not a silently wrong answer. `cyclotomicDivisors` against `τ(n)`
separate `cyclotomic` calls, which is the differential test of the
shared computation.

**Identity cases.** `checkCyclotomicProd F = true` for every `n ≤ 200`
and for a sample of highly composite indices up to `5040`, which is the
reflected form of identity (3).

**Cross-library cases.** The `cyclotomicSplit?` agreement described
above, over `b ∈ {2, 3, 5, 7, 10}` and `n ≤ 32`, for both signs, which
is the same grid hex-int-factor's own `b^n ± 1` fixtures use. Also, as a
`#guard` rather than an oracle case, the irreducibility of `Φₙ` for
`n ≤ 40` through Berlekamp-Zassenhaus's `Hex.ZPoly` irreducibility
decision. That check pins the property this library's users care about
most and is not otherwise visible in the Mathlib-free layer.

**The conformance project needs one dependency the library does not.**
The irreducibility check pulls in `hex-berlekamp-zassenhaus`, which
`hex-cyclotomic` does not depend on and must not, since the dependency
runs the other way for the benchmark inputs. The monorepo hides this;
the released split repository would not, so the manifest entry records
the conformance-only pin. This is the same arrangement
[hex-sparse-poly](../../HexSparsePoly/SPEC/hex-sparse-poly.md) makes for `ZMod64`.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexCyclotomic/Bench.lean`. Native only, plus the small kernel
family for the `decide` closure listed under kernel exposure.

Families:

- **powerful-index**: `n = 2^k` for `k ≤ 22` and `n = 2^a · 3^b` with
  `φ(n)` up to `10⁶`. The radical is tiny and the cost should be the
  output size. The required property is that the time is linear in
  `φ(n)` and independent of `k` beyond that.
- **squarefree-index**: `n` the product of the first `j` odd primes for
  `j ≤ 6`, so `n` runs `3, 15, 105, 1155, 15015, 255255`. This is where
  the ladder does all of its work and where the family stops being flat:
  `H(Φ₂₅₅₂₅₅) = 532` against `H(Φ₁₀₅) = 2`. The reported number is time
  against `φ(n)²`. The next member, `4849845`, has `φ(n) = 1658880`,
  `H = 669606`, and a ladder cost around `10¹¹` coefficient operations,
  which is past the CI wallclock cap in
  [SPEC/benchmarking.md](../benchmarking.md), so it belongs to the
  scheduled timing workflow rather than to the merge-blocking one.
- **highly-composite-index**: `n ∈ {5040, 27720, 720720}`, where `τ(n)`
  is large, measuring `cyclotomicDivisors` against `τ(n)` separate
  constructions. The required property is that the shared computation
  wins.
- **route-crossover**: `cyclotomic` against `cyclotomicRec` on every
  family, up to the index where the recursion becomes unaffordable. The
  SPEC's claim is that the ladder wins everywhere, so this family exists
  to falsify it, and a crossover in the recursion's favour at any index
  is a bug report against this SPEC.
- **evaluate**: `Φ_d(b)` for the `bⁿ ± 1` grid, against
  hex-int-factor's `Nat` recursion for the same values. Two
  measurements, because the two libraries answer the same question by
  different routes and the consumer should be told which to call.
- **checked-overhead**: `cyclotomicChecked?` against `cyclotomic`, and
  `checkCyclotomicProd` on its own. The required property is that the
  checked construction is a small constant factor, since the fixture
  emitter uses it.

**Comparators.** PARI's `polcyclo` through cypari2, `informational`: it
is the conformance oracle, and the measurement includes cypari2's
marshalling of a degree-`φ(n)` coefficient vector into Python, so the
ratio does not isolate the algorithm. SymPy's `cyclotomic_poly`,
`informational`, for the same reason and more so. No external comparator
is registered with `class: gating`, and that is the justification.

Two required internal checks, which matter more than the external ones:

- The powerful-index family must be linear in `φ(n)`. A regression here
  means the final substitution started going through `compose` rather
  than a direct spread, which costs a factor of the output degree.
- `cyclotomicDivisors` must cost less than `τ(n)` separate `cyclotomic`
  calls on the highly-composite family. A regression means the shared
  prefixes stopped being shared.

## The Mathlib layer

`hex-cyclotomic-mathlib` identifies the computed polynomial with
Mathlib's:

```lean
namespace HexCyclotomicMathlib
open Polynomial

theorem toPolynomial_cyclotomic {n : Nat} (F : CheckedFactorization n) :
    HexPolyMathlib.toPolynomial (Hex.ZPoly.cyclotomic F) = cyclotomic n ℤ

theorem natDegree_eq {n : Nat} (F : CheckedFactorization n) :
    (HexPolyMathlib.toPolynomial (Hex.ZPoly.cyclotomic F)).natDegree = Nat.totient n

theorem irreducible {n : Nat} (F : CheckedFactorization n) :
    Irreducible (HexPolyMathlib.toPolynomial (Hex.ZPoly.cyclotomic F))

theorem irreducible_rat {n : Nat} (F : CheckedFactorization n) :
    Irreducible ((HexPolyMathlib.toPolynomial (Hex.ZPoly.cyclotomic F)).map
      (Int.castRingHom ℚ))

theorem divisors_index_nodup {n : Nat} (F : CheckedFactorization n) :
    ((Hex.ZPoly.cyclotomicDivisors F).map (·.1)).toList.Nodup

theorem divisors_index_eq {n : Nat} (F : CheckedFactorization n) :
    ((Hex.ZPoly.cyclotomicDivisors F).map (·.1)).toList.toFinset = n.divisors

theorem prod_divisors_eq {n : Nat} (F : CheckedFactorization n) :
    ((Hex.ZPoly.cyclotomicDivisors F).map
        (fun dp => HexPolyMathlib.toPolynomial dp.2)).foldl (· * ·) 1 = X ^ n - 1
```

`toPolynomial_cyclotomic` is the correspondence everything else goes
through, exactly as `factorization_eq` is for
[hex-int-factor](hex-int-factor.md). The rest are short
consequences of it together with Mathlib's `natDegree_cyclotomic`,
`cyclotomic.irreducible`, `cyclotomic.irreducible_rat`, and
`prod_cyclotomic_eq_X_pow_sub_one`. Exact helper names are read from the
pinned Mathlib during implementation. The SPEC does not depend on
remembered names that may be deprecated or absent.

The divisor-product statement is written over the executable array with
the two index theorems supplying the identification of its index set
with `Nat.divisors n`, rather than over `n.divisors` directly. The
reason is that a statement over `n.divisors` would need a function from
a Mathlib divisor to a checked factorization of it, which is a
dependent lookup with a membership proof, and writing the statements
separately keeps the arithmetic content and the index bookkeeping apart.

**`divisors_index_nodup` is not redundant.** Passing to `toFinset`
discards both order and duplicates. Order is harmless, since polynomial
multiplication is commutative and the `foldl` may be reassociated
freely. Duplicates are not: a list with a repeated index has the same
`toFinset` and a different product, so `divisors_index_eq` alone cannot
carry the array fold to Mathlib's `Finset.prod`. The Mathlib-free layer
already has the enumeration fact, since `divisorsChecked` is ascending
in the divisor, so this is a transport rather than new content.

**The proof of the correspondence follows the ladder, not the
recursion.** Mathlib has both halves of it already:
`cyclotomic_expand_eq_cyclotomic_mul` is identity (1) and
`cyclotomic_expand_eq_cyclotomic` is identity (2), both stated with
`Polynomial.expand R p`, which is the Mathlib counterpart of
`DensePoly.substPow`. So the induction over the prime ladder needs three
transported facts and no new cyclotomic theory:

1. `toPolynomial_substPow`, which says `substPow` is `expand`. This is a
   hex-poly-mathlib prerequisite, since it is a fact about a hex-poly
   operation.
2. A statement that the executable division by a monic divisor computes
   the true quotient when the divisor divides the dividend. Mathlib's
   `divByMonic` and `modByMonic` are the target, and hex-poly-mathlib is
   where that transport belongs. `HexPolyMathlib/Euclid.lean` already
   relates the field-style operations, so the monic case is an addition
   to an existing file rather than a new development.
3. `Nat.totient` agreement with hex-int-factor's `totient`, which
   `hex-int-factor-mathlib` already supplies as `totient_eq`, and
   `Nat.divisors` agreement with `divisorsChecked`, which is the
   companion's own small addition beside `divisors_eq`.

The companion does not add a `DecidablePred` instance of any kind, and
it does not redefine `Polynomial.cyclotomic`. Following the project
split, no theorem about `Hex.ZPoly.cyclotomic` belongs here beyond the
correspondence and one consequence per public operation.

## Prerequisite changes in other libraries

**hex-poly** gains a dense substitution of a power of `x`:

```lean
/-- `p(x^k)`: multiply every exponent by `k`. At `k = 0` every exponent
collapses to `0` and the result is the constant `p(1)`. -/
def substPow [Zero R] [Add R] [DecidableEq R] (p : DensePoly R) (k : Nat) :
    DensePoly R

theorem coeff_substPow, eval_substPow, substPow_eq_compose_monomial
theorem degree_substPow (hk : 0 < k), monic_substPow (hk : 0 < k)
```

`[Add R]` is there for `k = 0`, which sums the coefficients. That case
is not reachable from this library, since the kernel exponent
`n / rad n` is at least `1`, but it is reachable from
[hex-sparse-poly](../../HexSparsePoly/SPEC/hex-sparse-poly.md), whose `substPow` takes `[Add R]`
for exactly this reason and whose SPEC lists the collapse as a
canonicalisation case. Mathlib agrees: `Polynomial.expand R 0 f` is
`C (f.eval 1)`. The degree and monicity statements carry `0 < k`, since
at `k = 0` the degree drops to `0` and the constant `p(1)` is not
generally `1`.

The name matches hex-sparse-poly's sparse operation, so the two
libraries state the same fact about the same named thing. It is not
merely a convenience. `compose p (monomial k 1)` computes the same value
by Horner, and `monomial k 1` is a dense array of `k + 1` coefficients
whose zeros the schoolbook multiplication still traverses, so Horner
stage `j` multiplies an array of size `jk` by one of size `k` and the
total is `Θ(d²k²)` for `d = deg p`. The direct spread is `Θ(dk)`, which
is the output size and cannot be improved. The slowdown is therefore a
factor of `Θ(dk)`, the output degree itself. The final ladder step is
the largest polynomial this library ever writes, which is why the factor
matters here and not elsewhere.

**hex-poly-z** must have `divExact?`, which
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md) already schedules as its first
prerequisite and sites in hex-poly-z. This library needs only the monic
case. No new primitive is requested, and in particular no second copy of
exact integer-polynomial division: the count of those in the tree is
already the subject of that SPEC's "`divExact?` is not new either,
quite".

**hex-int-factor** gains three things, all cheap and all derived rather
than searched:

```lean
/-- `0 < n`, from the certificate's own first condition. -/
theorem CheckedFactorization.pos {n : Nat} (F : CheckedFactorization n) : 0 < n

/-- The distinct primes of `n`, ascending. -/
def primes {n : Nat} (F : CheckedFactorization n) : Array Nat

/-- Every divisor of `n` with its factorization, derived from `F`.
Ascending in the divisor. -/
def divisorsChecked {n : Nat} (F : CheckedFactorization n) :
    Array ((d : Nat) × CheckedFactorization d)

theorem divisorsChecked_fst {n : Nat} (F : CheckedFactorization n) :
    (divisorsChecked F).map (·.1) = divisors F
```

and the two totient facts milestone 4 needs, neither of which the
published divisor API promises today:

```lean
/-- `φ` is multiplicative on coprime arguments. -/
theorem totient_mul_of_coprime {a b : Nat} (Fa : CheckedFactorization a)
    (Fb : CheckedFactorization b) (Fab : CheckedFactorization (a * b))
    (h : Nat.Coprime a b) : totient Fab = totient Fa * totient Fb

/-- Gauss: the totients of the divisors sum to the index. -/
theorem sum_totient_divisors {n : Nat} (F : CheckedFactorization n) :
    ((divisorsChecked F).map (fun ⟨_, Fd⟩ => totient Fd)).sum = n
```

Multiplicativity may fall out of the finite-CRT counting argument that
hex-int-factor's own `totient_eq_count` already needs. The divisor sum
does not: nothing in that library requires it. Both belong there rather
than here, since they are statements about the divisor API, and if that
library declines them they become local obligations of milestone 4.

`divisorsChecked` is the requirement that this library not hide a
repeated factorization, and it is the only new API of the three that has
content. Each divisor's factorization is a sublist of `F`'s with
exponents lowered, and the entries with exponent zero dropped. Building
it by re-running `checkFactorization` per divisor would replay every
primality certificate `τ(n)` times, which is the cost this whole API
shape exists to avoid, so the construction supplies the `valid` field by
a proof instead:

```lean
/-- `G` lowers `F`: `G`'s factors are, in order, a sublist of `F`'s
carrying the same primality certificates, every retained exponent is
positive and no larger than `F`'s, and `G.subject` is the resulting
product. -/
def Lowers (G F : Factorization) : Prop

theorem checkFactorization_of_lowers {F G : Factorization}
    (h : checkFactorization F = true) (hG : Lowers G F) :
    checkFactorization G = true
```

The primality certificates are reused
verbatim, the ascending order is inherited, and the product identity
holds by construction of the divisor. That lemma is the whole content of
the prerequisite, and it belongs in hex-int-factor beside
`checkFactorization`'s other soundness theorems, not here.

**hex-poly-mathlib** gains `toPolynomial_substPow` and the monic
division transport described in the Mathlib layer section.

**Ordering.** This library cannot start before hex-int-factor
milestone 2, since it needs the certificate and the divisor-function
API. It does not need hex-int-factor's search routes, so it is not
blocked by ECM or by the cyclotomic split, and the split is not blocked
by this library either: hex-int-factor computes its own values in `Nat`
and the relationship between the two is a conformance boundary, not a
dependency.

## Milestones

1. **The ladder.** `xPowSubOne`, `substPow` in hex-poly,
   `cyclotomicRadical`, `cyclotomic`, `cyclotomicOf?`, and the
   accessors. With the PARI oracle wired and the boundary cases from the
   conformance list written first, since `n = 1` and the prime powers
   are where the routes differ from what an implementation guesses.

2. **The checked construction.** `cyclotomicChecked?` and
   `cyclotomicChecked?_eq`, together with monicity and the degree
   formula along the checked route, where they follow from the verified
   divisions without the general theory.

3. **The divisor family and the reference route.** `divisorsChecked` in
   hex-int-factor with `checkFactorization_of_lowers`, then
   `cyclotomicDivisors`, `checkCyclotomicProd` with its reflection
   theorem, `cyclotomicRec`, and the conformance comparison of the two
   routes. At the end of this milestone the factorization identity is
   checkable at any specific index. `cyclotomicDivisors` comes after
   `divisorsChecked` and not before, since it is the consumer that
   forces it.

4. **The Mathlib-free identities.** `dvd_xPowSubOne`, the ladder and
   kernel steps, `cyclotomic_eq_rec`, `monic_cyclotomic`, and
   `degree_cyclotomic` in their unconditional forms. This is the
   milestone with real proof content and it is scheduled after the
   measurements, per design principle 9.

5. **Benchmarks**, including the route-crossover family that tests this
   SPEC's central claim, and the evaluation comparison with
   hex-int-factor. The measured numbers are written back into the
   complexity section when they exist.

6. **The companion.** `toPolynomial_cyclotomic` first, by induction over
   the ladder through Mathlib's two expand identities, then the degree,
   irreducibility, and divisor-product consequences. Independent of
   milestone 4.

## File organisation

```
HexCyclotomic/
  Basic.lean      -- xPowSubOne, the prime ladder, cyclotomicRadical,
                  --   cyclotomic, cyclotomicOf?, monicity and degree
  Checked.lean    -- cyclotomicChecked?, cyclotomicDivisors,
                  --   checkCyclotomicProd and the reflection theorems
  Spec.lean       -- cyclotomicRec, cyclotomic_eq_rec, the divisor-product
                  --   identity and the lemmas it is decomposed into
HexCyclotomic.lean
HexCyclotomicMathlib/
  Correspondence.lean -- toPolynomial_cyclotomic and its consequences
HexCyclotomicMathlib.lean
```

`Checked.lean` comes before `Spec.lean` because the reflected identity
is what the conformance suite uses while the proofs in `Spec.lean` are
still open.

`libraries.yml` gains:

```yaml
  HexCyclotomic:
    deps: [HexPolyZ, HexIntFactor, HexPoly]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: PARI polcyclo via cypari2
          class: informational
          rationale: "PARI is the conformance oracle and the measurement includes cypari2's marshalling of a degree-phi(n) coefficient vector into Python, so the ratio does not isolate the algorithm."
        - tool: SymPy cyclotomic_poly
          class: informational
          rationale: "SymPy is the second-opinion oracle and is Python, so the ratio is reported for context and does not determine acceptance."
      input_families:
        - name: powerful-index
          description: n = 2^k and 2^a 3^b with phi(n) up to 10^6, where the radical is tiny and the cost should be the output size
        - name: squarefree-index
          description: products of the first j odd primes for j up to 6, where the ladder does all the work and the coefficients grow
        - name: highly-composite-index
          description: n in 5040, 27720, 720720, measuring cyclotomicDivisors against tau(n) separate constructions
        - name: route-crossover
          description: the ladder against the divisor recursion on every family, up to the index where the recursion is unaffordable
        - name: evaluate
          description: Phi_d(b) on the b^n +- 1 grid against hex-int-factor's Nat recursion for the same values
        - name: checked-overhead
          description: the checked construction and the product-identity check against the plain construction
  HexCyclotomicMathlib:
    deps: [HexCyclotomic, HexPolyZMathlib, HexPolyMathlib, HexIntFactorMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

Neither `HexIntFactor` nor `HexPrimality` is in `libraries.yml` yet, so
the dependency claims above are draft prose rather than repository state
until those entries land.

## Open questions

- **Whether the Möbius power-series route is worth the dependency.** It
  is the method the fast external implementations use, and it would make
  `hex-truncated-series` a dependency of this library. The
  squarefree-index and route-crossover families are what decide it. The
  answer is probably "not until an index with `φ(n)` above `10⁶` has a
  consumer", and today none does.
- **Where the sparse adapter lives once there is a second consumer.**
  Inside the consumer is right for one, a `hex-cyclotomic-sparse`
  library above both is right for several, and neither is right for
  none. Recorded so that the first consumer does not quietly add
  `HexSparsePoly` to this library's dependency list.
- **Whether `cyclotomicChecked?` survives milestone 4.** Once
  `cyclotomic_eq_rec` and the exactness lemma are proved, the checked
  construction returns `some` unconditionally and is a slower way to
  compute the same value. The argument for keeping it is that it gives a
  consumer a run-time guarantee without importing the proof, and the
  argument against is that the API should not carry two names for one
  polynomial. The conformance emitter is the deciding consumer.
- **Whether the measured cost of the prime order matches the counted
  one.** The counted cost is settled: ascending is optimal. Writing `A`
  for the totient of the prefix before two adjacent primes `a < b`, the
  two orders cost `A²[(a−1) + (a−1)²(b−1)]` and
  `A²[(b−1) + (b−1)²(a−1)]`, and the second minus the first is
  `A²(b−a)(1 + (a−1)(b−1)) > 0`, so every adjacent exchange out of
  ascending order costs more. What is open is only whether wall time
  agrees, since coefficient sizes and locality are not in the count.
  The squarefree-index family is where a disagreement would show up.
- **Whether `Φₙ` mod `p` deserves an entry point.** Reducing the
  coefficients is a one-line map to `FpPoly p` at the call site, and the
  result is generally reducible, so a named function would suggest a
  property it does not have. If the Berlekamp benchmark inputs end up
  wanting it, it belongs in the benchmark driver rather than in the
  library.
