# hex-poly-z-gcd (modular gcd for `ℤ[x]`, with cofactors and a coprimality witness)

Greatest common divisors of integer polynomials, with cofactors, a
checked coprimality witness, exact division, and the modular algorithms
that make them fast. Mathlib-free. The companion
`hex-poly-z-gcd-mathlib` identifies the results with divisibility in
`Polynomial ℤ` and supplies the decidability instances.

This SPEC expands the "Modular gcd for `ℤ[x]`" bullet of the "Modular
techniques" entry in [future-work](../future-work.md). It uses the
reconstruction operations of [hex-modular](hex-modular.md), and it is the
one-variable case of [hex-mv-gcd](hex-mv-gcd.md), which is written
against a different polynomial representation and should call this
library rather than reimplement it. The relationship is set out under
"Why this is not hex-mv-gcd at arity one".

The future-work bullet says the certificate carries "a Bézout witness
that `f'` and `h'` are coprime". No such witness exists: `ℤ[x]` is not a
Bézout domain, since `x` and `2` are coprime and `u·x + v·2 = 1` has no
solution there. [hex-mv-gcd](hex-mv-gcd.md) already records the
correction for the multivariate case. The univariate replacement is
smaller and better than the multivariate one, and it is specified below
under "The certificate".

## Why this library exists

**The tree has no integer polynomial gcd.** What it has is a gcd over a
field: `HexPolyZ.primitiveSquareFreeDecomposition` maps its input into
`DensePoly Rat` with `toRatPoly`, calls `DensePoly.gcd`, and maps the
result back with `ratPolyPrimitivePart`. That is correct and it is the
algorithm every textbook opens by warning against, because the Euclidean
remainder sequence over `ℚ` produces intermediate rationals whose
numerators and denominators grow exponentially in the degree even when
the input and the answer are small.

**Squarefree decomposition over `ℤ` is the first consumer and the
baseline to beat.** `primitiveSquareFreeDecomposition` is on the
Berlekamp-Zassenhaus path, so its cost is paid by every integer
factorisation, and the benchmark family below measures the new gcd
against exactly that route.

**Berlekamp-Zassenhaus wants it in two more places.** Prime selection
tests whether the image is squarefree, which is a gcd over `F_p` and is
already fast, and the recombination phase divides candidate products into
the input, which is exact division over `ℤ[x]` and belongs here beside
the gcd rather than being reinvented per consumer.

**hex-number-field and hex-resultant want it.** Trager's algorithm
computes gcds of polynomials over a number field by norms and gcds over
`ℚ`, and every gcd it takes is a gcd of integer polynomials after
clearing denominators. The subresultant chain in hex-resultant produces a
last nonzero entry whose primitive part is the gcd, which is the fallback
route below and is much slower than the modular one.

**Rational function simplification wants the cofactors.** `cancel`, the
second piece of the `Together` and `Apart` item in
[future-work](../future-work.md), reduces `p/q` to lowest terms. In one
variable over `ℚ` that is this library plus clearing denominators, and it
is reachable long before the multivariate machinery lands.

## Why this is not hex-mv-gcd at arity one

[hex-mv-gcd](hex-mv-gcd.md) computes gcds of `MvPoly n R cmp`, and at
`n = 1` the mathematics is the same. Three things make a separate library
right anyway.

**The representation is different, and the consumers are on this side of
it.** Berlekamp-Zassenhaus, hex-poly-z, hex-number-field, and
hex-resultant all hold `ZPoly = DensePoly Int`. Routing them through
`MvPoly 1 Int cmp` would mean a conversion per call, a comparator
argument they have no opinion about, and a dependency on hex-mv-poly,
which is a large new representation whose SPEC is still a draft.

**The algorithm is simpler by a whole layer.** Brown's algorithm has two
nested reconstruction schemes: primes with Chinese remaindering for the
coefficients, and evaluation points with interpolation for the variables.
In one variable the second layer is empty. There are no evaluation
points, no bad points, no unlucky points, no leading-coefficient
correction per point, and no interpolation. What remains is a loop over
primes.

**The soundness theorem is unconditional here and conditional there.**
[hex-mv-gcd](hex-mv-gcd.md) states `checkCoprime_sound` under a
`LawfulContent` hypothesis, because its certificate recursion finishes
with "so `d` divides both contents", and the universal property of the
multivariate content is the multivariate gcd's own maximality one
variable down. In one variable the content is an integer and the
corresponding fact is `Int.dvd_gcd`, which hex-arith has. So the
circularity that forces the multivariate statement into the companion
does not arise, and this library's checker is unconditionally sound.

The right relationship is that hex-mv-gcd depends on this library and
calls it for its arity-one case, which is also its recursion's base case
in the main variable.

## Scope

In scope: gcd with cofactors, gcd of a list, lcm, exact division and its
`Option` form, divisibility, coprimality testing with a witness, and the
`DensePoly Rat` wrapper that clears denominators and calls the integer
routine.

Not in scope: squarefree decomposition, which stays in hex-poly-z and
becomes faster by calling this library; factorisation, which is
hex-berlekamp-zassenhaus; resultants, which are hex-resultant; and
anything multivariate.

## Exact division

Every check here runs an exact division, so it is specified before the
gcd.

```lean
namespace Hex.ZPoly

/-- The exact quotient `f / g`, or `none` when `g = 0` or `g ∤ f`. -/
def divExact? (f g : ZPoly) : Option ZPoly

instance : Dvd ZPoly
instance (f g : ZPoly) : Decidable (g ∣ f)

theorem divExact?_zero_right : divExact? f 0 = none
theorem divExact?_eq (hg : g ≠ 0) : divExact? f g = some q ↔ f = q * g
theorem divExact?_isSome_of_dvd (hg : g ≠ 0) : g ∣ f → (divExact? f g).isSome
```

The `g ≠ 0` hypothesis on `divExact?_eq` is not decoration: at `f = 0`
and `g = 0` the right-hand side holds for every `q`, and a deterministic
`Option` returns at most one, so the unconditional biconditional is
false. This is the same statement [hex-mv-gcd](hex-mv-gcd.md) makes about
its own `divExact?`, and the two should be provable by the same argument
in different representations.

`divExact?` fails as soon as a leading coefficient fails to divide,
rather than dividing to completion and testing the remainder. Trial
division dominates the running time of a modular gcd whenever the gcd is
large, so the cheap rejections matter: the degree comparison, the
divisibility of the leading coefficients, the divisibility of the
contents, and the divisibility of the values at one small integer each
reject without allocating a quotient.

## The certificate

The design is one verified checker and several unverified candidate
producers, following design principle 4. Every prime choice, evaluation
point, and retry budget below is outside the proof.

### What "greatest" needs

`f = g·f'` and `h = g·h'` are two exact divisions, and they establish
`g ∣ f` and `g ∣ h` and nothing more. Any common divisor satisfies them,
`1` included. The second witness the certificate must carry is that the
cofactors `f'` and `h'` have no nonunit common divisor.

### The witness

Fix a prime `p` with `p ∤ lc f'` and `p ∤ lc h'`. Reduce both cofactors
into `FpPoly p` and exhibit `α, β` with `α · f'ₚ + β · h'ₚ = 1`. Then
exhibit that the integer contents of `f'` and `h'` are coprime.

```lean
structure GcdCert where
  gcd  : ZPoly
  cofL : ZPoly
  cofR : ZPoly
  prime : Hex.Modular.PrimeModulus
  alpha : FpPoly prime.m
  beta  : FpPoly prime.m

def checkGcd (f h : ZPoly) (c : GcdCert) : Bool

theorem checkGcd_sound (hc : checkGcd f h c = true) :
    f = c.gcd * c.cofL ∧ h = c.gcd * c.cofR ∧
      ∀ d : ZPoly, d ∣ c.cofL → d ∣ c.cofR → IsUnit d
```

`checkGcd` verifies, cheapest first: that `c.gcd * c.cofL = f` and
`c.gcd * c.cofR = h`; that `c.gcd` is normalised (positive leading
coefficient, positive content); that `Int.gcd (content cofL)
(content cofR) = 1`; that reduction modulo `p` preserves both cofactor
degrees; and that `alpha * cofLₚ + beta * cofRₚ = 1` in `FpPoly p`.

The soundness argument, in full, because it is short and because it is
the whole content of the design. Let `d` divide both cofactors, say
`f' = d·e`. Reduction modulo `p` is a ring homomorphism, so
`f'ₚ = dₚ · eₚ`. `F_p` is a field, so degrees add in `FpPoly p`, and
degrees add in `ℤ[x]` because `ℤ` is a domain, so

```
deg f' = deg f'ₚ = deg dₚ + deg eₚ ≤ deg d + deg e = deg f',
```

using the checked degree preservation on the left. So every inequality is
an equality and `deg dₚ = deg d`. Now `dₚ` divides
`α·f'ₚ + β·h'ₚ = 1`, so `dₚ` is a unit and `deg d = 0`. So `d` is an
integer, dividing both contents, which are coprime, so `d = ±1`.

The argument uses `F_p[x]` being a domain, which is where primality
enters, and it uses `Int.dvd_gcd`, which hex-arith has. There is no
hypothesis and no companion obligation.

**The prime should be the smallest usable one.**
[hex-modular](hex-modular.md) measures the cost of a kernel-replayed
primality proof: 0.04 s at 16 bits and 6.2 s at 31 bits. A certificate
replayed by `decide +kernel` pays that, and this certificate names a
prime, so the producer tries small primes first. Any prime not dividing
either leading coefficient works, so a small one almost always exists,
and when it does not the certificate is still valid and merely more
expensive to replay.

The rule is a consequence of trial division rather than of the
certificate design. The "Better primality" item in
[future-work](../future-work.md) points at Pocklington certificates,
whose checker is a handful of modular exponentiations, and once one
exists a certificate field replaces the `Hex.Nat.Prime` field here and
the size preference goes away. The
`GcdCert` field is written as `Hex.Modular.PrimeModulus` so that the
change is confined to how that structure carries its evidence.

### What the checker establishes and what it does not

```lean
/-- The cofactor identities together with coprimality of the cofactors. -/
def CoprimeCofactors (f h g : ZPoly) : Prop :=
  ∃ f' h', f = g * f' ∧ h = g * h' ∧ ∀ d, d ∣ f' → d ∣ h' → IsUnit d
```

`CoprimeCofactors f h g` is not literally "`g` is a greatest common
divisor". Getting from one to the other means showing that a common
divisor `d` of `f` and `h` divides `g`, which is a statement about
`ℤ[x]` being a gcd domain.

**Unlike the multivariate case, that step is within reach
Mathlib-free.** The ingredients are all present: Gauss's lemma is
`DensePoly.content_mul` (`HexPoly/Euclid.lean:675`, with the `ZPoly`
wrapper in `HexPolyZ/Core.lean:908`), already Mathlib-free; the Euclidean
gcd over `DensePoly Rat` with `gcd_dvd_left`, `gcd_dvd_right`, and
`dvd_gcd` is in `HexPoly/Euclid/DivGcd.lean`; and the passage between
them is `content_mul_primitivePart` and `ratPolyPrimitivePart`. The
argument is that a common divisor, made primitive, divides the rational
gcd, which is associate to `g` because the cofactors stay coprime over
`ℚ[x]`, and Gauss's lemma brings the divisibility back to `ℤ[x]`.

```lean
theorem dvd_gcd_of_coprimeCofactors (hc : CoprimeCofactors f h g)
    (d : ZPoly) (hf : d ∣ f) (hh : d ∣ h) : d ∣ g
```

This SPEC schedules that theorem in milestone 3 rather than deferring it
to the companion, and records it as the point where this library is
genuinely better off than [hex-mv-gcd](hex-mv-gcd.md). If the proof turns
out to be larger than it looks, the fallback is the multivariate
resolution (state it in the companion from
`UniqueFactorizationMonoid`), and the cost of that fallback is that
Mathlib-free consumers get cofactors without maximality.

## The gcd API

```lean
def gcdCert (f h : ZPoly) : GcdCert
def gcd (f h : ZPoly) : ZPoly := (gcdCert f h).gcd
def cofactors (f h : ZPoly) : ZPoly × ZPoly
def isCoprime (f h : ZPoly) : Bool
def gcdList (fs : List ZPoly) : ZPoly
def lcm (f h : ZPoly) : ZPoly

/-- The gcd of two rational polynomials, monic, computed by clearing
denominators and calling `gcd`. -/
def ratGcd (f h : DensePoly Rat) : DensePoly Rat
```

Contracts on the degenerate inputs: `gcd 0 0 = 0`, `gcd f 0 = normalize f`,
`gcd f h = 1` when either side is a nonzero constant, `gcdList [] = 0`,
and `lcm f 0 = 0`. Each has a matching certificate case: a unit or zero
input is accepted through a `GcdCert` whose Bézout pair is over the
constants.

`normalize f` makes the content positive and the leading coefficient
positive. Over `ℤ` the two conditions are the same condition, since the
content is positive by definition and the sign lives in the primitive
part, so `normalizePrimitiveSign` in hex-poly-z is the existing function
and should be reused rather than duplicated.

`ratGcd` returns the monic associate, which is the convention every
consumer of a gcd over a field expects, and it is what
`primitiveSquareFreeDecomposition` would call.

## The algorithms

Every route produces a candidate `GcdCert` and `gcdCert` accepts it only
through `checkGcd`. A rejected candidate falls through to the next route.
Only the last route's success has to be proved.

**One statement to keep straight.** Trial division shows a candidate is
*a* common divisor. It does not show it is the greatest: `1` divides both
inputs. Every stopping rule below is "stop when `checkGcd` accepts",
never "stop when the candidate divides both inputs". In the modular
routes the coprimality half is nearly free, because the image gcd the
route already computed is what produces the Bézout pair.

### 0. Structural reductions, always applied

Zero and constant inputs return immediately. Then, in order: split off the
power of `x` dividing both and put it into the answer; split off the
integer content of each input and put `Int.gcd` of the two into the
answer; and compare degrees, since the gcd's degree is at most the
smaller of them. Each is linear in the coefficient count.

### 1. Coprime detection

Reduce both primitive parts modulo one small prime that divides neither
leading coefficient and compute the gcd in `FpPoly p`. A result of `1`
is conclusive and produces the certificate directly: the image Bézout
pair is what `xgcd` in `FpPoly p` already returns. A result other than
`1` proves nothing, because the prime may be unlucky, and the route falls
through.

The asymmetry is the point. The cheap test is conclusive in the case that
occurs most often, and `cancel` is dominated by it. The requirement this
places on the implementation is that `gcd f h` must not run a
reconstruction when the inputs are coprime, and the benchmark family
"coprime pairs" checks it.

### 2. The heuristic gcd

Evaluate both inputs at a single large integer `ξ`, take `Int.gcd` of the
two values, and reconstruct a polynomial from the symmetric `ξ`-adic
digits. In one variable the Kronecker substitution the multivariate
version needs is just this evaluation, so the route is a few lines.

Two things are worth stating because the multivariate version of this
SPEC got them wrong first. Reconstruction being exact does not follow
from the input coefficient sizes: the integer gcd can carry accidental
common factors contributed by the evaluated cofactors, so `ξ` chosen from
the coefficient norms is a heuristic for the success rate and proves
nothing. And the retry budget must be projected bit size rather than a
fixed count, since each retry raises `ξ` and the evaluated integers grow
with it. Char, Geddes, and Gonnet introduced the algorithm (GCDHEU);
Parisse, ["A correct proof of the heuristic GCD
algorithm"](https://arxiv.org/abs/cs/0206032), is the correction worth
reading before implementing.

### 3. Brown's modular algorithm

This is the route the library exists for, and in one variable it is a
single loop.

Let `γ = Int.gcd (lc f) (lc h)`, an integer that the true gcd's leading
coefficient divides. For each prime `p` in turn:

- Reject `p` if it divides `γ`, or if it divides either leading
  coefficient. These are the **bad** primes, and rejecting them is what
  makes the image degrees meaningful.
- Compute `gₚ = gcd(fₚ, hₚ)` in `FpPoly p`, monic.
- **Scale by `γ`.** The image gcd is monic and the true gcd is not, so
  the image is multiplied by `γ mod p` before it is folded in.
  Reconstructing unscaled images gives a polynomial that is not the gcd
  and whose trial division fails, which is a slow way to discover the
  bug.
- **Compare degrees.** A prime whose image gcd has larger degree than the
  running minimum is **unlucky**: discard it and continue. A prime whose
  image gcd has smaller degree makes every earlier image unlucky: discard
  the accumulated state and restart from this prime. Both cases occur,
  and the second is the one an implementation forgets.
- Fold the coefficient vector into a `CrtVec` from
  [hex-modular](hex-modular.md).
- Take the primitive part of the symmetric reconstruction, multiply back
  the content gcd from route 0, and offer the result to `checkGcd`.
  Accept on success.

Brown, "On Euclid's algorithm and the computation of polynomial greatest
common divisors" (JACM 18, 1971), is the reference.

**On the coefficient bound.** No bound is needed for soundness, and none
is needed for the dispatch to be total, because `checkGcd` decides and
route 4 is the fallback. A bound is what proves this route eventually
succeeds, and there is one: the gcd divides `f`, so the Landau-Mignotte
bound applies to it, scaled by `γ / lc(gcd)`. hex-poly-z already computes
it as `mignotteCoeffBound`, with the analytic half discharged in
hex-poly-z-mathlib, so the termination argument is a hypothesis this tree
already carries rather than a new one. The bound is used only to size the
fuel, and the loop offers the candidate to `checkGcd` at every step, so
in practice it stops enormously earlier.

### 4. The subresultant fallback

Run hex-resultant's `subresultantChain` over `Int` unchanged, take the
primitive part of the terminal nonzero entry, and multiply by the content
gcd. This is deterministic, needs no prime, and is what makes `gcdCert` a
total function with a proved postcondition:

```lean
theorem gcdCert_checks (f h : ZPoly) : checkGcd f h (gcdCert f h) = true
```

The proof obligation is concentrated: `checkGcd_sound` (short, and given
above) plus completeness of route 4, which is the standard subresultant
argument.

**This route is a scheduling dependency, not a mathematical one.**
hex-resultant is at `done_through: 1`, and its correctness theorems
additionally require `Lean.Grind.CommRing` on the coefficient type, which
`Int` has, and `ExactDivLaws Int`, which `HexResultant/ExactDiv.lean`
supplies as `instExactDivLawsInt`. So the executable chain runs today and
its theorems apply, and what is missing is the phases of hex-resultant
rather than anything about this library. Milestone 2 below is written so
that a working `gcd` exists before that dependency matters, by using the
`DensePoly Rat` Euclidean route as the initial fallback and swapping in
the subresultant chain when it is ready.

## Complexity

`f` and `h` of degree at most `n` with coefficients of at most `b` bits,
a gcd of degree `k`, moduli of `w = 31` bits, and a Landau-Mignotte bound
of `B` bits (with `B = O(n + b)`).

These are **probe counts** where a probe is an image gcd, an
evaluation, or a trial division, not machine operations.

| operation | algorithm | probes |
|---|---|---|
| `divExact?` | leading-coefficient cancellation, early failure | `O((n-k)·k)` integer ops |
| `isCoprime` | one image gcd | 1 image gcd |
| heuristic | one evaluation and one `Int.gcd` at `O(n·(b + log ξ))` bits | 1 integer gcd |
| Brown | one image gcd per prime, plus one trial division per candidate | `O(B/w)` image gcds |
| subresultant | the chain over `Int` | `O(n)` pseudo-divisions, coefficients to `O(n·b)` bits |
| rational Euclid (today's route) | Euclid over `ℚ` | `O(n)` divisions, coefficients growing exponentially |

The last two rows are the comparison, and the last row is what the
library replaces. An image gcd is `O(n²)` word operations, so Brown costs
`O(n²·B/w)` word operations against the subresultant chain's `O(n²)`
integer operations on numbers of `O(n·b)` bits, which is a factor of `n`
in the bit complexity, and against the rational Euclid route's
unbounded coefficient growth.

## Kernel exposure

The kernel replay closure is `checkGcd` and what it calls: `DensePoly`
multiplication and equality over `Int`, `content`, `Int.gcd`, reduction
into `FpPoly p`, and `FpPoly` multiplication, addition, and equality,
together with the primality proof for the certificate's prime. Each is
`@[expose]`, and a downstream module carries a `decide +kernel` test that
fails if any of them stops reducing.

Nothing in routes 1 through 4 is in that closure. The prime search, the
Chinese remaindering, the interpolation-free reconstruction, and the
subresultant chain are search, they never appear in a proof term, and
they should not pay for exposure.

The primality proof is the one expensive element, and the size table in
[hex-modular](hex-modular.md) is why the producer prefers a small prime.
A certificate over a 16-bit prime replays in about a fortieth of a second
and one over a 31-bit prime in about six seconds, for a witness that is
equally valid either way.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexPolyZGcd/EmitFixtures.lean` exposed as
`lean_exe hexpolyzgcd_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexPolyZGcd/zgcd.jsonl`, and an oracle driver at
`scripts/oracle/zgcd_sympy.py`. One tuple appended to `ORACLES` in
`scripts/ci/run_oracles.sh`:

```
"HexPolyZGcd|hexpolyzgcd_emit_fixtures|scripts/oracle/zgcd_sympy.py|conformance-fixtures/HexPolyZGcd/zgcd.jsonl"
```

SymPy's `gcd` and `cofactors` over `ZZ` and `QQ` cover the whole surface
and fix the same normalisation convention (positive leading coefficient
over `ℤ`, monic over `ℚ`), so the fixture compares values directly.
python-flint's `fmpz_poly.gcd` is a performance comparator rather than
the oracle, because it does not expose cofactors.

**An end-to-end fixture cannot tell which route ran.** Every candidate
goes through `checkGcd`, and a rejection falls through to a route that
returns the right answer, so the oracle suite passes even if the leading
coefficient scaling is inverted, the unlucky-prime restart never fires,
and the heuristic route is broken. The suite therefore has two halves,
and the route-level half is worth more.

**Route-level tests**, in Lean, invoking each producer directly: that the
candidate it produced was accepted; that the intended route succeeded
before the fallback ran; that a constructed bad prime was rejected; that
a constructed unlucky prime was discarded; and that the accumulated state
was restarted when a smaller image degree appeared. Constructing an
unlucky prime is done by making the resultant of the cofactors divisible
by it, and the fixture carries that construction rather than a random
search for one.

**Oracle fixtures**, checking public answers. Cases that must be present:

- `gcd 0 0`, `gcd f 0`, `gcd f 1`, gcds of constants, and `gcd f f`.
- Coprime pairs at several degrees, checking the answer is `1` and the
  cofactors are the inputs.
- A gcd that is a pure power of `x`, so route 0 carries the answer.
- A gcd that is a constant, so the content recursion carries it.
- Inputs whose gcd has a leading coefficient that is not `±1`, which is
  what the `γ` scaling exists for.
- Inputs where a small prime divides a leading coefficient, and inputs
  with an unlucky prime among the first few tried.
- Inputs with large coefficients and a small gcd, where the
  Landau-Mignotte bound is enormously pessimistic and early acceptance is
  what makes the route fast.
- Swell cases: small inputs whose subresultant remainder sequence has
  large coefficients, and the same inputs over `ℚ` where the rational
  Euclid route is worst.
- Content cases over `ℤ`: `2x` and `4x`, `12x` and `18x`, `6` and `4`,
  where the answer is an integer times a polynomial and the normalisation
  convention is visible.
- Cyclotomic and near-cyclotomic pairs, which are the sparse inputs with
  small coefficients where the heuristic route should win.
- `ratGcd` on inputs with large denominators, checking the clearing step
  happens and the result is monic.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexPolyZGcd/Bench.lean`. Native and kernel: the kernel suite
measures `checkGcd` replay at a small prime, since that is what a
downstream certificate consumer pays.

Families:

- **Coprime pairs**, degrees 8 to 512. Decides whether route 1 works. The
  required property is that the time is a small multiple of the time to
  reduce the inputs modulo one prime. A regression means a reconstruction
  is running when it should not.
- **Dense gcds**, degrees 16 to 512 with a gcd of about half the degree,
  coefficients of 8 and 256 bits.
- **Swell cases**, small degree with a subresultant sequence whose
  coefficients explode. Route 4, and the argument for having the others.
- **Squarefree decomposition**, the existing
  `primitiveSquareFreeDecomposition` inputs, measured through the old
  rational route and the new integer gcd. This family is the reason the
  library exists and it should show the largest improvement.
- **Rational coefficients**, the same inputs over `ℚ` through `ratGcd`.

**Comparators.** FLINT's `fmpz_poly_gcd` is `gating`. FLINT dispatches
among a heuristic route, a modular route, and a subresultant fallback,
which is the same set of routes this SPEC specifies, so the comparison is
like-for-like and there is no structural reason for an exemption. The
threshold, written down in advance: within `5x` of FLINT on the dense and
coprime families at every rung above degree 32. Two required internal
checks, which matter more than the external one:

- `gcd` must be faster than the existing `DensePoly Rat` Euclidean route
  on every family except degree-2 inputs, and faster by at least `10x` on
  the swell family.
- `primitiveSquareFreeDecomposition` rewritten to call this library must
  be faster than its current form on the Berlekamp-Zassenhaus input
  ladder.

SymPy is the oracle and is not a performance comparator.

## The Mathlib layer

`hex-poly-z-gcd-mathlib` transports the results onto `Polynomial ℤ`.
Writing `e` for hex-poly-mathlib's `DensePoly Int ≃+* Polynomial ℤ`:

```lean
theorem gcd_dvd_left  : e (gcd f h) ∣ e f
theorem gcd_dvd_right : e (gcd f h) ∣ e h
theorem dvd_gcd (d) : d ∣ e f → d ∣ e h → d ∣ e (gcd f h)

theorem coprimeCofactors_greatest (hc : CoprimeCofactors f h g) (d) :
    d ∣ e f → d ∣ e h → d ∣ e g

theorem divExact?_eq_dvd : (divExact? f g).isSome = true ↔ e g ∣ e f

instance : Decidable (a ∣ b)          -- Polynomial ℤ
instance : DecidableEq (Polynomial ℤ) -- through the equivalence, for the above
```

If `dvd_gcd_of_coprimeCofactors` lands Mathlib-free as milestone 3
schedules, `dvd_gcd` here is a transport rather than a proof, and
`coprimeCofactors_greatest` is its restatement. If it does not, this is
where it is proved, from `UniqueFactorizationMonoid (Polynomial ℤ)`,
and the Mathlib-free layer keeps the weaker `CoprimeCofactors`
conclusion. Either way the companion's statements are the same, which is
why the decision can be deferred without changing any signature.

Mathlib has no `NormalizedGCDMonoid (Polynomial ℤ)` instance in the
elaborator's path, so the statements above are in terms of divisibility
rather than an equation between named gcds, and an `Associated` version
is derived where a caller has such an instance in scope. This matches
what [hex-mv-gcd](hex-mv-gcd.md) does for the multivariate case, and for
the same reason.

Following the project split, no theorem about `ZPoly` belongs in the
companion beyond these and one correspondence lemma per public operation.

## Milestones

1. **Exact division and the certificate.** `divExact?` with its
   theorems, the `Dvd` and `Decidable` instances, `GcdCert`, `checkGcd`,
   and `checkGcd_sound`. Nothing computes a gcd yet, and the hardest
   proof in the library is already done.

2. **A correct gcd.** Route 0, route 1, and a fallback, with
   `gcdCert_checks`. The fallback is the `DensePoly Rat` Euclidean route
   initially, so this milestone does not wait on hex-resultant. At the
   end of it the library is usable and slow on the hard cases.

3. **Maximality.** `dvd_gcd_of_coprimeCofactors`, through Gauss's lemma
   and the rational gcd. This is the milestone that decides whether the
   companion proves maximality or restates it.

4. **Brown.** Route 3, with the `γ` scaling and the bad and unlucky prime
   handling. The route-level tests for those traps are written before the
   code.

5. **The heuristic and the subresultant fallback.** Route 2, and route 4
   replacing the rational fallback once hex-resultant is far enough
   along.

6. **The companion**, and the rewrite of
   `primitiveSquareFreeDecomposition` in hex-poly-z to call `gcd`. The
   rewrite is the benchmark that justifies the library, so it is a
   milestone rather than a follow-up.

## File organisation

```
HexPolyZGcd/
  Divide.lean       -- divExact?, Dvd, Decidable, the prefilters
  Cert.lean         -- GcdCert, checkGcd, checkGcd_sound
  Fast.lean         -- routes 0 and 1, isCoprime
  Heu.lean          -- route 2 and its bit budget
  Brown.lean        -- route 3
  Prs.lean          -- route 4
  Gcd.lean          -- the dispatch, gcd, cofactors, gcdList, lcm, ratGcd
  Maximal.lean      -- dvd_gcd_of_coprimeCofactors
HexPolyZGcd.lean
HexPolyZGcdMathlib/
  Gcd.lean          -- divisibility, maximality, the Associated statements
  Decide.lean       -- Decidable (a ∣ b)
HexPolyZGcdMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexPolyZGcd:
    deps: [HexPolyZ, HexPolyFp, HexPoly, HexModular, HexModArith, HexArith, HexResultant]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: FLINT fmpz_poly_gcd via python-flint
          class: gating
          goal: within 5x on the dense and coprime families above degree 32
      input_families:
        - name: coprime-pairs
          description: coprime inputs at degrees 8 to 512, where route 1 must settle it
        - name: dense-gcds
          description: gcds of about half the input degree at 8 and 256 bit coefficients
        - name: swell
          description: small inputs whose subresultant sequence has large coefficients
        - name: squarefree
          description: the Berlekamp-Zassenhaus squarefree decomposition ladder
        - name: rational
          description: the same inputs over the rationals through ratGcd
  HexPolyZGcdMathlib:
    deps: [HexPolyZGcd, HexPolyZMathlib, HexPolyMathlib, HexModArithMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexResultant` is a dependency for route 4 only, and it is the one
dependency at `done_through: 1`. Milestone 2 is arranged so that nothing
before milestone 5 needs it.

## Open questions

- **Whether `primitiveSquareFreeDecomposition` should move here.** It is
  hex-poly-z's function today, its only nontrivial dependency after this
  library exists is the gcd, and Yun's algorithm over `ℤ` is a natural
  neighbour of the gcd. Against moving it: it is on the
  Berlekamp-Zassenhaus path and moving a function that far down the
  dependency graph is disruptive. This SPEC keeps it where it is and
  rewrites its body, and the question should be revisited if a second
  squarefree consumer appears.
- **Whether the certificate should carry the prime's primality proof or
  recompute it.** Carrying it makes the certificate self-contained and
  makes its size depend on the proof term. Recomputing it makes the
  checker run `isPrimeTrial`, priced in the table in
  [hex-modular](hex-modular.md). The measurement that settles this is
  the kernel bench family.
- **Whether to use a prime power rather than several primes.** Lifting a
  single image modulo `p^k` by Hensel's lemma is an alternative to
  Chinese remaindering across primes, and hex-hensel already implements
  the lifting. It replaces one image gcd per prime by one image gcd plus
  `k` lifting steps, and whether that wins depends on the degree and the
  coefficient size. Both are unverified producers, so either may be
  adopted without touching the checker.
- **Whether `isCoprime` should return the witness.** `cancel` wants to
  know only whether the gcd is `1`, and a caller that later needs the
  Bézout pair over `F_p` currently recomputes it. Returning
  `Option GcdCert` costs nothing and complicates the common call site.
- **The crossover between routes 2 and 3.** The heuristic route wins on
  sparse inputs with small coefficients and loses badly as the degree
  grows. The dispatch tries route 2 first below a degree threshold, and
  this SPEC does not guess the number.
