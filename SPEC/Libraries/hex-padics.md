# hex-padics (fixed-precision p-adic approximations, depends on hex-arith, hex-modular, hex-primality)

Finite approximations to elements of `ℤ_p` and `ℚ_p`, with the
precision carried in the data, the valuation reported as a lower bound
when that is all the data supports, and every arithmetic operation
stating exactly how much precision it loses. Mathlib-free. The
companion `hex-padics-mathlib` states the correspondence: an
approximation names a **ball** in `ℤ_[p]` or `ℚ_[p]`, and every
operation is proved to enclose the true answer.

This SPEC expands the "Fixed-precision p-adic approximations" entry of
[future-work](../future-work.md). It does not specify an exact
inverse-limit or lazy `ℤ_p` / `ℚ_p` type, and it does not specify a
precision typeclass shared with
[hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md). Both are deferred, for
reasons given under "Scope" and in the open questions.

## Why this library exists

**Three consumers each carry a private modular tower.**
[hex-hensel](../../HexHensel/SPEC/hex-hensel.md) lifts a factorization
from `p` to `p^k` and owns `ZPoly.reduceModPow`, `ZPoly.congr`, and a
`Canonical f m` range invariant. The Dixon solve in
[hex-modular-matrix](hex-modular-matrix.md) accumulates digits
`x ≡ Σ xᵢ pⁱ (mod p^k)` and divides the residual by `p` exactly at
every step.
[hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md)
consumes the first and reconstructs integer factors from the lifted
ones. All three do the same three things: reduce modulo a prime power,
divide out a known power of `p`, and reconstruct an exact answer from a
residue and a bound. None of them has a name for the object it is
manipulating.

**The precision contract is the interesting theorem, and every one of
those consumers states it informally.** "The result is correct modulo
`p^k`" is a claim about a set of values, not about a number, and the
whole difficulty is that the set shrinks under some operations, stays
put under others, and grows under exactly two. Writing the contract
down once, with the hypotheses each operation actually needs, is most
of the value here.

**Finite data cannot decide whether a p-adic number is zero, and an API
that hides that fact is wrong.** An approximation known modulo `p^N`
whose residue is `0` may be the exact zero, or `p^N`, or
`p^(10^6)`. The library therefore has an *approximate zero* as a
first-class case, `valuation?` returns `none` on it rather than a
number, and inversion and division by it fail rather than guessing.
Every design decision below follows from taking that seriously.

**There is no p-adic number type in this tree today.** A user who wants
to compute in `ℚ_p` writes integers, a modulus, and their own
bookkeeping. That bookkeeping is what this library replaces.

## What an approximation is, and what it is not

Fix a prime `p`. An approximation names a **ball**

```text
B(c, m) = { x : v(x - c) ≥ m }
```

with centre `c` and absolute precision `m`, where `v` is the p-adic
valuation. Every statement in this library is a statement about that
set. The three consequences are stated here once and relied on
everywhere below.

**An approximation is not a number.** `a = b` as approximations says
the two balls coincide. It says nothing about the values they
approximate beyond `v(x - y) ≥ m`. No theorem in this library or its
companion concludes `x = y` in `ℚ_p` from an equality of
approximations, and "Equality, and what it does not say" states the one
direction that is available.

**The valuation of an approximation is exact or it is a bound, and
which one is visible in the data.** If the centre has valuation `v < m`
then every element of the ball has valuation exactly `v`, because the
error has valuation at least `m > v`. If the centre has valuation at
least `m`, the ball is `B(0, m)`, it contains `0`, and all that is
known is `v(x) ≥ m`. There is no third case.

**Operations are enclosures, not equalities.** The specification of
`mul` is "if `x ∈ a` and `y ∈ b` then `x * y ∈ mul a b`", never
"`mul a b` is the product". The distinction is not pedantic: it is why
`QpApprox` is not a ring, which "Why `QpApprox` is not a ring" shows
with a counterexample.

## Placement in the DAG

Above hex-arith, hex-modular, and hex-primality. Below hex-hensel,
hex-berlekamp-zassenhaus, and hex-modular-matrix.

```text
hex-arith ──────┐
hex-modular ────┼── hex-padics ── hex-padics-mathlib
hex-primality ──┘
```

Each dependency is used for a named thing and none is decorative.

- **hex-arith** supplies the extended GCD behind the modular inverse
  and the exact division `exactDiv` the digit loop performs. It also
  owns `Hex.Nat.Prime`, which is the proposition the primality witness
  discharges.
- **hex-modular** supplies `symMod` for the symmetric representative
  used in display and in the reconstruction bound, and `ratRecon?` for
  the exactification described under "Exactification". Reimplementing
  the truncated Euclidean run here would duplicate the one piece of
  [hex-modular](../../HexModular/SPEC/hex-modular.md) that costs real work.
- **hex-primality** supplies `CheckedPrimeCert p`. "The checked prime"
  explains what requires it and how the requirement is enforced.

**No edge runs from this library to hex-poly or to any polynomial
library, and none may be added.** Lifting a *factorization* is
hex-hensel's subject and stays there. This library names no polynomial
type, so a reviewer checking that hex-hensel may depend on it does not
have to trace imports, only to check that `HexPadics/*.lean` imports
nothing but `HexArith`, `HexModular`, `HexPrimality`, `HexBasic`, and
`Std`.

The direction is forced by the release graph as well as by the build.
[`scripts/release/released.yml`](../../scripts/release/released.yml)
publishes repositories in topological order and rewrites each one's
Lake pins, so an edge in the other direction has no valid publication
order rather than merely being inconvenient.

The companion adds an edge to Mathlib and one to
hex-primality-mathlib. The second is not optional: Mathlib's `ℤ_[p]`
and `ℚ_[p]` require `[Fact p.Prime]`
(`Mathlib/NumberTheory/Padics/PadicIntegers.lean:57`), the Mathlib-free
witness proves `Hex.Nat.Prime p`, and hex-primality-mathlib's
`prime_iff` is what converts one to the other. A companion that tried
to state a ball theorem without it would not typecheck.

```text
hex-padics ─────────────┐
                        ├── hex-padics-mathlib
hex-primality-mathlib ──┘
```

## Scope

In scope: the primality requirement and the power cache; `ZpApprox p N`
with its canonical residue, reduction maps, ring structure, valuation,
and partial inversion and division; `QpApprox p` with its normalized
centre, valuation, absolute precision, approximate zero, and
precision-aware arithmetic; the exact precision-loss formula for every
operation; conversion between the two types and to and from `Int` and
`Rat`; exactification by rational reconstruction; and the companion's
ball correspondence.

Not in scope, and deliberately:

- **An exact `ℤ_p` or `ℚ_p`.** An inverse limit, or a lazy value
  producing digits on demand, is a different type with different costs
  and a different correctness argument. It is separate future work,
  recorded in [future-work](../future-work.md) and in the open
  questions. Nothing here is a step towards it that would be wasted,
  since a lazy type wants exactly these balls as its finite views.
- **A precision typeclass shared with hex-truncated-series.** The two
  libraries do look alike, and "Why `QpApprox` is not a ring" is the
  reason a shared class would abstract almost nothing today. The open
  questions record the measurement that would settle it.
- **Polynomials over `ℤ_p`, Hensel lifting, and Newton polygons.**
  Lifting is hex-hensel's, and the placement above is what lets
  hex-hensel adopt this library rather than the other way round.
- **Square roots, `exp`, `log`, and Teichmüller lifts.** Each needs a
  lifting argument with its own hypotheses (the `p = 2` square root
  needs a congruence modulo `8`, and `exp` converges only for
  `v(x) > 1/(p-1)`), and none has a consumer in this tree. They are
  natural additions once the arithmetic is exercised.
- **Unramified extensions `ℤ_q` and ramified extensions.** A second
  type with a second uniformizer, wanted for p-adic factoring over
  extension fields and not by anything here.
- **Dependency tracking between approximations.** The operations assume
  their inputs are independent, which is the standard assumption and
  the standard trap. "Why `QpApprox` is not a ring" states what it
  costs.

## The checked prime

The directive is that `p` carry a checked hex-primality witness. It is
carried by a `Prop` class, which is the shape hex-mod-arith already
uses for the same question, and it is required at the two places where
requiring it means something.

```lean
namespace Hex.Padic

/-- `p` is prime. Both approximation types take this instance as a
parameter, so neither type can even be written at a composite `p`. -/
class PrimeBase (p : Nat) : Prop where
  prime : Hex.Nat.Prime p

/-- The intended way to obtain the instance for a large `p`: run
hex-primality's certificate search and keep the checked result. -/
def PrimeBase.ofCert (c : CheckedPrimeCert p) : PrimeBase p

theorem PrimeBase.two_le [PrimeBase p] : 2 ≤ p

instance : PrimeBase 2
instance : PrimeBase 3
instance : PrimeBase 5
```

For a literal `p` the instance is `⟨by decide⟩`, using hex-arith's
`Decidable (Hex.Nat.Prime n)`. For a `p` too large to decide, the only
route is `PrimeBase.ofCert` applied to the output of hex-primality's
`primeCert?`, which returns `CheckedPrimeCert p` indexed by the subject
so that a certificate for one number cannot answer a request about
another. There is no `sorry`-free third route and no
`Classical.choice` escape hatch, because `Hex.Nat.Prime` is decidable
and the class has exactly one field.

`PrimeBase` mirrors `ZMod64.PrimeModulus` in hex-mod-arith. It is a
separate declaration rather than a reuse because depending on
hex-mod-arith would add an edge to this library's dependency list for
the sake of one `Prop` class, and hex-mod-arith's class is about a
word-sized modulus.

**The instance is a parameter of both types**, following
`ZMod64 (p : Nat) [ZMod64.Bounds p]` in hex-mod-arith:

```lean
structure ZpApprox (p N : Nat) [PrimeBase p] where ...
inductive QpApprox (p : Nat) [PrimeBase p] where ...
```

So the enforcement is at the type former rather than at a convention
about which entry points to use. `ZpApprox 6 3` is not a type, the raw
structure constructor is unreachable at a composite `p` along with
everything else, and no operation or theorem below needs to carry the
instance separately, since a value of either type brings it along.
Every code block below therefore elaborates under a `variable
[PrimeBase p]`, and the instance brackets are not repeated on each
declaration.

**A `Prop` class can be a type parameter and a bundled certificate
cannot, which is the reason for the split.** Indexing on a
prime-with-certificate record is the design a reader reaches for first,
and it does not work: `CheckedPrimeCert p` contains a `PrimeCert` as
data, two certificates for the same prime are different data, and so
two indexed types would be distinct for one prime. A caller holding
values built from two independently produced certificates could not add
them. `PrimeBase` has no such problem, since it is a `Prop` and proof
irrelevance makes any two instances of it interchangeable. The
certificate is what *produces* the instance and is not what the type
is indexed by.

**The positivity that the operations need comes from the same place.**
`0 < p ^ N`, which every canonical residue and every `Zero` or `One`
needs, follows from `PrimeBase.two_le`. Without the type parameter the
operations with an argument could recover it from that argument's range
invariant, while `Zero`, `One`, and `Pow` (through its `k = 0` base
case) could not, since at `p = 0` and `N > 0` the type would be empty
and they would have nothing to return.

**What breaks at a composite `p`, concretely.** Both failures are in
the arithmetic and not only in the proofs. At `p = 6`:

- `v(2) = 0` and `v(3) = 0` while `v(6) = 1`, so the valuation is not
  additive and the product precision formula under "The two
  conservation laws" is wrong.
- `2` has valuation `0` and is not invertible modulo `6^k` for any `k`,
  so "valuation zero implies invertible", which `inv?` tests, is false.

There is no repair short of primality, which is why the witness is
required rather than recommended.

## The power cache

```lean
/-- `p ^ (2 ^ i)` for `i < sq.size`. These are the powers the doubling
Newton inversion and the binary-splitting valuation both index, and
`powAt` assembles any other power from them. -/
structure PowTable (p : Nat) where
  sq : Array Nat
  sq_eq : ∀ i, (h : i < sq.size) → sq[i] = p ^ (2 ^ i)

/-- Assembles `p ^ k` from the cached squares indexed by the binary
expansion of `k`, and computes the factors the table does not reach.
There is no coverage invariant on `sq`, so a short or empty table gives
correct answers and no speedup. -/
def PowTable.powAt (t : PowTable p) (k : Nat) : Nat
theorem PowTable.powAt_eq (t : PowTable p) (k : Nat) : t.powAt k = p ^ k
```

Every operation below has a plain form and an `At` form taking a
`PowTable p`, with a theorem `fooAt_eq : fooAt t a b = foo a b`. The
plain form is what the ring lemmas are stated about, and the `At` form
is what a loop calls. The proof field is what makes a stale or wrong
table impossible rather than merely unlikely.

Recomputing `p ^ N` per operation is the mistake this record exists to
prevent: at `p = 5` and `N = 4096` it is a `9500`-bit power computed by
square-and-multiply on every single addition. Squares rather than a
dense table is the right shape because the two algorithms that need
many powers both descend by halving, and a dense table of `p^0` through
`p^N` costs `O(N²)` digits to hold.

**No Barrett or Montgomery parameters are cached.** hex-arith's
reduction helpers target word-sized moduli, and `p ^ N` is a bignum for
every `N` a consumer cares about, so reduction is `Nat.mod` on GMP
integers. The open questions record the corner where that claim is
weakest.

## `ZpApprox`: the capped-absolute type

```lean
namespace Hex

/-- An element of `ℤ_p` known modulo `p ^ N`: the ball of radius
`p^(-N)` around `residue`. Canonical by construction. -/
structure ZpApprox (p N : Nat) [PrimeBase p] where
  residue : Nat
  lt : residue < p ^ N

namespace ZpApprox

variable {p N M K : Nat} [PrimeBase p] {a b : ZpApprox p N} {x y z : Int}

/-- The integers this approximation does not exclude. -/
instance : Membership Int (ZpApprox p N) where
  mem a x := ((p : Int) ^ N) ∣ (x - a.residue)

/-- The canonical approximation of an integer. -/
def ofInt (x : Int) : ZpApprox p N

instance : DecidableEq (ZpApprox p N)

theorem mem_ofInt (x : Int) : x ∈ (ofInt x : ZpApprox p N)
theorem mem_iff (a : ZpApprox p N) (x : Int) : x ∈ a ↔ a = ofInt x
theorem ext (h : a.residue = b.residue) : a = b
```

**The range invariant is a field rather than a separate predicate.**
`lt` is a `Prop`, so it is erased at runtime and costs nothing, and it
buys two things a predicate does not. Structural equality is equality of
balls with no canonicality side condition, which is what `mem_iff` says.
And no caller can build a non-canonical value, so no operation has to
defend against one.

The alternative, hex-hensel's `ZPoly.Canonical f m` as a separate
predicate, is right there because a polynomial's coefficients are
canonicalised in bulk by a reduction pass. A single residue is
canonicalised by the operation that produced it.

**Reduction maps, and the direction that is missing.**

```lean
/-- Discard the digits at index `M` and above. A surjective ring
homomorphism. -/
def reduce (a : ZpApprox p N) (h : M ≤ N) : ZpApprox p M

theorem mem_reduce (h : M ≤ N) (hx : x ∈ a) : x ∈ a.reduce h
theorem reduce_reduce (h : M ≤ N) (h' : K ≤ M) :
    (a.reduce h).reduce h' = a.reduce (Nat.le_trans h' h)
theorem reduce_mul (h : M ≤ N) : (a * b).reduce h = a.reduce h * b.reduce h
theorem reduce_add (h : M ≤ N) : (a + b).reduce h = a.reduce h + b.reduce h
```

**There is no map raising the precision, and this is the sharpest
contrast with [hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md).** That
library has `extend`, which pads with zeros, is documented as valid
only for inputs known to be polynomials, and carries no
multiplicativity lemma. The analogue here would send the ball
`B(c, N)` to `B(c, M)` with `M > N`, which is a strictly smaller ball:
it asserts that digits `N` through `M-1` are zero when the data says
nothing about them. That is not a lemma that fails to hold, it is a
claim the input does not license, so the operation does not exist under
any name and no "valid for inputs known to be integers below `p^N`"
caveat rescues it. A caller who wants more digits recomputes from the
exact input, which is the only source of them.

**The ring structure.**

Each operation is a named definition, and the notation instance
delegates to it, following `ZMod64.mul` and its `Mul` instance in
hex-mod-arith. The names are what the `At` forms of "The power cache"
and the correspondence theorems of the companion refer to.

```lean
def zero : ZpApprox p N
def one  : ZpApprox p N
def add  (a b : ZpApprox p N) : ZpApprox p N
def neg  (a : ZpApprox p N) : ZpApprox p N
def sub  (a b : ZpApprox p N) : ZpApprox p N
def mul  (a b : ZpApprox p N) : ZpApprox p N
/-- Square-and-multiply, per design principle 7. -/
def pow  (a : ZpApprox p N) (k : Nat) : ZpApprox p N

instance : Zero (ZpApprox p N) := ⟨zero⟩
instance : One  (ZpApprox p N) := ⟨one⟩
instance : Add  (ZpApprox p N) := ⟨add⟩
instance : Neg  (ZpApprox p N) := ⟨neg⟩
instance : Sub  (ZpApprox p N) := ⟨sub⟩
instance : Mul  (ZpApprox p N) := ⟨mul⟩
instance : Pow  (ZpApprox p N) Nat := ⟨pow⟩

theorem mem_add (hx : x ∈ a) (hy : y ∈ b) : x + y ∈ a + b
theorem mem_mul (hx : x ∈ a) (hy : y ∈ b) : x * y ∈ a * b
theorem mem_pow (hx : x ∈ a) (k : Nat) : x ^ k ∈ a ^ k

/-- At a fixed `N` the operations are exactly `ZMod (p ^ N)`
arithmetic, so the approximations form a commutative ring. -/
instance : Lean.Grind.CommRing (ZpApprox p N)
```

**`ZpApprox p N` is a ring, and that is a fact about the approximations
and not about `ℤ_p`.** Multiplication preserves absolute precision `N`
because every element of `ℤ_p` has non-negative valuation: writing
`x' = x + δ` and `y' = y + ε` with `v δ, v ε ≥ N`, the error
`xε + yδ + δε` has valuation at least `N`. That argument uses
`v x ≥ 0` and so does not survive the move to `ℚ_p`, which is why
`QpApprox` is built differently and is not a ring.

**The precision that multiplication throws away.** The true product of
`B(x, N)` and `B(y, N)` is a ball of absolute precision
`N + min N (min (v x) (v y))`, which is sharper than `N` exactly when
**both** inputs have positive valuation, and is `2N` when both are
approximate zeros. The cap at `N` in that formula is not decoration: an
approximate zero has no finite valuation to put there, and the error
term `δε` bounds the gain at `N` regardless. The capped-absolute model
discards all of it, and does so on purpose: the type index is the contract, and the consumers
that motivate this type (Hensel lifting to a fixed `p^k`, the Dixon
digit loop) work at a precision fixed in advance. A caller who wants
the sharper precision uses `QpApprox`, which is exactly the difference
between the two types.

## Valuation and approximate zero

```lean
/-- The valuation, when the data determines it: `some k` says every
represented integer has valuation exactly `k`, and `none` says the
residue is `0`, so all that is known is `v ≥ N`. -/
def valuation? (a : ZpApprox p N) : Option Nat

theorem valuation?_lt (h : valuation? a = some k) : k < N
theorem valuation?_eq_some (h : valuation? a = some k) (hx : x ∈ a) :
    (p : Int) ^ k ∣ x ∧ ¬ ((p : Int) ^ (k + 1) ∣ x)
theorem valuation?_eq_none (h : valuation? a = none) (hx : x ∈ a) :
    (p : Int) ^ N ∣ x
theorem valuation?_eq_none_iff : valuation? a = none ↔ a.residue = 0

/-- The base-`p` digits, low to high. -/
def digits (a : ZpApprox p N) : Vector Nat N
/-- The representative in `(-p^N/2, p^N/2]`, from hex-modular's
`symMod`. For display and for the reconstruction bound, never the
representation. -/
def symRepr (a : ZpApprox p N) : Int
```

`valuation?` returning `none` is the **approximate zero**, and the two
theorems above are the whole content of the honesty requirement: on
`some k` the valuation is pinned exactly, on `none` only a lower bound
is available, and the lower bound is `N` rather than anything larger.

**`valuation? = none` does not mean the value is zero.** It means the
data cannot tell zero from `p^N`, from `p^(N+1)`, or from any of
infinitely many other values. No theorem concludes `x = 0` from it, and
none can. The mirror-image mistake, reading `some k` as "the value is
`p^k` times a unit *of the approximation*", is also wrong at the top:
`some (N-1)` pins the valuation and leaves the unit part known to one
digit.

**Precision loss and precision discarded.**

```lean
/-- Multiply by `p ^ k`. The `k` extra digits the answer really has are
discarded, because the output precision is fixed by the type. -/
def mulPow (a : ZpApprox p N) (k : Nat) : ZpApprox p N

/-- Divide by `p ^ k`, or `none` when the residue is not divisible by
`p ^ k`. The precision drops by `k`, recorded in the type. -/
def divPow? (a : ZpApprox p N) (k : Nat) : Option (ZpApprox p (N - k))

theorem mem_divPow? (h : divPow? a k = some c) (hx : x ∈ a)
    (hdvd : (p : Int) ^ k ∣ x) : x / (p : Int) ^ k ∈ c
theorem divPow?_isSome_iff : (divPow? a k).isSome = true ↔ (p ^ k) ∣ a.residue
```

`divPow?` is the operation the Dixon digit loop performs at `k = 1` on
every iteration, and its type is where the precision loss is recorded.
A caller who wants `N` digits out of a division by `p^k` computes at
precision `N + k`, and the type is what tells them. This is the same
device [hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md) uses for
`divXPow?`, and for the same reason: a docstring saying "the caller
should remember to ask for more" is not a contract.

At `k > N` the output type is `ZpApprox p 0`, the trivial one-element
type, and `divPow?` succeeds exactly when the residue is `0`. That is
correct rather than a corner to avoid: dividing an approximate zero at
precision `N` by `p^(N+3)` yields something about which nothing is
known, and `ZpApprox p 0` is precisely the type that says nothing.

## Inversion and division in `ℤ_p`

```lean
/-- The inverse, when the data proves every represented value is a unit
of `ℤ_p`. Precision is preserved exactly. -/
def inv? (a : ZpApprox p N) : Option (ZpApprox p N)

theorem inv?_isSome_iff : (inv? a).isSome = true ↔ valuation? a = some 0
theorem inv?_mul (h : inv? a = some c) : a * c = 1
theorem mem_inv? (h : inv? a = some c) (hx : x ∈ a)
    (hy : ((p : Int) ^ N) ∣ (x * y - 1)) : y ∈ c

/-- `a / b` when `b` has valuation exactly `w` and the quotient is
integral. The precision drops by `w`, stated by the caller and
checked. -/
def divAt? (a b : ZpApprox p N) (w : Nat) :
    Option (ZpApprox p (N - w))

/-- The same with the loss discovered rather than supplied. -/
def div? (a b : ZpApprox p N) :
    Option ((w : Nat) × ZpApprox p (N - w))

theorem divAt?_isSome_iff :
    (divAt? a b w).isSome = true ↔
      valuation? b = some w ∧ (p ^ w) ∣ a.residue
theorem mem_divAt? (h : divAt? a b w = some c) (hx : x ∈ a) (hy : y ∈ b)
    (hz : x = y * z) : z ∈ c
```

**`inv?` succeeds exactly at valuation zero, and stating the condition
inside the approximation ring would be wrong.** The tempting
formulation is "`inv? a` succeeds when `a` is a unit of
`ZpApprox p N`". For `N ≥ 1` that is the same condition, since a
residue is a unit modulo `p^N` exactly when `p` does not divide it. At
`N = 0` it is not: `ZpApprox p 0` is the one-element ring in which
`0 = 1`, so *every* element is a unit of it, while the ball it names is
all of `ℤ_p`, which contains `0` and has no inverse.

This is where this library and
[hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md) point in opposite
directions, and the difference is worth stating because the two SPECs
otherwise look alike. There, `TSeries R n` **is** the ring
`R[[x]] / (x^n)`, so a success condition stated inside the type is a
statement about the object the caller holds, and that SPEC requires it
to be stated that way. Here `ZpApprox p N` is **not** `ℤ_p`, it is a
family of subsets of it, so a success condition stated inside the type
is a statement about the wrong object. The rule this library follows:
**a success condition is a statement about the represented set, never
about the approximation ring.** `inv?_isSome_iff` is stated with
`valuation?` for exactly that reason, and `valuation?` is `none` at
`N = 0` because the residue is `0` there, so the guard is automatic
rather than a special case.

**The two failure modes of `divAt?` are different and both are
`none`.** `valuation? b ≠ some w` means the caller's precision-loss
claim is wrong, or `b` is an approximate zero. `p ^ w ∤ a.residue`
means the quotient is not in `ℤ_p` at all, and the caller wants
`QpApprox`. The two are distinguishable by the caller from `valuation?`
and `divPow?`, so `divAt?` does not return a reason. That is a
considered choice and not an oversight: an `Except` with two
constructors would put a failure vocabulary on the hottest operation in
the Dixon loop, where the caller already knows `w = 1` and already
knows the division is exact.

**Division by an approximate zero is `none`, at every precision and in
both types.** If `b`'s residue is `0` its ball contains `0`, so the set
of quotients is unbounded and no ball encloses it. There is no total
form and no fallback value: design principle 8 requires any total form
to be classified `unreachable-by-pipeline-invariant` or
`audited-emergency-value`, and neither applies, since the failure is
reachable from ordinary inputs and no value is mathematically safer
than reporting it. The remedy principle 8 names, propagating the
`Option` upward until the public API takes responsibility, is what the
signatures above do.

`inv?` is Newton lifting on the residue, `c ↦ c * (2 - a * c)` started
from the inverse modulo `p`, doubling the known precision each step,
with the intermediate products reduced modulo `p^(2^j)` rather than
modulo `p^N`. The bounded step is what makes the total cost `O(M(b))`
rather than `O(M(b) log b)`, by the same geometric-sum argument
[hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md) makes for `invOfUnit`,
and the same mistake is available: running every step at full precision
is correct and asymptotically worse. The extended GCD route is the
alternative, is `O(M(b) log b)`, and is kept as the comparison in the
bench family below.

## `QpApprox`: the capped-relative type

`ℚ_p` has values of negative valuation, and the valuation is runtime
data rather than a type index, so the precision cannot live in the type
without the valuation living there too. The type therefore carries its
own precision, and it carries the valuation explicitly because that is
the quantity multiplication and division are additive in.

```lean
/-- An approximation to an element of `ℚ_p`.

`zero m` is the ball `{ x : v x ≥ m }`. It is what an approximation
degenerates to when cancellation exhausts the precision, and it is the
only shape that can represent a value indistinguishable from zero.

`mk v u r` is the ball `p^v * (u + p^r ℤ_p)` with `u` a unit residue
modulo `p^r`. Every element of it has valuation exactly `v`. -/
inductive QpApprox (p : Nat) [PrimeBase p] where
  | zero (prec : Int)
  | mk (val : Int) (unit : Nat) (rel : Nat)
       (pos : 0 < rel) (lt : unit < p ^ rel) (ndvd : ¬ p ∣ unit)

namespace QpApprox

variable {p : Nat} [PrimeBase p] {a b c : QpApprox p} {x : Rat}

/-- The absolute precision: the exponent below which nothing is known. -/
def prec : QpApprox p → Int
  | zero m         => m
  | mk v _ r _ _ _ => v + r

/-- The valuation, when the data determines it. -/
def valuation? : QpApprox p → Option Int
  | zero _         => none
  | mk v _ _ _ _ _ => some v

/-- The relative precision: the number of significant digits. `none` on
an approximate zero, which has no significant digit. -/
def rel? : QpApprox p → Option Nat
  | zero _         => none
  | mk _ _ r _ _ _ => some r

/-- The centre, as a rational: `p ^ val * unit`, and `0` for an
approximate zero, whose ball is centred at zero. -/
def centre : QpApprox p → Rat

/-- The best lower bound on the valuation the data supports: the
valuation when it is known, and the absolute precision otherwise. -/
def valLower : QpApprox p → Int

instance : DecidableEq (QpApprox p)
```

**The invariant is in the constructor, for the same reason it is in
`ZpApprox`.** `pos`, `lt`, and `ndvd` are `Prop`s, so they are erased,
and their presence makes the canonical form unique: for a given ball
there is exactly one `QpApprox` naming it. Structural equality is then
equality of balls with no side condition, and `DecidableEq` is derived.
Without `ndvd` the same ball would have several names, since
`mk 1 1 (r-1)` and a hypothetical `mk 0 p r` would both want to name
`p + p^r ℤ_p`, and the equality theorem under "Equality" would need a
canonicality hypothesis on both sides.

**Absolute precision is derived, not stored, and this is a small
deviation from [future-work](../future-work.md).** That entry says
`QpApprox p` carries "a normalized centre, valuation, and absolute
precision". The shape above carries the normalized centre (as `val` and
`unit`), the valuation, and the *relative* precision, with the absolute
precision `val + rel` computed by `prec`. The information is the same.
The reason for storing the relative one is that `0 < rel` is the
invariant that makes `unit` meaningful, and that relative precision is
what multiplication and division preserve, so the stored field is the
one the arithmetic reads. The approximate zero stores absolute
precision because it has no relative precision to store.

**Normalization is one function and every operation ends in it.**

```lean
/-- The canonical approximation of the ball with centre `p ^ e * c` and
absolute precision `m`. Strips powers of `p` from `c`, and returns
`zero m` when the centre's valuation reaches `m`. -/
def norm (c : Int) (e m : Int) : QpApprox p

theorem prec_norm : (norm c e m).prec = m
theorem norm_of_zero : norm 0 e m = zero m
theorem norm_eq_norm (h : (p : Int) ^ (m - e).toNat ∣ (c - c')) :
    norm c e m = norm c' e m
```

The last theorem is the one that makes `norm` a function of the ball
rather than of the representative: a centre is only ever known modulo
`p^(m-e)` in the first place, and two representatives that agree there
normalize to the same value.

The stripping loop is bounded by `m - e` steps, because a centre whose
valuation reaches `m - e` after scaling is an approximate zero and the
loop stops. So `norm` is structurally recursive on that bound, needs no
fuel argument, and has no exhaustion branch to classify under design
principle 8. This is the same device
[hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md) uses for its Newton
driver, and for the same reason.

**The semantics is stated over `Rat`, and the companion upgrades it.**

```lean
/-- The p-adic valuation of a positive natural number. `p` is explicit
because these three are p-generic helpers rather than operations on an
approximation, and the instance is what makes the stripping loop
terminate. -/
def natVal (p : Nat) [PrimeBase p] (n : Nat) : Nat

/-- The p-adic valuation of a nonzero rational; `none` at zero. -/
def ratVal (p : Nat) [PrimeBase p] (x : Rat) : Option Int

/-- `x` is within absolute precision `m` of zero: every determined
valuation of `x` is at least `m`, and `x = 0` satisfies it. -/
def NearZero (p : Nat) [PrimeBase p] (m : Int) (x : Rat) : Prop :=
  ∀ k, ratVal p x = some k → m ≤ k

/-- The rationals this approximation does not exclude. -/
instance : Membership Rat (QpApprox p) where
  mem a x := NearZero p a.prec (x - a.centre)
```

`NearZero` is written as a universally quantified implication rather
than as a comparison in `Option Int` so that the exact zero, whose
`ratVal` is `none`, satisfies it at every `m`. Writing it as
`m ≤ ratVal p x` under some order on `Option Int` would need that order
to put `none` at the top, which is `WithTop ℤ` reinvented, and the
Mathlib-free layer does not have `WithTop`. The companion states the
same thing with Mathlib's `WithTop ℤ`, where it reads more directly.

**The arithmetic, declared.** As on `ZpApprox`, each operation is a
named definition and the notation instance delegates to it. There is no
`Zero` and no `One`, for the reason under "Why `QpApprox` is not a
ring".

```lean
def add  (a b : QpApprox p) : QpApprox p
def neg  (a : QpApprox p) : QpApprox p
def sub  (a b : QpApprox p) : QpApprox p
def mul  (a b : QpApprox p) : QpApprox p
/-- `none` exactly on an approximate zero. -/
def inv? (a : QpApprox p) : Option (QpApprox p)
/-- `none` exactly when the divisor is an approximate zero. -/
def div? (a b : QpApprox p) : Option (QpApprox p)

instance : Add (QpApprox p) := ⟨add⟩
instance : Neg (QpApprox p) := ⟨neg⟩
instance : Sub (QpApprox p) := ⟨sub⟩
instance : Mul (QpApprox p) := ⟨mul⟩

theorem mem_add (hx : x ∈ a) (hy : y ∈ b) : x + y ∈ a + b
theorem mem_mul (hx : x ∈ a) (hy : y ∈ b) : x * y ∈ a * b
theorem mem_inv? (h : inv? a = some c) (hx : x ∈ a) (hx0 : x ≠ 0) : x⁻¹ ∈ c
theorem inv?_isSome_iff : (inv? a).isSome = true ↔ a.valuation?.isSome = true
theorem div?_isSome_iff : (div? a b).isSome = true ↔ b.valuation?.isSome = true
```

Each of `add`, `sub`, and `mul` computes a raw centre and a raw
absolute precision and ends in `norm`, so the precision formulas of
"The two conservation laws" are read off that call rather than proved
per operation.

**Precision changes, and again only one direction.**

```lean
/-- Lower the absolute precision. -/
def coarsen (a : QpApprox p) (m : Int) : QpApprox p

theorem prec_coarsen : (a.coarsen m).prec = min m a.prec
theorem mem_coarsen (hx : x ∈ a) : x ∈ a.coarsen m
```

`mem_coarsen` is an inclusion of balls in the widening direction, which
is sound. There is no refining map, for the reason `ZpApprox` has no
`extend`.

**Conversions.**

```lean
def ofZp (a : ZpApprox p N) : QpApprox p
def toZp? (a : QpApprox p) : Option (ZpApprox p N)

/-- An exact rational has unbounded precision, so the caller chooses
one. There is no default. -/
def ofRat (x : Rat) (prec : Int) : QpApprox p

theorem toZp?_isSome_iff :
    (toZp? (N := N) a).isSome = true ↔ 0 ≤ a.valLower ∧ (N : Int) ≤ a.prec
```

`ofRat` taking a precision is not an inconvenience to be optimised
away. No ball contains exactly one point, so an exact value has no
sharpest representable approximation, and any default the library
picked would be a silent policy decision at the one place the caller
knows better. The same reasoning appears again under "Powers" for
`pow a 0`.

`toZp?` fails on negative valuation, which is the whole point of having
two types: `1/p` is a perfectly good `QpApprox` and is not in `ℤ_p`.
Using `valLower` rather than `valuation?` is what makes it also fail on
`zero (-3)`, whose ball contains `p^(-3)`.

## The two conservation laws

The precision arithmetic is two rules and everything else follows.

> **Addition and subtraction conserve absolute precision. Multiplication
> and division conserve relative precision.**

Writing `v` for the valuation, `r` for the relative precision, and
`m = v + r` for the absolute precision:

| operation | valuation | relative precision | absolute precision |
|---|---|---|---|
| `a + b`, `a - b` | at least `min (v a) (v b)`, computed by `norm` | derived | `min (prec a) (prec b)` |
| `a * b` | `v a + v b` | `min (r a) (r b)` | `v a + v b + min (r a) (r b)` |
| `inv? a` | `-(v a)` | `r a` | `r a - v a` |
| `div? a b` | `v a - v b` | `min (r a) (r b)` | `v a - v b + min (r a) (r b)` |
| `a ^ k`, `k ≥ 1` | `k * v a` | `r a + v_p k`, with one `p = 2` exception | derived |
| `coarsen m` | unchanged, or lost | derived | `min m (prec a)` |

Each row is derived rather than asserted, and each derivation is short
enough to record.

**Multiplication.** With `x = p^v(u + δ)` and `y = p^w(t + ε)`,
`v δ ≥ r`, `v ε ≥ s`, the product is `p^(v+w)(ut + uε + tδ + δε)`, and
the error has valuation at least `min r s` because `u` and `t` are
units. The centre `ut` is a unit because `p` is prime, which is the
second place primality is load-bearing. So the relative precision is
`min r s` and the valuation is `v + w` exactly.

**Inversion.** From `1/x - p^(-v) u^(-1) = (p^v u - x) / (x · p^v u)`,
the numerator has valuation at least `v + r` and the denominator has
valuation exactly `2v`, so the difference has valuation at least
`r - v`. The valuation of `1/x` is `-v`, so the relative precision is
`(r - v) - (-v) = r`, preserved exactly. Computing it needs `u^(-1)`
modulo `p^r`, which exists because `p ∤ u` and `p` is prime, the third
place primality is load-bearing.

**Addition, and where it loses.** The absolute precision of the sum is
`min (prec a) (prec b)` and there is nothing subtle about that. What is
subtle is the valuation: `v(x + y) ≥ min (v x) (v y)`, with equality
whenever `v x ≠ v y`, and with no upper bound at all when
`v x = v y`. So the *relative* precision of a sum is
`min (prec a) (prec b) - v(sum)`, which can be anything from `r` down
to zero or below. When it reaches zero or below, `norm` returns
`zero (min (prec a) (prec b))` and the significant digits are gone.
This is **precision exhaustion by cancellation**, it is the
characteristic failure of every fixed-precision arithmetic, and it is
not an error: the returned approximate zero is a correct enclosure of
the answer. It is simply an enclosure that has lost the information the
caller wanted.

The example to keep in mind, at `p = 5`:

```text
a = 1 + O(5^10)                       val 0, rel 10
b = -1 + 5^8 + O(5^10)                val 0, rel 10
a + b = 5^8 + O(5^10)                 val 8, rel 2
```

Eight of the ten significant digits are gone in one addition, and the
answer is still correct. Repeating it twice more gives `zero 10`. A
caller who needs `k` significant digits out of a computation with a
cancellation of depth `d` starts at relative precision `k + d`, and
nothing in the library can discover `d` for them.

**Why the sum's valuation is computed rather than bounded.** An
implementation that recorded `min (v a) (v b)` as the valuation of the
sum would be *wrong*, not merely imprecise: `mk` requires a unit
centre, and after a cancellation the centre is not a unit, so the
invariant would fail. Computing the true valuation of the centre sum,
which is what `norm` does, is forced by the representation, and that is
a point in favour of putting the invariant in the constructor.

## Powers, and the one rule that is not the obvious one

```lean
def pow (a : QpApprox p) (k : Nat) : QpApprox p

/-- The relative precision of a positive power: `r + v_p k`, except at
`p = 2` with a single significant digit and an even exponent, where it
is one more. -/
def powRel (p : Nat) [PrimeBase p] (r k : Nat) : Nat :=
  if p = 2 ∧ r = 1 ∧ 2 ∣ k then natVal 2 k + 2 else r + natVal p k

/-- Lifting the exponent: a power gains `v_p k` significant digits, and
one more in the exceptional case. -/
theorem rel?_pow (h : a.rel? = some r) (hk : 1 ≤ k) :
    (pow a k).rel? = some (powRel p r k)
```

The `1 ≤ k` hypothesis is not decoration. `pow a 0` is the exact `1`
approximated at a precision the caller did not choose, so it is
governed by the convention below rather than by `powRel`, and
`powRel 2 1 0` would report two digits where the convention gives one.

Square-and-multiply through `mul` would give relative precision `r`,
which is sound and is not sharp. The gap is real: at `p = 2`, squaring
an approximation with one significant digit gives three.

The rule is **lifting the exponent**, applied to the ratio of two lifts
of the unit part rather than to a difference of integers. For lifts `u`
and `u'` of that unit part, `v(u' - u) ≥ r` and `p ∤ u`, so the ratio
`u'/u` lies in `1 + p^r ℤ_p`, on which raising to the `k`th power is
multiplication by `k` in the logarithm coordinate. Hence

```text
v(u'^k - u^k) = v(u' - u) + v_p(k)     (u' ≠ u, and p odd or r ≥ 2)
```

so `u^k` is determined modulo `p^(r + v_p k)` by `u` modulo `p^r`, and
no further, since the equality is attained by a lift with
`v(u' - u) = r` exactly. The implementation computes `u^k` modulo that
higher modulus by square-and-multiply on any lift, and records the
higher relative precision.

**The `p = 2` exception is real and is not an artefact of the proof.**
At `p = 2` and `r = 1` the ball is the whole unit group `1 + 2ℤ_2`, and
lifting the exponent carries its usual correction term `v_2(u' + u)`,
which is at least `2` there rather than `1`. Concretely `1² = 1` and
`3² = 9` differ by `8`, every odd square is `1` modulo `8`, and so
squaring a unit known to one digit gives a square known to three. An
implementation that applies the uniform rule at `p = 2` and `r = 1`
reports two, which is sound and not sharp. One that applies the
exception at `r ≥ 2` reports one digit too many, which is **wrong**.

**A binomial bound is not enough to get this right, which is why the
statement above is the group one.** Reading
`(u + p^r t)^k - u^k = Σ_{j ≥ 1} C(k, j) u^(k-j) p^(j r) t^j` term by
term gives `v_p(k) + r` from the linear term and `2r` from the rest,
hence the bound `min (r + v_p k) (2r)`. That bound is sound and it is
not sharp: at `p = 3`, `r = 1`, `k = 9` it reports two digits, while
`1⁹`, `4⁹`, and `7⁹` are all `1` modulo `27`, so three are determined.
The tail terms are not independent of the linear one, and only the
group statement sees that.

**`pow a 0` is the one operation with no sharp answer.** The image of
any ball under `x ↦ x^0` is the single point `1`, and no smallest ball
contains a single point. The convention is `pow a 0 = mk 0 1 (r a)` on
a nonzero `a`, and `mk 0 1 1` on an approximate zero, which carries no
relative precision to reuse. Both are documented as deliberately not
sharp, for the same reason `ofRat` takes a precision from the caller.

## Why `QpApprox` is not a ring

There is no `CommRing (QpApprox p)` instance and there must not be one,
for two independent reasons.

**There is no `Zero` and no `One` to build it from.** The exact values
`0` and `1` have unbounded precision, and no ball contains exactly one
point, so `zero m` and `mk 0 1 r` are approximations of them at a
precision someone had to choose. `Zero (QpApprox p)` would have to pick
an `m` out of the air. This is the same obstruction as `ofRat` taking a
precision and `pow a 0` having no sharp answer, and it is why those two
are stated the way they are.

**Distributivity fails**, which is the substantive reason and does not
depend on the first. `Add`, `Sub`, and `Mul` instances do exist, and
under them addition is associative and commutative, multiplication is
associative and commutative, and the distributive law is false.

At `p = 5`, take

```text
a = 1 + O(5)                          val 0, rel 1
b = 1 + O(5^10)                       val 0, rel 10
c = -1 + 5^5 + O(5^10)                val 0, rel 10
```

Then `b + c = 5^5 + O(5^10)`, with valuation `5` and relative precision
`5`, so

```text
a * (b + c) = 5^5 + O(5^6)            val 5, rel 1
a * b       = 1 + O(5)                val 0, rel 1
a * c       = -1 + O(5)               val 0, rel 1
a * b + a * c = O(5)                  zero 1
```

The two sides are different approximations. Both are correct
enclosures, and the left one is sharper, because the cancellation
happened before the precision was reduced instead of after.

The law that does hold is the inclusion, stated with the membership
predicate:

```lean
theorem mem_mul_add (hx : x ∈ a * (b + c)) : x ∈ a * b + a * c
```

and it holds in that direction only. Stating the ring axioms as
inclusions rather than equalities is the honest algebra of this type,
and it is the same algebra
[hex-interval](../../HexInterval/SPEC/hex-interval.md) has for the same
reason.

**The independence assumption comes with it.** `sub a a` is
`zero (prec a)` and not an exact zero, because the operation treats its
two arguments as independent balls. The enclosure is correct, since the
true difference `x - x = 0` does lie in `B(0, prec a)`. It is not
sharp, and no arrangement of the arithmetic makes it sharp, because the
type carries no record that the two arguments came from the same value.
A caller who needs `x - x = 0` exactly does not have a p-adic
approximation problem, it has an exact-arithmetic problem, and should
work in `Rat`, or in `ZpApprox` where the answer is an honest zero of
the approximation ring.

**This is the reason the shared precision typeclass is deferred.**
`TSeries R n` is a commutative ring. `ZpApprox p N` is a commutative
ring. `QpApprox p` is not, its precision lives at runtime rather than
in a type index, and its degenerate cases are the opposite of
`TSeries`'s. A class covering all three would have to be stated for the
one that is not a ring, at which point it abstracts the ring structure
away and carries little more than "there is a precision". The open
questions record what would change the answer.

## Equality, and what it does not say

```lean
instance : DecidableEq (ZpApprox p N)
instance : DecidableEq (QpApprox p)

/-- Distinct approximations at the same precision have disjoint balls,
so they prove their contents distinct. -/
theorem ne_of_ne {a b : ZpApprox p N} (h : a ≠ b) (hx : x ∈ a) (hy : y ∈ b) :
    ¬ ((p : Int) ^ N ∣ (x - y))

/-- `true` when the two balls are disjoint, which proves the values
distinct. `false` is an absence of information and never a proof of
equality. -/
def separated (a b : QpApprox p) : Bool

theorem ne_of_separated (h : separated a b = true) (hx : x ∈ a) (hy : y ∈ b) :
    x ≠ y
```

**Equality of approximations is equality of balls and nothing more.**
`a = b` at precision `N` says `v(x - y) ≥ N` for the represented
values, which is compatible with `x = y` and compatible with `x ≠ y`.
There is no theorem in this library or its companion whose conclusion
is `x = y` in `ℤ_p` or `ℚ_p`, and adding one would be adding a
falsehood.

**Distinctness *is* available, and the ultrametric is why.** Two balls
of the same radius are equal or disjoint, with no partial overlap. So
`a ≠ b` at a common precision is a proof that the represented values
differ, which is what `ne_of_ne` says and what `separated` returns.

**The return type of `separated` is `Bool` and not `Option Bool`, and
that is the point rather than an economy.** A three-valued result would
have to name a case meaning "proved equal", which this library can
never produce, so the type would advertise an outcome that does not
exist. `false` means "not separated at this precision", which is an
absence of information. A caller that reads `separated a b = false` as
evidence of equality has made the error this library exists to prevent,
and the `Bool` is named for the property it does establish.

`separated` reduces both arguments to their common absolute precision
first, which is the only comparison that means anything. Comparing a
value known to `10` digits against one known to `3` at the finer
precision would report a difference that is an artefact of the coarser
input.

## Exactification

The end of every lifting computation is the recovery of an exact
answer, and the recovery is a checked candidate rather than a
consequence of the lifting.

```lean
/-- Reconstruct a rational lying in this ball with numerator and
denominator within the given bounds, when one exists. -/
def toRat? (a : QpApprox p) (P Q : Int) : Option Rat

/-- The symmetric-bound case at relative precision `r`, taking
`P = Q = ⌊√((p^r - 1)/2)⌋`, which satisfies `2PQ < p^r` by
construction. -/
def toRatSym? (a : QpApprox p) : Option Rat

theorem mem_toRat? (h : toRat? a P Q = some q) : q ∈ a
theorem toRat?_bounds (h : toRat? a P Q = some q) :
    |q.num| ≤ P ∧ (q.den : Int) ≤ Q
theorem toRat?_unique (h : toRat? a P Q = some q) (hr : a.rel? = some r)
    (hbound : 2 * P * Q < (p : Int) ^ r)
    (hq' : q' ∈ a) (hnum : |q'.num| ≤ P) (hden : (q'.den : Int) ≤ Q) :
    q' = q
theorem toRat?_complete (hr : a.rel? = some r)
    (hbound : 2 * P * Q < (p : Int) ^ r)
    (hq' : q' ∈ a) (hnum : |q'.num| ≤ P) (hden : (q'.den : Int) ≤ Q) :
    toRat? a P Q = some q'
```

The implementation scales by `p^(-val)` to land in `ℤ_p`, reads the
residue, calls [hex-modular](../../HexModular/SPEC/hex-modular.md)'s `ratRecon?` at modulus
`p^r`, and **checks that the result lies in the ball** before returning
it. `mem_toRat?` follows from the check alone and needs no bound
hypothesis, exactly as [hex-modular-matrix](hex-modular-matrix.md)'s
`solve?_spec` follows from its final integer check.

**The bounds are scaled along with the value, and forgetting to scale
them is the easy mistake.** A rational `x` of valuation `v ≥ 0` in
lowest terms has `p^v` dividing its numerator exactly, so
`x / p^v` has numerator `x.num / p^v` and the same denominator. Running
`ratRecon?` at the caller's `P` on the scaled value and multiplying the
answer back by `p^v` therefore returns a rational whose numerator is up
to `p^v` times too large. At `p = 5` with a ball of valuation `1` and
unit part `1`, and `P = Q = 1`, the scaled reconstruction returns `1`
and the rescaled answer is `5`, which lies in the ball and violates the
stated numerator bound. So `toRat?` calls `ratRecon?` at
`P' = ⌊P / p^v⌋` and `Q' = Q` for `v ≥ 0`, and at `P' = P` and
`Q' = ⌊Q / p^(-v)⌋` for `v < 0`. Both divisions are exact tests on
integers, so `toRat?_bounds` holds with no side condition, and
`2 P Q < p^r` implies `2 P' Q' < p^r`, so the completeness hypothesis
is unchanged.

`toRat?_unique` says the answer is the only one of that size in the
ball, and `toRat?_complete` says an answer of that size is found. The
two are separate statements and the first does not imply the second.
`toRat?_complete` rests on hex-modular's `ratRecon?_complete`, which
that SPEC schedules a milestone later than `ratRecon?` itself, so this
theorem may lag the rest of the library by the same distance.

**`toRat?` returning `some q` does not prove that the value being
approximated is `q`.** It proves `q` lies in the ball, and, under the
bound hypothesis, that `q` is the only rational of that size in the
ball. Whether the approximated value was a rational of that size at all
is the caller's obligation, and it is discharged in the consumers by a
Hadamard-type bound or a Mignotte bound on the answer they are
computing. That obligation cannot be discharged here, since this
library does not know where the value came from, and a SPEC that let
`toRat?` claim otherwise would be inviting exactly the false
"approximation equals exact value" reading that "What an approximation
is, and what it is not" rules out.

## Degenerate-input audit

Every operation at an approximate zero, at negative valuation, at
exhausted precision, and at the trivial precisions. This table is the
checklist a reviewer runs against the implementation, and the
conformance fixtures below are it turned into data.

| operation | approximate zero | negative valuation | exhausted precision | `N = 0`, or no relative precision |
|---|---|---|---|---|
| `ZpApprox.ofInt` | residue `0`, total | unrepresentable, not an input | not reachable | the unique element |
| `ZpApprox.reduce M` | stays an approximate zero | not representable | not reachable | total, `M = 0` |
| `ZpApprox` `+`, `-`, `*`, `^` | total | not representable | may produce one | total, one element |
| `ZpApprox.valuation?` | `none` | not representable | `none` | `none` always |
| `ZpApprox.mulPow k` | stays an approximate zero | not representable | may produce one | total |
| `ZpApprox.divPow? k` | `some`, at precision `N - k` | not representable | may produce one | `some` iff the residue is `0` |
| `ZpApprox.inv?` | `none` | not representable | `none` | **`none`**, though every element is a unit of the type |
| `ZpApprox.divAt? w` | `none` when the divisor is one | not representable | `none` | `none` |
| `ZpApprox.symRepr` | `0` | not representable | `0` | `0` |
| `QpApprox.norm` | returns `zero m` | total | returns `zero m` | returns `zero m` |
| `QpApprox.valuation?` | `none` | `some v` with `v < 0` | `none` | `none` |
| `QpApprox` `+`, `-` | total, absolute precision is the minimum | total | may produce `zero` | total |
| `QpApprox.mul` | `zero (prec a + val b)` | total | preserved | total |
| `QpApprox.inv?` | **`none`** | `some`, valuation negated | `none` | `none` |
| `QpApprox.div?` | `none` when the divisor is one | total | `none` when the divisor is one | `none` |
| `QpApprox.pow k` | `zero (k * prec)` for `k ≥ 1` | total | preserved | see "Powers" for `k = 0` |
| `QpApprox.coarsen m` | stays `zero (min m prec)` | total | total | total |
| `QpApprox.toZp?` | `none` unless `prec ≥ N` | **`none`** | `none` | at `N = 0`, `some` iff `0 ≤ valLower` |
| `QpApprox.toRat?` | `some 0` when `0` is in range | total | `some 0` when in range | see below at `r = 1` |
| `separated` | `false` against anything overlapping | total | `false` | `false` |

Six rows deserve prose, because an implementation gets them wrong in
the same way each time.

**`ZpApprox.inv?` at `N = 0` is `none`, and an implementation that asks
the ring returns `some`.** `ZpApprox p 0` has one element with `0 = 1`,
so `a * a = 1` holds and a unit search inside the type succeeds. The
ball is all of `ℤ_p` and contains `0`. The test is on `valuation?`,
which is `none` at `N = 0` because the residue is `0`.

**`QpApprox.inv?` on `zero m` is `none` at every `m`, including a very
large `m`.** A high absolute precision does not make an approximate
zero invertible: the ball still contains `0` and the set of inverses is
still unbounded. An implementation that treats `zero (10^6)` as "close
enough to `p^(10^6)`" is inventing a valuation the data does not carry.

**Multiplication by an approximate zero has an exact answer, and it is
not `zero (prec a)`.** For `x` with `v x ≥ m` and `y` with valuation
exactly `w`, the product satisfies `v(xy) ≥ m + w`, so the result is
`zero (m + w)`: the absolute precision *shifts* by `w`. For `w > 0` it
is a gain, and returning `zero m` would be sound and would throw away
`w` digits for no reason. For `w < 0` it is a loss, and returning
`zero m` would be **unsound**, since `m = 3` and `w = -2` gives a true
answer only in `zero 1` and `zero 3` is a strictly smaller ball. The
product of two approximate zeros is `zero (m + m')` by the same
argument.

**Negative valuation is ordinary in `QpApprox` and impossible in
`ZpApprox`.** `ofRat (1/p) prec` has valuation `-1`, `inv?` of a
valuation-`3` approximation has valuation `-3`, and `zero (-3)` is the
perfectly good ball `p^(-3) ℤ_p`. None of these has a `ZpApprox` image,
which is what `toZp?` reports. An implementation that stores the
valuation as a `Nat` fails at all of them, and it fails silently at the
one that matters most, since `inv?` is where negative valuations first
appear in a computation that started integral.

**Precision exhaustion is not an error and must not be reported as
one.** A cancellation that produces `zero m` has produced a correct
enclosure. There is no `Except`, no failure record, and no diagnostic:
the caller detects it by reading `rel?` or `valuation?`, and the
library's obligation is to make that detectable rather than to decide
what it means. A consumer that needs a guarantee restarts at a higher
precision, which is the standard loop and is the caller's to write.

**`toRatSym?` at relative precision `1`.** The modulus is `p` and the
symmetric bound is `⌊√((p-1)/2)⌋`. That is `0` only at `p = 2`, where
`toRatSym?` finds nothing and returns `none` for every input, which is
correct and is worth a fixture because an implementation that omits the
`P, Q > 0` guard divides by zero there. At `p = 3` the bound is `1`,
and `2 · 1 · 1 < 3`, so the two unit residue classes reconstruct to `1`
and `-1` rather than to `none`. The boundary is at `p = 2` and not at
`p ≤ 3`.

## Complexity

`b = N log₂ p` is the bit size of the modulus, and `M(b)` the cost of
multiplying two `b`-bit integers, which for Lean's GMP-backed `Nat` is
subquadratic in practice.

| operation | algorithm | cost |
|---|---|---|
| `ZpApprox` `+`, `-` | add and conditionally subtract | `O(b)` |
| `ZpApprox` `*` | multiply and reduce | `M(b)` |
| `ZpApprox` `^ k` | square-and-multiply | `O(log k) · M(b)` |
| `ZpApprox.reduce M` | one reduction | `M(b)` |
| `ZpApprox.valuation?` | binary-splitting removal of `p`-powers | `O(M(b) log b)` |
| `ZpApprox.divPow? k` | exact division by `p^k` | `M(b)` |
| `ZpApprox.inv?` | Newton with bounded steps | `O(M(b))` |
| `ZpApprox.inv?` | extended GCD, the comparison | `O(M(b) log b)` |
| `ZpApprox.divAt?` | one `divPow?` and one `inv?` | `O(M(b))` |
| `QpApprox.norm` | one valuation and one reduction | `O(M(b) log b)` |
| `QpApprox.mul`, `div?` | as `ZpApprox` at the smaller precision | `O(M(b))` |
| `QpApprox` `+` | one reduction and one `norm` | `O(M(b) log b)` |
| `toRat?` | truncated extended Euclidean run | `O(M(b) log b)` |

Two rows carry the interesting claims.

**`valuation?` is not repeated division.** Dividing by `p` until the
remainder is nonzero costs `O(v · M(b))`, quadratic in the valuation,
and the valuations that arise in a Dixon loop are as large as the
precision. The removal algorithm uses the `PowTable` squares
`p, p², p⁴, …`, descends, and costs `O(M(b) log b)`.

**Newton inversion is `O(M(b))` only if the step is bounded.** Step `j`
reduces modulo `p^(2^j)`, so it costs `M(2^j log p)`, and the sum over
`j < log₂ N` is `O(M(b))` because `M` is superadditive. Running every
step at the full modulus is correct and costs `O(M(b) log b)`, which is
the extended GCD's cost, at which point the Newton route has bought
nothing. This is the one implementation mistake that turns a correct
implementation into a pointless one, and the bench check below is
stated to detect it.

## Kernel exposure

The replay closure is `ZpApprox.residue`, addition, multiplication,
`ofInt`, and equality on `ZpApprox p N`. Each is `@[expose]`, and a
downstream module carries a `decide +kernel` test over `ZpApprox 5 4`
that fails if any of them stops reducing.

That closure is deliberately small. No consumer in this tree puts a
p-adic approximation into a proof term today, and the reason to require
the residue arithmetic to reduce anyway is cheap insurance: a future
`norm_num`-style check that a residue is what it claims costs nothing
now and is expensive to retrofit, since the retrofit means revisiting
the representation.

`QpApprox` is **not** in the closure. `norm` runs a bounded stripping
loop and `valuation?` runs a binary-splitting descent, both of which
would reduce, and neither has a consumer, so exposing them would commit
the implementation to shapes chosen for the kernel rather than for
speed. Those recursions are still structural rather than well-founded,
which is a requirement from design principle 8 (no fuel means no
exhaustion branch to classify) rather than from kernel reduction.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexPadics/EmitFixtures.lean` exposed as
`lean_exe hexpadics_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexPadics/padics.jsonl`, and an oracle driver at
`scripts/oracle/padics_pari.py`. One tuple appended to `ORACLES` in
`scripts/ci/run_oracles.sh`, in the PARI-backed group:

```
"HexPadics|hexpadics_emit_fixtures|scripts/oracle/padics_pari.py|conformance-fixtures/HexPadics/padics.jsonl"
```

**The oracle is PARI's `t_PADIC` through cypari2.** PARI represents a
p-adic as `(p, p^prec, valuation, unit)`, which is the same data as
`QpApprox` above, and its arithmetic follows the same
minimum-relative-precision rules. cypari2 is already installed for the
oracle job (`.github/workflows/ci.yml:77`) and is already the primary
oracle for [hex-hensel](../../HexHensel/SPEC/hex-hensel.md), so no new
dependency is needed. python-flint exposes no `padic` type on the
pinned version, which the implementation should recheck rather than
assume; if a later version exposes FLINT's `padic` module it becomes a
useful second source.

**Two documented divergences, mapped in the harness rather than papered
over.** PARI raises an error where this library returns `none` for
division by an inexact zero, so the harness catches it and compares
against `none`. PARI prints an approximate zero as `O(p^n)` and reports
`n` as its valuation, where `valuation?` here returns `none`; the
harness compares `n` against the recorded absolute precision. Neither
divergence is a disagreement about the mathematics, and recording them
here is what stops a future reader from treating them as one.

**A second oracle runs in `always` mode.** An independent Python
implementation over `fractions.Fraction`, recomputing the ball from the
original serialized inputs, checks membership and the precision
formulas without PARI. The ball semantics is a dozen lines of Python,
it is the thing most worth checking independently, and
[hex-interval](../../HexInterval/SPEC/hex-interval.md) already sets the
precedent of an `always` Python oracle beside an `if_available` library
one.

Cases that must be present, and the first five are the directive's
explicit checks:

- **Approximate zero.** `valuation?` returning `none` at every
  precision on the ladder; `inv?` and `div?` by it returning `none`;
  the product `zero m * mk w t s = zero (m + w)` checked for the
  precision *gain*; `zero m + zero m' = zero (min m m')`.
- **The zero case at trivial precision.** `ZpApprox p 0` over `p = 2`,
  `3`, `5`: `inv?` must be `none` even though the type is the ring in
  which every element is a unit, `valuation?` must be `none`, and
  `divPow? 0` must be `some`. This is the single fixture most likely to
  catch a real bug, because the natural implementation returns `some`.
- **Negative valuation.** `ofRat (1/p)`, `ofRat (7/p^3)`, `inv?` of an
  approximation with valuation `3`, `zero (-3)`, and `toZp?` returning
  `none` on each. Also `toRat?` on a negative-valuation ball, which
  exercises the scaling by `p^(-val)` before reconstruction.
- **Precision exhaustion.** The `p = 5` cancellation above, emitted at
  relative precisions `1` through `12`, checking `rel?` after each of
  three successive cancellations and checking that the third returns
  `zero`. Also `sub a a`, recording that the answer is
  `zero (prec a)` and not an exact zero, so a later "simplification"
  that special-cases it fails the suite.
- **Division by an approximate zero.** Every divisor shape crossed with
  every dividend shape, at `N = 0`, at small `N`, and at large `N`,
  expecting `none` throughout. Including the case where the dividend is
  itself an approximate zero, where an implementation that short-cuts
  on a zero dividend returns `some 0`.
- **The distributivity failure**, emitted as the `p = 5` triple above
  with both sides recorded, so that a later change making the two agree
  fails the suite. The check is that the left side's ball is contained
  in the right side's, not that they are equal.
- **Powers at `p ∣ k`.** Squaring at `p = 2` and cubing at `p = 3`,
  checking that the relative precision *rises* by `v_p k`; the
  `p = 2`, `r = 1` exception, where it rises by one more; and
  `p = 3`, `r = 1`, `k = 9`, where the binomial bound reports two
  digits and three are determined. Also `k = 0` at `p = 2`, `r = 1`,
  which the convention answers and `powRel` does not. A
  square-and-multiply implementation through `mul` passes every
  soundness check here and fails the first three, and one using the
  binomial bound passes the first and fails the third.
- **Canonicity.** `norm` on centres already divisible by `p`, on
  centres divisible by `p` to exactly the precision bound, and on `0`,
  checking the unique normal form each time. Two constructions of the
  same ball must be structurally equal.
- **Equality and separation.** `separated` at mismatched precisions,
  checking that the comparison happens at the coarser one; and a pair
  with equal balls and distinct exact values, recorded so the fixture
  set contains a witness that equality of approximations is not
  equality of values.
- **Exactification.** Round trips of `ofRat` then `toRatSym?` over a
  spread of rationals including negative valuation; `toRatSym?` at
  relative precision `1`, expecting `none` at `p = 2` and `±1` at
  `p = 3`; a ball of valuation `1` at `p = 5` with `P = Q = 1`, where
  an implementation that reconstructs at the unscaled bound returns `5`
  and violates `toRat?_bounds`; and a reconstruction whose bound
  hypothesis fails, checking that `toRat?` still only ever returns a
  rational lying in the ball.
- **The two types agreeing.** For integral values at a common
  precision, `ofZp` then arithmetic must agree with arithmetic then
  `ofZp` wherever the absolute precisions coincide, and the fixture
  records the cases where they do not, which are exactly the products
  of two positive-valuation factors.

`core` profile sizes: `p ∈ {2, 3, 5, 7}` and `N` up to `8`. `ci` adds
`p` up to `10^9 + 7`, `N` up to `64`, and randomized centres.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexPadics/Bench.lean`. Native and kernel: the kernel suite
measures `decide +kernel` on a `ZpApprox 5 4` product, which is what a
downstream proof would pay.

Families:

- **Multiplication**, `N` from `8` to `8192` at `p = 5` and at a
  `31`-bit prime. The baseline every other family is read against.
- **Inversion**, the same ladder, bounded Newton against the extended
  GCD.
- **Valuation**, on inputs with valuation `0`, `N/2`, and `N - 1`,
  binary-splitting removal against repeated division.
- **The digit loop**, `divPow? 1` iterated `N` times, which is the
  shape [hex-modular-matrix](hex-modular-matrix.md)'s Dixon solve runs.
- **`QpApprox` arithmetic**, a mixed sequence at relative precisions
  `8` to `1024` including cancellations, measuring the `norm` overhead
  against `ZpApprox` at the same absolute precision.
- **Exactification**, `toRatSym?` on the same ladder.

**Comparators.** PARI's `t_PADIC` arithmetic through cypari2 is
`informational`, not `gating`. At the low end of the ladder the ratio
measures Lean's boxed-`Nat` overhead against PARI's inlined small
integers rather than anything about the algorithms, and at the high end
both sides are GMP, so a single classification covering the whole
ladder would be reporting two different things under one number.
Reclassification to `gating` is worth revisiting once the ladder has
run and the crossover is a measured number.

Two required internal checks, which matter more than the external one:

- **Bounded Newton inversion beats the extended GCD at the top of the
  ladder, and the ratio improves monotonically along it.** This is the
  evidence that the step is bounded. An implementation that reduces
  modulo `p^N` at every step produces a flat ratio near `1`, which is
  the signature of the mistake described under "Complexity".
- **Binary-splitting `valuation?` is within a small constant of the
  repeated-division route at valuation `0`, and asymptotically faster
  at valuation `N - 1`.** The threshold at the low end is a counted
  number once the family has run, and this SPEC does not guess it. The
  asymptotic claim at the high end is the one with content, since
  repeated division is quadratic there.

The bench target imports `HexPadics`, which imports `HexArith`,
`HexModular`, `HexPrimality`, `HexBasic`, and `Std`, none of which
import Mathlib, so the Mathlib-free requirement of
[SPEC/benchmarking.md](../benchmarking.md) is met without further
argument.

## The Mathlib layer

`hex-padics-mathlib` states the correspondence the whole library is
organised around: **an approximation is a ball, and every operation
encloses.**

```lean
variable {p N : Nat} [PrimeBase p]

/-- Mathlib's `Nat.Prime` from the Mathlib-free witness, through
hex-primality-mathlib's `prime_iff`. Callers turn it into the `Fact`
instance `ℤ_[p]` needs with `haveI := Fact.mk (prime_of_base p)`. -/
theorem prime_of_base (p : Nat) [PrimeBase p] : Nat.Prime p

variable [Fact (Nat.Prime p)]

/-- The ball an integral approximation names: the fibre of Mathlib's
reduction map. -/
def mem (a : ZpApprox p N) (x : ℤ_[p]) : Prop :=
  PadicInt.toZModPow N x = (a.residue : ZMod (p ^ N))

theorem mem_iff_norm (a : ZpApprox p N) (x : ℤ_[p]) :
    mem a x ↔ ‖x - (a.residue : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ))

/-- The approximations at precision `N` are the quotient. -/
def zmodEquiv : ZpApprox p N ≃+* ZMod (p ^ N)
```

`PadicInt.toZModPow` (`Mathlib/NumberTheory/Padics/RingHoms.lean:447`)
is a ring homomorphism `ℤ_[p] →+* ZMod (p ^ n)`, and
`PadicInt.ker_toZModPow` (same file, line 459) says its kernel is
`Ideal.span {(p : ℤ_[p]) ^ n}`. So the fibres of `toZModPow N` are
exactly the balls of absolute precision `N`, `mem_iff_norm` follows
from `PadicInt.norm_le_pow_iff_mem_span_pow`
(`Mathlib/NumberTheory/Padics/PadicIntegers.lean:470`), and the
enclosure theorems are corollaries of `toZModPow` being a homomorphism
rather than separate inductions.

```lean
theorem mem_add (hx : mem a x) (hy : mem b y) : mem (a + b) (x + y)
theorem mem_mul (hx : mem a x) (hy : mem b y) : mem (a * b) (x * y)
theorem isUnit_of_inv? (h : inv? a = some c) (hx : mem a x) : IsUnit x
theorem mem_inv? (h : inv? a = some c) (hx : mem a x) (hu : IsUnit x) :
    mem c ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
```

**The valuation correspondence has to be stated in `WithTop ℤ`, and
`Padic.valuation` is the wrong target.** Mathlib's
`Padic.valuation : ℚ_[p] → ℤ`
(`Mathlib/NumberTheory/Padics/PadicNumbers.lean:1040`) sends `0` to `0`
(`Padic.valuation_zero`, line 1050), so `Padic.valuation_mul` carries
`x ≠ 0` and `y ≠ 0` hypotheses. The statement this library needs is
about a set that may contain `0`, so the target is
`Padic.addValuationDef : ℚ_[p] → WithTop ℤ` (line 1140), which sends
`0` to `⊤` and whose `Padic.AddValuation.map_mul` (line 1151) is
unconditional.

```lean
/-- The membership predicate for `QpApprox`. -/
def memQ : QpApprox p → ℚ_[p] → Prop

theorem addValuation_eq_of_mem (h : a.valuation? = some v) (hx : memQ a x) :
    Padic.addValuationDef x = (v : WithTop ℤ)

theorem le_addValuation_of_mem (h : a.valuation? = none) (hx : memQ a x) :
    (a.prec : WithTop ℤ) ≤ Padic.addValuationDef x
```

Those two theorems are the formal content of "valuation bounds
including approximate zero". The first pins the valuation on the nose
for a nonzero approximation. The second gives only a bound, and the
bound is stated in `WithTop ℤ` precisely so that the genuinely-zero
case is included rather than excluded by a hypothesis. A companion that
stated the second with `Padic.valuation` would either exclude `x = 0`,
which is the case the approximate zero exists for, or be false at it,
since `Padic.valuation 0 = 0` while `a.prec` may be larger.

The precision-loss formulas transport the same way, each becoming a
statement about the output ball containing the true answer:

```lean
theorem memQ_mul (hx : memQ a x) (hy : memQ b y) : memQ (mul a b) (x * y)
theorem memQ_inv? (h : inv? a = some c) (hx : memQ a x) : memQ c x⁻¹
theorem memQ_mul_add (hx : memQ (mul a (add b c)) x) :
    memQ (add (mul a b) (mul a c)) x
```

Sharpness is the other half of the correspondence, and it is what
distinguishes a specification from a soundness claim. It says the
output ball is contained in every ball that would also have been sound:

```lean
/-- Stated for `mul`, `add`, `inv?`, and `div?`. -/
theorem mul_sharp (a b : QpApprox p) (e : QpApprox p)
    (he : ∀ x y, memQ a x → memQ b y → memQ e (x * y)) :
    ∀ z, memQ (mul a b) z → memQ e z
```

**`pow` has no sharpness theorem at `k = 0` and the SPEC says so.** The
image is a single point, no smallest ball contains it, so the statement
above is unsatisfiable there. For `k ≥ 1` the sharp precision is the
`r + v_p k` of "Powers", with the `p = 2`, `r = 1` exception, and the
sharpness proof is lifting the exponent on `1 + p^r ℤ_p` rather than a
term-by-term binomial bound.

**No `CommRing (QpApprox p)` instance appears in the companion
either.** The counterexample under "Why `QpApprox` is not a ring" is
about the executable operations, so no Mathlib-side transport repairs
it. What the companion supplies instead is the inclusion form of each
ring axiom, as `memQ_mul_add` above.

Following the project split, no theorem about `ZpApprox` or `QpApprox`
belongs in the companion beyond the membership statements, the
sharpness statements, and one correspondence lemma per public
operation.

## What the consumers get, and what they should not do

The placement makes adoption possible. It does not make every adoption
worthwhile, and saying which is which is part of this SPEC's job.

**[hex-modular-matrix](hex-modular-matrix.md)'s Dixon solve is the
closest fit.** Its residual update `rᵢ₊₁ = (rᵢ - A xᵢ) / p` is
`divPow? 1` on every entry, its step count `p^k > 2 P Q` is a statement
about absolute precision, and its final `ratReconVec?` is `toRat?`
applied entrywise. What it should *not* do is store its residual vector
as a `Vector (ZpApprox p N) n`: the entries share one modulus, the loop
is the hot path, and boxing each entry costs more than the shared
bookkeeping saves. The adapter to write is at the level of the
precision accounting and the exactification, and the vector stays an
integer vector.

**[hex-hensel](../../HexHensel/SPEC/hex-hensel.md) shares less than it
looks.** Its `ZPoly.congr` and `reduceModPow` are bulk operations on
coefficient arrays, and its `WordMod` path exists precisely to keep
word-sized moduli out of bignum arithmetic. A coefficient-wise
`ZpApprox` would undo that. What hex-hensel can take is the `PowTable`,
the exact-division primitive, and the valuation, and those three are
worth taking because they are where its own code repeats itself.

**[hex-berlekamp-zassenhaus](../../HexBerlekampZassenhaus/SPEC/hex-berlekamp-zassenhaus.md)
consumes hex-hensel, so it inherits whatever hex-hensel adopts** and
has no direct use of its own beyond the reconstruction at the end.

**The consumers that want the element type do not exist yet.** p-adic
root finding, Newton polygons, p-adic regulators, and interactive
computation in `ℚ_p` all want a scalar with honest precision, and none
of them is served by a private modular tower inside someone else's
algorithm. That is the case for building the type now rather than after
a consumer demands it, and it is also why this SPEC declines to promise
that the three existing consumers will be rewritten around it.

## Milestones

1. **The prime and the power cache.** `PrimeBase`, `PrimeBase.ofCert`,
   `two_le`, the small-prime instances, `PowTable`, `powAt` with
   `powAt_eq`. The composite-`p` counterexamples become `#guard`s here,
   since this is where a reader first meets the requirement.

2. **`ZpApprox` and its ring.** The type with its range invariant,
   `ofInt`, the `Membership` instance, `mem_iff`, `reduce` with its
   homomorphism laws, the ring operations, `digits`, `symRepr`, and the
   `Lean.Grind.CommRing` instance. The `decide +kernel` test lands
   here, because that is when the representation is still cheap to
   change.

3. **Valuation, inversion, and division in `ℤ_p`.** `valuation?` with
   both of its theorems, `mulPow`, `divPow?`, bounded Newton `inv?`
   with `inv?_isSome_iff`, and `divAt?`. At the end of it the `N = 0`
   audit rows are all exercised and the hardest degenerate case is
   settled.

4. **`QpApprox`.** The type, `ratVal` and the `Rat`-side membership
   predicate, `norm` with its structural bound, the arithmetic, `pow`
   with the `v_p k` gain, `inv?`, `div?`, `coarsen`, and the
   conversions. The distributivity counterexample becomes a `#guard`
   here.

5. **Exactification and comparison.** `toRat?`, `toRatSym?`,
   `separated`, `ne_of_ne`, `ne_of_separated`, and the uniqueness
   theorem under its bound hypothesis.

6. **The companion**, and the conformance and bench suites. The
   sharpness theorems come last, since they are the statements most
   likely to need the executable shapes to have settled.

## File organisation

```
HexPadics/
  Prime.lean       -- PrimeBase, ofCert, the small-prime instances
  PowTable.lean    -- PowTable, powAt, powAt_eq
  Zp.lean          -- ZpApprox, ofInt, Membership, reduce, the ring operations
  ZpVal.lean       -- valuation?, digits, symRepr, mulPow, divPow?
  ZpInv.lean       -- bounded Newton inv?, divAt?, div?
  RatVal.lean      -- natVal, ratVal, NearZero, the Rat-side membership predicate
  Qp.lean          -- QpApprox, norm, the arithmetic, pow, inv?, div?, coarsen
  Convert.lean     -- ofZp, toZp?, ofRat, toRat?, toRatSym?
  Compare.lean     -- separated, ne_of_ne, ne_of_separated
HexPadics.lean
HexPadicsMathlib/
  Basic.lean       -- prime_of_base, mem, zmodEquiv, mem_iff_norm
  Ball.lean        -- the enclosure theorems for every operation
  Valuation.lean   -- the addValuationDef correspondence, the precision formulas
  Sharp.lean       -- the sharpness theorems
  Recon.lean       -- exactification correctness
HexPadicsMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexPadics:
    deps: [HexArith, HexModular, HexPrimality, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: PARI t_PADIC arithmetic via cypari2
          class: informational
          rationale: "At small precisions the ratio measures Lean's boxed-Nat overhead against PARI's inlined small integers rather than the algorithms, and at large precisions both sides are GMP. One classification cannot cover both ends of the ladder; revisit once the crossover is measured."
      input_families:
        - name: multiplication
          description: products at absolute precisions 8 to 8192 over p = 5 and a 31-bit prime
        - name: inversion
          description: bounded Newton against the extended GCD on the same ladder
        - name: valuation
          description: binary-splitting removal against repeated division at valuations 0, N/2, N-1
        - name: digit-loop
          description: divPow? 1 iterated N times, the shape the Dixon solve runs
        - name: qp-arithmetic
          description: mixed QpApprox sequences with cancellations at relative precisions 8 to 1024
        - name: exactification
          description: toRatSym? on the same ladder
  HexPadicsMathlib:
    deps: [HexPadics, HexPrimalityMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

The dependency list is the check that matters when the library is
scaffolded: `scripts/check_dag.py` cross-checks `libraries.yml` against
the lakefile, so an accidental `import HexPoly` or `import HexHensel`
fails there rather than at release time.

## Open questions

- **Whether a precision typeclass shared with
  [hex-truncated-series](../../HexTruncatedSeries/SPEC/hex-truncated-series.md) is worth having.**
  Not now, because `QpApprox` is not a ring and its degenerate cases
  are the opposite of `TSeries`'s, so the class would abstract little
  more than the existence of a precision. What would change the answer
  is a third member: a capped-relative truncated series, or an
  approximation type over an unramified extension. Two members with
  incompatible degenerate cases do not justify a class, and three with
  a common shape might. The decision belongs to whoever writes the
  third.
- **Whether `ZpApprox` should be capped-relative too.** The
  capped-absolute model throws away the sharper precision a product
  really has, and a single capped-relative type over `ℤ_p` would keep
  it and would subsume `QpApprox` restricted to non-negative
  valuations. It is refused here because the type index is what makes
  the reduction maps static and the absence of a widening map
  enforceable, and because the consumers work at a fixed target
  precision. The measurement that settles it is whether any consumer
  computes a long product chain where the discarded precision would
  have avoided a restart at a higher precision.
- **Whether `PowTable` should carry Montgomery parameters after all.**
  The claim above is that `p ^ N` is always a bignum and GMP's `mod` is
  the right primitive. That is false for the small-`p`, small-`N`
  corner a conformance suite spends its time in, and it may be false
  for the Dixon loop at a word-sized `p`, where hex-hensel already
  found a word path worth having. The bench family at a `31`-bit prime
  is what produces the number.
- **Where the p-adic valuation of a `Rat` should live.** `ratVal` is
  defined here because nothing else has it, and it is arguably
  hex-arith's, beside the integer valuation its factorization helpers
  already compute. Moving it is a change to hex-arith rather than to
  this library, so it is recorded here and decided there.
- **Whether the structure constructors should be private.** "The
  checked prime" records that the raw constructor bypasses the witness
  requirement, and that nothing unsound follows because the theorems
  still need the instance. A private constructor with `ofInt` as the
  only entry point would close it, at the cost of checking that Lean's
  privacy applies as expected to a structure constructor and of losing
  pattern matching in the implementation's own modules. Worth settling
  when the type is written rather than guessed at now.
- **Whether the exact lazy `ℤ_p` belongs in this tree at all.** An
  inverse-limit or digit-stream type would make `x = y` semi-decidable
  from the other side and would let a caller ask for more digits
  instead of restarting. It is a different type with a different cost
  model and no consumer, and the honest reason to defer it is that the
  approximations here are what its finite views would be, so nothing
  built now is wasted. Worth revisiting once a consumer wants a
  precision it cannot predict in advance.
- **Whether `separated` should return the separating precision.** It
  currently returns a `Bool` backed by `ne_of_separated`. A version
  returning the precision at which the two balls first separate would
  let a consumer record why two values are distinct without
  recomputing. No consumer wants it yet, and the extra field is cheap
  to add later.
