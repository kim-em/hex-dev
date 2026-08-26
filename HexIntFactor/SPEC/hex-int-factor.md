# hex-int-factor (integer factorization, depends on hex-primality)

Factorization of natural numbers into primes with certificates, the
divisor-function API built on it, and the multiplicative-order and
primitive-root results that are the reason this tree wants it.
Mathlib-free. The companion `hex-int-factor-mathlib` proves the
correspondence with `Nat.factorization` and `Nat.primeFactorsList`,
supplies factorization-derived witnesses for squarefree decomposition,
and relates the order API to `orderOf` in `(ZMod n)ˣ`.

This SPEC expands the "Integer factorization" entry in
[future-work](../../SPEC/future-work.md) and depends on
[hex-primality](../../HexPrimality/SPEC/hex-primality.md), which owns the primality
certificates each factor carries and the multiplicative order this
library's order API is stated with.

One thing the future-work entry says needs sharpening rather than
correcting. It observes that "the multiplicative order of an element
mod `p` … comes from the factorization of `p − 1`, and the pattern
recurs for group orders throughout". True, and the consumer that
actually exists in this tree is
[hex-conway](../../HexConway/SPEC/hex-conway.md) Tier 2, whose group
order is `p^n − 1` rather than `p − 1`. That is a materially harder
family of integers, and it has structure worth exploiting. See "The
`p^n − 1` problem".

## Why this library exists

**hex-conway Tier 2 is the motivating consumer, not a current
blocker.** hex-conway's committed table now has Tier 2 proofs using
small, locally checked factorizations. Its SPEC defines Tier 2 as
"irreducible, primitive, compatible with `C(p, m)` for each proper
divisor `m ∣ n`". Primitivity of a root `α` of `C(p, n)` means
`ord(α) = p^n − 1`, which is checked by `α^{(p^n − 1)/q} ≠ 1` for each
prime `q ∣ p^n − 1`. What that needs is a **certified complete prime
support** of `p^n − 1` -- every distinct prime divisor, with no
multiplicities -- and a complete factorization is the sufficient
certificate this library supplies when that table grows beyond values
comfortable to maintain by hand. Tier 2 also needs the compatibility
proofs across degree divisors, so factorization remains one ingredient
rather than the whole verification story.

**Squarefree content over `ℤ`, but not for the reason hex-mv-gcd
gives.** `12x` is not squarefree in `ℤ[x]` because `4 ∣ 12`, so the
ring-theoretic predicate over `ℤ` is partly a question about an
integer. [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) says the `ℤ` instance of
`Decidable (Squarefree p)` "waits on the integer factorization item".
It does not: Mathlib already has
`instance : DecidablePred (Squarefree : ℕ → Prop)`
(`Mathlib/Data/Nat/Squarefree.lean:234`, via `minSqFac`) and relates
integer squarefreeness to `natAbs`, so hex-mv-gcd-mathlib can decide it
today with no dependency on this library.

What this library adds is the *witness*: the square divisor, the
squarefree part, and the multiplicities, which the decision procedure
does not produce and which a caller wanting to normalise rather than
merely test does need. That is a weaker motivation than an undecidable
predicate, and stating it honestly is better than inheriting a claim
that does not survive checking.

**hex-primality's certificate search wants it.** A Pocklington
certificate for `n` needs `n − 1` factored past `√n` (or past `n^{1/3}`
with the cube-root variant). hex-primality owns a minimal untrusted
`partialFactor` for exactly that, and this library is where that
becomes a real factorization suite. The dependency runs upward --
hex-int-factor depends on hex-primality, never the reverse -- because a
factorization certificate has to prove its factors prime while a
certificate search needs no proof at all. The reverse flow -- this
library's advances improving hex-primality's search -- has three
sanctioned routes (certificate hand-off, shared stage-1 primitives
sited upstream, an optional search hook), recorded in hex-primality's
"Taking up downstream factoring advances".

**The maximal order needs it.** [future-work](../../SPEC/future-work.md)'s
"Ring of integers" entry names the squarefree part of the polynomial
discriminant as its dependency, "where such computations turn
conditional in practice". That is a consumer whose design is shaped by
what this library can and cannot deliver, and the answer it needs is
"here is the factorization, or here is exactly what was left
unfactored".

## Scope

In scope: the factorization certificate and its checker; perfect-power
detection; trial division against hex-primality's table; reuse of
hex-primality's Brent-rho and Pollard `p − 1` stage-1 primitives; ECM
stage 1 with Montgomery curves; the divisor-function API
(`divisors`, `sigma`, `totient`, `radical`, `squarefreePart`,
`isSquarefree`); the multiplicative-order and primitive-root
certificates; and the cyclotomic pre-split for numbers of the form
`b^n ± 1`.

Pollard `p − 1` stage 2 and ECM stage 2 are not in scope. Real
continuations need specified baby-step/giant-step and Brent-Suyama
layouts respectively, an arbitrary-precision modular-arithmetic cost
model, and their own benchmark families; "the standard continuation"
is not an implementable contract. Each stage 1 is independently useful
and is the largest surface specified here.

ECM stage 1 without stage 2 may not earn its maintenance cost. Milestone
6 is therefore benchmark-gated: if the specified stage-1 route does not
win on an unbalanced-semiprime family, it is removed from the initial
library rather than retained on the assumption that an unspecified
continuation will rescue it.

Not in scope: the quadratic sieve and the number field sieve. They
reach past anything this tree needs, they are large projects, and the
honest position is that a fuel-exhausted `FactorStop.incomplete` result is a better
answer for this project than a sieve implementation nobody will
maintain. If a consumer appears that needs 60-digit factorizations, the
route is an untrusted external oracle checked by this library's
`checkFactorization`, which design principle 4 explicitly permits.

Also not in scope: discrete logarithms. The future-work entry scopes
them correctly and the reasoning is worth keeping -- the consumers this
project has want factorization and exponentiation, not logarithms.
Checking that `g` is a primitive root mod `p` is checking
`g^{(p−1)/q} ≠ 1` for each prime `q ∣ p − 1`, which is this library's
order API and not a logarithm. A general discrete logarithm
(Pohlig-Hellman down to prime-order subgroups, then baby-step
giant-step or Pollard rho) belongs here once something asks for one,
scoped to a named cyclic subgroup of certified order, because `g^x = h`
witnesses a solution and settles neither uniqueness nor minimality nor,
on failure, nonexistence, and the unit group mod a composite need not
be cyclic.

## The certificate

```lean
namespace Hex.Nat

/-- One prime power in a factorization. The base is the certificate's
subject, so the two cannot disagree. -/
structure PrimePower where
  exponent : Nat
  cert     : PrimeCert

def PrimePower.prime (e : PrimePower) : Nat := e.cert.subject

/-- A complete factorization of `subject`. -/
structure Factorization where
  subject : Nat
  factors : List PrimePower

def checkFactorization (F : Factorization) : Bool

/-- Accepted factorization data tied to the subject requested by its caller. -/
structure CheckedFactorization (n : Nat) where
  raw        : Factorization
  subject_eq : raw.subject = n
  valid      : checkFactorization raw = true
```

The subtype is not decoration. An earlier draft had the divisor
functions take a bare `Factorization` and called their theorems
unconditional, which is false: a record claiming `subject := 12` while
carrying factors of `5` is a perfectly good `Factorization`, and
`totient` of it means nothing. Either every theorem carries
`checkFactorization F = true` as a hypothesis, or the validity travels
with the data. The second is better, and it is what "takes checked
data" has to mean. Indexing the checked form by `n` additionally prevents
a valid factorization of one number from answering a request about another.

`checkFactorization` verifies:

1. `0 < F.subject`.
2. `F.factors` is strictly ascending in `prime`, so the primes are
   distinct and the representation is canonical.
3. Every `exponent` is positive.
4. `checkPrime` accepts each `cert`; `prime` is definitionally that
   certificate's subject.
5. `∏ prime ^ exponent = F.subject`.

Steps 1 through 3 and step 5 are arithmetic on the literal data; step 4
is hex-primality's checker, recursively. The whole check is `O(k)`
bounded exponentiations plus `k` primality replays.

As in `checkPrime`, powers and their product are accumulated against the
known bound `F.subject`: the loop rejects as soon as the running value
exceeds the subject. An untrusted exponent therefore cannot force the
kernel to construct a gigantic `prime ^ exponent` before discovering
that the certificate is invalid.

```lean
theorem checkFactorization_prod {F} (h : checkFactorization F = true) :
    (F.factors.map (fun e => e.prime ^ e.exponent)).prod = F.subject

theorem checkFactorization_prime {F} (h : checkFactorization F = true) :
    ∀ e ∈ F.factors, Hex.Nat.Prime e.prime

theorem checkFactorization_pos {F} (h : checkFactorization F = true) :
    0 < F.subject

theorem CheckedFactorization.pos {n} (F : CheckedFactorization n) : 0 < n

/-- The prime support is exactly the listed primes. Not "nothing else
divides" -- composite divisors certainly exist -- but no other *prime*
does, which is the statement the order and primitivity certificates
need. -/
theorem checkFactorization_primeSupport {F} (h : checkFactorization F = true)
    {q : Nat} (hq : Hex.Nat.Prime q) :
    q ∣ F.subject ↔ ∃ e ∈ F.factors, e.prime = q

/-- And with the right multiplicity. -/
theorem checkFactorization_multiplicity {F} (h : checkFactorization F = true)
    {e} (he : e ∈ F.factors) {k : Nat} :
    e.prime ^ k ∣ F.subject ↔ k ≤ e.exponent
```

**This certificate pins the prime support, and it is worth being
precise about why**, because [future-work](../../SPEC/future-work.md)'s own
preamble warns that a positive certificate usually does not establish
completeness.
Here it does, and the argument is the one the entry gives: any further
prime factor `q` would divide `∏ pᵢ^{eᵢ}`, so by Euclid's lemma
(`Hex.Nat.Prime.dvd_mul`, already in hex-arith) it divides some `pᵢ`,
and since `pᵢ` is prime and `q ≠ 1` that forces `q = pᵢ`. The
completeness comes from the *conjunction* of the product identity and
the primality of every listed factor. Drop either and it fails: a
product identity alone admits `12 = 4 · 3`, and primality alone admits
a proper sub-list.

Strict ascending order is not needed for that argument; it is needed
for canonicity and for `checkFactorization_multiplicity`, which is why
the checker requires it anyway. `0 < subject` is implied once the
product and primality checks pass, and is checked first only because it
is the cheapest way to reject `0`.

So the search is an untrusted oracle and may be partial or
time-bounded, while the checker is total. That is the cleanest instance
of design principle 4's certificate model anywhere in this tree, and it
is why every algorithm below needs no correctness proof.

**Degenerate inputs.** `factor? 1` has a checked empty
factorization, whose product is `1`. At `0`, `factor?` reports
`FactorStop.zero`: `0` has no factorization into
primes and every `n` divides it, so `checkFactorization` requires
`0 < subject`. This is
stated because the alternative -- a junk value at `0` -- makes
the factorization's prime-support completeness theorem false and would be found only by a
consumer.

## The algorithms

The generic routes produce a partial aggregate, which `factor?` accepts through
`checkPartial`; residual one becomes a complete certificate by
`checkFactorization_of_checkPartial`, without another checker replay. The
cyclotomic route separately replays `checkFactorization` on its merged complete
aggregate. Rejection at either boundary is a route bug, never ordinary fuel
exhaustion, and is exposed as `FactorStop.rejected`. Route-local attempts that
report no factor may still continue to the next search route.

```lean
inductive FactorStop where
  | zero
  | incomplete
  | rejected

structure PartialSnapshot where
  raw   : PartialFactorization
  valid : checkPartial raw = true

structure FactorFailure where
  stop     : FactorStop
  attempts : Nat
  rand     : Rand
  snapshot : Option PartialSnapshot := none
  culprit  : Option PartialFactorization := none
  metered   : Bool := true

def defaultFuel (n : Nat) : Nat

def factor? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedFactorization n × Rand)
```

There is no total `factor : Nat → Factorization`. An earlier draft had
one, justified by "a default fuel that is a function of the bit
length", and that is not a justification: a finite fuel cannot make a
partial search total, and design principle 8 does not admit "the
default is generous" as a classification. The default fuel is a
`fuel := defaultFuel n` argument, not a second entry point.

`r : Rand` is threaded because Pollard rho draws its polynomial
constant and starting point, and because
[hex-finite-field](../../SPEC/Libraries/hex-finite-field.md)'s randomness discipline
requires the draw to be an explicit argument and the advanced state to
come back. `Hex.Rand` does not exist in the tree yet; it is a
prerequisite, specified there and sited in hex-basic.

### 0. Structural reductions, always applied

- **Powers of two**, by a dedicated trailing-zero count followed by one
  right shift. For positive `n`, the isolated lowest set bit is
  `n XOR (n AND (n - 1))`, so its `log₂` is exactly the multiplicity of two.
  The native `Nat` bit operations remove that factor before the table loop and
  avoid repeating the generic `% p`/`/ p` producer for `p = 2`.
- **Perfect powers.** If `n = m^k` for some `k ≥ 2`, factor `m` and
  multiply the exponents. Detection first tries every committed prime
  exponent below `primeTableBound`, then every larger exponent through
  `log₂ n`; the latter superset of the prime exponents keeps the finite table
  from becoming a completeness boundary. Each exact integer root uses bounded
  binary search with the upper bound `2^(⌊log₂ n / k⌋ + 1)`. The
  full structural pipeline is reapplied to every popped search-stack entry,
  including recursive cofactors produced by a split; its exponent is multiplied
  by the entry's accumulated multiplicity before the result is merged.
  Strongly recommended rather than mathematically required: an earlier draft
  claimed Pollard `p − 1` and ECM "fail on prime powers, because the
  group they work in has no distinct primes to separate", and that is
  false. On `n = 9` with `a = 2` and `M = 2`, `p − 1` returns
  `gcd(2² − 1, 9) = 3`. What is true is that both routes are prone to
  returning the whole modulus on a prime power, that neither recovers
  the multiplicity, and that the detection is cheap; those are the
  reasons to do it first.
- **Small primes**, by trial division against hex-primality's
  `primeTable`. This is where most inputs finish and it is the only
  route whose cost is predictable.

### 1. Pollard rho with Brent's cycle detection

This route is hex-primality's `Hex.Nat.rhoFactor?`, reused directly
rather than reimplemented here. It is the workhorse for factors up to
about `10^{12}`: iterate
`x ↦ x² + c (mod n)`, detect a cycle by Brent's method rather than
Floyd's (fewer function evaluations per step), and take
`gcd(|xᵢ − x_j|, n)` in batches of accumulated products so that one gcd
serves many steps. The shared implementation flushes at 32 differences
or a cycle boundary. A whole-modulus batch is replayed difference by
difference, so a proper factor hidden inside that batch can still be
recovered. A nontrivial batched gcd need not be prime: collisions for
different prime factors in one batch can return their composite product,
which the recursive dispatcher splits or certifies like any other divisor.

Expected cost is `O(p^{1/2})` iterations to find a factor `p`, so
`O(n^{1/4})` to split a semiprime. The batching constant matters: a gcd
per step makes the routine gcd-bound rather than multiply-bound. The
primitive required is `Nat.gcd`, not extended GCD.

`c` and the starting point are drawn from `Hex.Rand` (specified in
[hex-finite-field](../../SPEC/Libraries/hex-finite-field.md), sited in hex-basic), following
the same explicit-argument discipline: the draw is an argument, the
retry budget is fuel, and a bad draw costs time and never correctness.
The draw rejects `c = 0`, globally rejects the degenerate polynomial
`x² - 2`, and rejects any other `(c, x)` pair satisfying
`x² + c ≡ x (mod n)`, a fixed point that can be detected before the
loop. An offset rejected for one fixed start remains available with
another start.

Complete-factorization dispatch allocates at most eight rho restarts to
one unresolved cofactor. Exhausting that bounded attempt leaves Pollard
`p − 1` and ECM reachable; it does not spend a fuel-squared number of
restarts before those routes can run.

### 2. Pollard `p − 1`

Like rho, stage 1 is sited upstream: hex-primality owns it beside
`rhoFactor?`, under the same dynamically validated proper-factor
contract, and this library reuses it. What follows specifies the
algorithm both consumers get.

The integer-factor adapter re-exports that contract under its own route name,
parallel to the rho and ECM adapters:

```lean
theorem pMinusOneFactor_spec
    (h : pMinusOneFactor n base bound = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n
```

Stage 1 chooses `1 < a < n` and first checks `gcd(a,n)`: a gcd greater
than `1` is necessarily a proper factor. Otherwise it computes
`x = a^M mod n` for `M = ∏ q^{⌊log_q B⌋}` over primes
`q ≤ B` and takes `g = gcd((x + n - 1) % n, n)`, avoiding truncated
`Nat` subtraction. Three outcomes, all of which
the implementation must distinguish: `g = 1` (increase `B`, retry, or
fall through), `1 < g < n` (a factor), `g = n` (the exponent killed
every component; retry with a different base or a smaller `B`).

The public bound is explicit rather than aspirational. `smoothBoundCap` is
the conservative cap `primeTableBound - 1`, inside the range where the
committed table is certified to contain every prime at or below the bound, and
`smoothBound B = min B smoothBoundCap`. Both the selected primes and their
prime-power exponents use that same effective bound. In particular a request
above the cap is not the former hybrid that omitted large primes while still
raising table primes to powers derived from the larger request. The theorem
`pMinusOneStage1_bound` states exact equality with the capped call.

The success condition is about the **order of `a` modulo `p`**, not
about `p − 1`: stage 1 finds `p` when `ord_p(a) ∣ M`. That is implied
by `p − 1` being `B`-smooth and is strictly weaker than it, so an
earlier draft's "succeeds iff `p − 1` is `B`-smooth" was wrong in both
directions -- it can succeed on a non-smooth `p − 1` when the base has
small order, and it can fail on a smooth one by returning `n`.

A future stage 2 may allow one prime factor of `ord_p(a)` between `B₁`
and `B₂`, but a difference table is an idea rather than an algorithm.
Before it enters scope it needs an exact baby-step/giant-step layout over
the interval primes, a batched-gcd schedule, and a benchmark family.
Montgomery and Kruppa's treatment,
https://antsmath.org/ANTSVIII/files/kruppa.pdf, is the starting reference
for that separate specification.

It is cheap, it fails on most inputs, and it succeeds instantly on the
inputs this tree actually produces. `p^n − 1` is a difference of
powers, and its prime factors `p` frequently have smooth `p − 1`; the
same is true of the moduli in the Cunningham tables generally. So it
runs before ECM and after rho, and the benchmark family "`b^n ± 1`"
below is the one that justifies its place.

At one unresolved dispatcher entry, p−1 receives at most four attempts from
the combined smooth-route budget. It starts with base `2` and bound `64`.
A no-factor result multiplies the bound by eight up to `smoothBoundCap`, then
falls through if the cap made no change. A whole-modulus result lowers the
bound by a factor of eight (not below `2`) and advances through bases
`[2, 3, 5, 7]`. A proper factor stops the ladder immediately. These are
attempts, not hidden retries inside one nominal route call.

### 3. The elliptic curve method

For factors past rho's reach. Montgomery curves in **projective `x:z`
coordinates** with Suyama's parameterisation and stage 1 scalar
multiplication against the same smoothness-bound structure as `p − 1`.
Expected total work is
subexponential in the size of the smallest factor rather than in `n`,
which is what makes it the right last route: its cost tracks the
difficulty of the *answer*, not of the input.

**The arithmetic description matters, and an earlier draft got it
backwards.** The whole point of `x:z` coordinates is that scalar
multiplication performs *no* modular inversion; the draft said "one
modular inversion per stage". What ECM stage 1 actually does is accumulate `z`
coordinates and take a gcd at the stage boundary, with three outcomes to
distinguish exactly as in `p − 1`: `gcd = 1` is no information,
`1 < gcd < n` is the factor, and `gcd = n` is failure, not success.
Suyama setup does need one inversion or gcd. And the primitive required
is `Nat.gcd`, not Bézout coefficients, so the relevant hex-arith export
is the gcd rather than `HexArith.Int.extGcd`.

ECM uses the same `smoothBound` contract, recorded by
`ecmStage1_bound`. After the p−1 ladder, every remaining attempt in the
combined budget draws a fresh Suyama parameter
`sigma = 6 + word % 256` and advances `Rand` exactly once. It starts at
bound `64`; gcd one raises the next bound eightfold, while whole modulus
changes curve at the retained bound. A no-factor result at the cap falls
through. Thus the production route is genuinely multi-curve
and deterministic replay from a fixed state includes both the parameters and
the final state.

The stage keeps `A24 = a24num / a24den` scaled throughout. If
`AA = (X + Z)²`, `BB = (X - Z)²`, and `C = AA - BB`, doubling is

```
X₂ = AA * BB * a24den
Z₂ = C * (BB * a24den + a24num * C)
```

modulo the input. The denominator multiplies both projective coordinates;
omitting it from `X₂` changes the represented point. Scalar multiplication
maintains the adjacent pair `(mP, (m+1)P)`. For an even scalar it returns
`(2mP, (2m+1)P)`, and for an odd scalar it returns
`((2m+1)P, (2m+2)P)`, using differential addition with the original `P`.
This is the invariant required by `xADD`; independently recursing to `mP`
and passing `P` as the difference between `2mP` and `mP` is valid only when
`m = 1`.

Lenstra's analysis, https://annals.math.princeton.edu/1987/126-3/p09,
is the source for the dependence on the smallest prime factor.

ECM is where the implementation effort is, and it is milestone 6 for
that reason. Everything above it is a complete and useful library. It
needs no hex-matrix, no hex-poly, and none of the algebraic
infrastructure, but it does need an explicit arithmetic dispatch:
word-sized odd moduli use hex-arith's `MontCtx`; larger moduli use direct
GMP-backed `Nat` multiplication and remainder, `(a * b) % n`. The
existing Montgomery context is `UInt64`-only and is not claimed to be an
arbitrary-precision backend. The ECM benchmark family must show that the
direct-`Nat` route is useful before this milestone is complete; a future
stage 2 or a failed benchmark is the point at which to specify a separate
big-integer modular context. On the word route, one context is constructed
after setup, the curve constants and initial point enter Montgomery
representation once, every stage multiplication stays there, and only the
final `z` coordinate is decoded for the boundary gcd. Context construction
or representation conversion inside the scalar-multiplication loop is not
the word backend specified here.

### 4. Fuel, and what failure means

`FactorStop.incomplete` means the routes did not finish inside
`fuel`, and it is
reachable -- deliberately so. Per design principle 8 that is the third
remedy, propagating the failure upward, and it is the right one here:
there is no fallback that is correct-but-slow, because trial division
past `10^{18}` is not slow, it is unavailable.

The p−1 and ECM ladders share `min fuel 8` attempts at each unresolved
cofactor, with at most four assigned to p−1 and the unused remainder assigned
to ECM. Their execution-order event list is the accounting source: its length
is added on factor success and exhaustion alike, and its final `Rand` is
threaded into every continuation. Checker rejection retains the attempt total
already accumulated by the producing search; it does not replay a curve or
replace the advanced state.

`FactorStop.rejected` is deliberately separate: it means a final aggregate
failed its certificate checker. At the generic partial-acceptance boundary it
preserves the advanced random state and attempt count. A rejected partial
aggregate also retains both the unchecked candidate in
`FactorFailure.culprit` and a checked empty-factor
recovery snapshot for the positive subject; the two are not conflated. It must
be treated as an implementation defect rather than a request for more fuel.
The internal candidate-acceptance boundary is exercised directly by negative
conformance tests. Genuine incomplete failures retain the checked aggregate in
`FactorFailure.snapshot`; the zero case has no snapshot. Cyclotomic dispatch
propagates rejection rather than retrying it as though it were exhaustion. A
rejection propagated from a cyclotomic part remains scoped to that subproblem;
a rejected merged cyclotomic aggregate records the target candidate and random
state. Its successful subsearch attempts are not exposed by `factor?`, so its
placeholder count is marked unavailable by `metered = false` rather than being
presented as an exact total.

A partial answer is more useful than no answer, so the search also
exposes

```lean
/-- What the search proved, and what it did not. `residual` is the
unfactored cofactor: composite, or not yet shown prime. -/
structure PartialFactorization where
  subject  : Nat
  factors  : List PrimePower
  residual : Nat

structure CheckedPartialFactorization (n : Nat) where
  raw        : PartialFactorization
  subject_eq : raw.subject = n
  valid      : checkPartial raw = true

def factorPartial? (n : Nat) (r : Rand) (fuel : Nat := defaultFuel n) :
    Except FactorFailure (CheckedPartialFactorization n × Rand)
```

`checkPartial` verifies `0 < subject`, `∏ pᵢ^{eᵢ} · residual = subject`,
positive exponents, strictly ascending distinct bases, and the primality
of the listed factors through their certificates -- the same conditions
as `checkFactorization` minus the requirement that the residual be `1`.
Its product calculation uses the same subject-bounded loop.
It makes **no** completeness claim. The indexed checked form prevents a
partial factorization of one subject from answering a request about
another. The characterising lemmas `checkPartial_pos`,
`CheckedPartialFactorization.pos`, `checkPartial_prod`,
`checkPartial_prime`, `checkPartial_exponent`, and `checkPartial_sorted`
expose subject positivity, reconstruction, primality, exponent positivity, and
factor-base ordering without requiring consumers to unfold the checker.
`checkFactorization_of_checkPartial` proves that residual one is already a
complete certificate, avoiding a second certificate replay. The search result
theorems are

```lean
theorem factorPartial?_error {n r fuel f}
    (h : factorPartial? n r fuel = .error f) :
    (f.stop = .zero ∧ n = 0) ∨
      (f.stop = .rejected ∧
        ∃ rejected saved, f.culprit = some rejected ∧
          checkPartial rejected = false ∧ f.snapshot = some saved ∧
            saved.raw.subject = n)

theorem factorPartial?_result {n r fuel} (hn : 0 < n) :
    (∃ F r', factorPartial? n r fuel = .ok (F, r')) ∨
      ∃ f rejected saved, factorPartial? n r fuel = .error f ∧
        f.stop = .rejected ∧ f.culprit = some rejected ∧
          checkPartial rejected = false ∧ f.snapshot = some saved ∧
            saved.raw.subject = n
```

For positive `n`, ordinary fuel exhaustion returns the checked aggregate with
its unfactored residual. It does not use an empty fallback to conceal an
aggregate that failed `checkPartial`. Such a failure is returned as
`FactorStop.rejected`, and the success-or-rejection theorem makes that internal
failure case explicit. At `n = 0` no object satisfying `0 < subject` and
`subject = n` exists, and `FactorStop.zero` reports that fact instead of
returning checked data about another number. A generic-search failure retains
its advanced state and exact attempt count. The dispatcher's attempt unit is
one Brent-rho restart, one primality-certificate witness candidate, one p−1
base/bound call, or one ECM curve, including the successful attempt in each
route. Certificate search also accumulates its internal rho restarts and
recursive child witnesses. Structural reductions, table lookup,
Miller--Rabin filtering, and checker replay are deterministic work rather than
search attempts. Counted internal success shapes preserve these totals across
continuations without changing the compatible public pair-returning APIs.
Success returns the state alongside the checked data, so a caller never
repeats a failed random stream accidentally.

The current cyclotomic wrapper cannot recover attempt counts for successfully
factored parts from the compatible pair-returning `factor?` API. If a later
part or its generic continuation stops, the wrapper therefore preserves the
failure and generator state but sets `metered := false`; it never presents the
remaining subtotal as exact. Outside the cyclotomic wrapper, the generic
dispatcher and its checker-rejection boundary remain exactly metered.

`factor?` uses the same partial-candidate acceptance boundary: it propagates
`FactorStop.zero` or `FactorStop.rejected`, converts residual one to the complete
checked form by `checkFactorization_of_checkPartial` without replaying the
certificates, and returns `FactorStop.incomplete` otherwise, retaining
the same advanced state and attempt count. Keeping both APIs avoids
forcing callers that require completeness to unpack an object they
cannot use.

That is the honest object for the consumers that need one: hex-primality's
Pocklington search wants "enough of `n − 1` to pass `√n`" and does not
care about the rest, and the "Ring of integers" entry's requirement
that "the design records what was assumed when factorization ran out of
budget, so a possibly-non-maximal order announces itself as one" is
exactly a `residual ≠ 1`.

## The `p^n − 1` problem

The motivating table-growth path asks for factorizations of `p^n − 1`,
and that family deserves its own treatment rather than being handed to
the generic dispatch.

For `b ≥ 2` and `n > 0`,

```
b^n − 1 = ∏_{d ∣ n} Φ_d(b)          b^n + 1 = ∏_{d ∣ 2n, d ∤ n} Φ_d(b)
```

where `Φ_d` is the `d`th cyclotomic polynomial. The plus case is a
different divisor set, not the same one, and an earlier draft omitted
it entirely.

Each `Φ_d(b)` is much smaller than `b^n ± 1`:
`log₂ Φ_d(b) = φ(d) · log₂ b + O_d(1)`. That is asymptotic, not an
upper bound -- `Φ_3(2) = 7` needs three bits where `φ(3) log₂ 2 = 2` --
and factoring the pieces separately is a different problem from
factoring the product. For `n = 6` the split is
`p^6 − 1 = (p − 1)(p + 1)(p² + p + 1)(p² − p + 1)`, four numbers of
roughly `2 log p` bits in place of one of `6 log p` bits.

```lean
inductive Sign where | minus | plus

/-- One candidate cyclotomic part: its index `d` and proposed value
`Φ_d(b)`. Exact cyclotomic semantics are conformance-tested, not trusted by
the factorization route. -/
structure CyclotomicPart where
  index : Nat
  value : Nat

/-- Candidate split of `b^n - 1` or `b^n + 1`. Invalid domains or a
candidate whose product is not the input return `none`. -/
def cyclotomicSplit? (b n : Nat) (sign : Sign) : Option (List CyclotomicPart)

theorem cyclotomicSplit?_prod {b n sign parts}
    (h : cyclotomicSplit? b n sign = some parts) :
    2 ≤ b ∧ 0 < n ∧
      (parts.map (·.value)).prod =
        match sign with | .minus => b ^ n - 1 | .plus => b ^ n + 1
```

An enum rather than a `Bool`, and a named pair rather than
`Nat × Nat`, because neither of the earlier draft's choices said which
way round it was. Invalid domains use the existing failure channel: at
`b ≤ 1` or `n = 0` the identities degenerate and no caller wants an
answer.

This needs cyclotomic polynomials evaluated at an integer, which is the
subject of [hex-cyclotomic](../../SPEC/Libraries/hex-cyclotomic.md). This library does not
depend on it. Evaluating
`Φ_d(b)` does not need the polynomial: the recursion

```
Φ_d(b) = (b^d − 1) / ∏_{e ∣ d, e < d} Φ_e(b)
```

computes a candidate in `Nat` with one division per index. The route does
not take exactness of those truncating divisions into its trusted proof
surface: `cyclotomicSplit?` checks the final product, and the eventual
factorization still passes `checkFactorization` against the original
input. The Möbius
form `∏_{μ(d/e)=1}(b^e−1) / ∏_{μ(d/e)=−1}(b^e−1)` is also correct, but
only as a single final quotient: dividing term by term in an arbitrary
order is not justified in `Nat`. The recursive producer is specified
because it is the natural fast candidate algorithm; a separate
Mathlib-free formalization of cyclotomic-polynomial identities is not a
prerequisite for this checked search optimization.

The two computations of `Φ_d(b)`, this one in `Nat` and
[hex-cyclotomic](../../SPEC/Libraries/hex-cyclotomic.md)'s evaluation of the constructed
polynomial, are independent and must agree. The comparison lives in that
library's conformance suite, which is the one that can import both.

**The parts need not be pairwise coprime**, so factoring them
separately can produce the same prime twice with different exponents.
A merge pass -- collect, group by prime, sum exponents, sort -- runs
before the candidate `Factorization` is offered to `checkFactorization`,
which requires strictly ascending distinct bases and would otherwise
reject a correct answer.

Two things this does not do, and they bound the claim.

It does not make the problem easy. The Cunningham project exists
because `b^n ± 1` is hard even after the cyclotomic split, and there
are entries of moderate size that have resisted for decades. What the
split does is move the boundary of what is reachable a long way out,
and turn a single hard number into several where usually only one is
hard.

And it does not exhaust the structure. Aurifeuillian factorizations
split `Φ_d(b)` further for particular `b` and `d` -- `Φ_4(2 m²) `
factoring as a product of two quadratics is the smallest case -- and
those are a known finite family of identities rather than an algorithm.
They are worth adding once the benchmark family shows a case they
would have caught, and they are recorded here rather than specified.

**What this means for hex-conway.** The committed table covers
`p ∈ {2, 3, 5, 7, 11, 13}` with `n ≤ 6`, so the largest `p^n − 1` in
scope is `13^6 − 1 = 4826808 = 2³ · 3² · 7 · 61 · 157` -- which
trial division against a `10^4` table finishes instantly. So a
refactoring of the current Tier 2 proofs onto these shared certificates
would need nothing beyond milestone 1 of this library, and the
difficulty is entirely in how far the table is
allowed to grow. That is the right way round: the primitivity checker
should land early and cheaply, and the table's growth policy should be
set by what the factorizations cost, alongside the proof-checking
budget hex-conway's SPEC already names.

## The order API

```lean
/-- A witness that `base` has multiplicative order exactly `order`
modulo `modulus`. -/
structure OrderCert where
  base     : Nat
  modulus  : Nat
  order    : Nat
  orderFac : Factorization

def checkOrder (c : OrderCert) : Bool

/-- Order data accepted by the checker. Search APIs return this form. -/
structure CheckedOrderCert where
  raw   : OrderCert
  valid : checkOrder raw = true
```

`checkOrder` verifies `1 < c.modulus`, `0 < c.order`,
`c.orderFac.subject = c.order`, `checkFactorization c.orderFac = true`,
`HexArith.powModNat base order modulus = 1 % modulus`, then
`HexArith.powModNat base (order/q) modulus ≠ 1 % modulus` for each prime
`q` in the factorization. `OrderCert` stays raw and serializable; only
`CheckedOrderCert` embeds the proof that this full replay succeeded.
The identity is normalised as `1 % modulus` rather than `1` so that the
same modular expression is used throughout, although `1 < c.modulus`
excludes the degenerate modulus.

The characterisation `checkOrder_iff` and named projections
`checkOrder_one_lt_modulus`, `checkOrder_order_pos`,
`checkOrder_orderFac_subject`, `checkOrder_orderFac`, `checkOrder_pow`, and
`checkOrder_pow_div_prime` expose these accepted facts so
downstream proofs do not unfold the Boolean checker or index a nested
conjunction.

```lean
theorem order_eq_of_checkOrder {c} (h : checkOrder c = true) :
    Hex.Nat.orderOf c.base c.modulus = c.order

/-- Coprimality is a consequence, not a hypothesis: `a^m ≡ 1 (mod n)`
with `0 < m` exhibits `a` as a unit. -/
theorem coprime_of_checkOrder {c} (h : checkOrder c = true) :
    Nat.Coprime c.base c.modulus
```

using `Hex.Nat.orderOf` from [hex-primality](../../HexPrimality/SPEC/hex-primality.md)'s
`HexPrimality/Order.lean`, which that SPEC specifies as the least
positive `k` with `a^k % n = 1 % n` for `1 < n` and coprime `a`, and
`0` elsewhere. The junk value is why `0 < c.order` is checked.

The prime-divisor criterion does pin the order exactly: if the true
order `r` divided `order` properly, some prime `q ∣ order / r` would
give `r ∣ order / q`, hence `base^{order/q} ≡ 1`, which the checker
rejected.

**The completeness of `orderFac` is doing the work.** `base^m ≡ 1`
proves only that the order divides `m`; a proper divisor of `m` could
be the true order. Ruling that out means ruling out `order/q` for every
prime `q ∣ order`, and that quantifier ranges over a set the
factorization certificate is what pins down. This is the "second
witness" pattern [future-work](../../SPEC/future-work.md)'s preamble describes,
and here the second witness is the completeness of a factorization
rather than a separate object.

```lean
def isPrimitiveRoot {p : Nat} (pc : CheckedPrimeCert p)
    (F : CheckedFactorization (p - 1)) (g : Nat) : Bool

theorem isPrimitiveRoot_iff {p pc F g} :
    isPrimitiveRoot (p := p) pc F g = true ↔
      Hex.Nat.orderOf g p = p - 1

def primitiveRoot? {p : Nat} (pc : CheckedPrimeCert p)
    (F : CheckedFactorization (p - 1)) (fuel : Nat) :
    Option (Nat × CheckedOrderCert)

theorem primitiveRoot?_spec {p pc F fuel g c}
    (h : primitiveRoot? (p := p) pc F fuel = some (g, c)) :
    c.raw.base = g ∧ c.raw.modulus = p ∧ c.raw.order = p - 1

def carmichael {n : Nat} (F : CheckedFactorization n) : Nat

theorem pow_carmichael {n : Nat} (F : CheckedFactorization n)
    (a : Nat) (ha : Nat.Coprime a n) :
    a ^ carmichael F % n = 1 % n

theorem orderOf_dvd_carmichael {n : Nat} (F : CheckedFactorization n)
    (a : Nat) (hn : 1 < n) (ha : Nat.Coprime a n) :
    Hex.Nat.orderOf a n ∣ carmichael F
```

All three consume certified data rather than a `Nat`. An earlier draft
had `isPrimitiveRoot (g p : Nat) : Bool` and
`carmichael (n : Nat) : Nat`, both of which silently need a complete
factorization that the fuel-limited search may not have produced:
`isPrimitiveRoot` would have to answer `false` on exhaustion, which is
wrong, and `carmichael` had no failure channel at all.

`primitiveRoot?` handles `p = 2` with `g = 1`; for odd primes it scans
the residues `2 ≤ g < p` in ascending order and returns the first that
checks. It is `Option`-valued only because the search is fuel-bounded,
since a primitive root exists modulo every prime. Returning a checked
order certificate, and stating how its fields relate to the requested
prime, makes a successful search result usable without trusting that
search.

`carmichael` is the lcm of its prime-power values. For odd `p`,
`λ(p^e) = (p - 1) * p^(e - 1)`. For `p = 2`, the values are `1` at
`e = 1`, `2` at `e = 2`, and `2^(e - 2)` at `e ≥ 3`; the empty
factorization gives `λ(1) = 1`. These cases are part of the definition,
not an implementation note. The two theorems above give the local
Mathlib-free semantics consumers need; the companion later identifies
the value with Mathlib's Carmichael function if and when that bridge is
useful.

Those theorems are not free consequences of hex-arith's current Fermat
lemma. Their Mathlib-free proof prerequisites are explicit milestone
obligations:

- Euler's congruence modulo an odd prime power, proved by lifting
  Fermat through the binomial theorem;
- the separate odd-unit congruence modulo `2^e`, giving exponent
  `2^(e-2)` for `e ≥ 3`;
- preservation of `a^k ≡ 1` when the exponent is multiplied; and
- combination of congruences across the pairwise-coprime prime powers
  in a checked factorization.

Hex-arith currently supplies Fermat modulo a prime, but not these
prime-power or CRT steps. They belong in `Order.lean` beneath
`pow_carmichael`; the milestone is not complete until they are proved.

**The generic form for hex-conway.** Primitivity of a field element is
`checkOrder` with `modulus` replaced by a finite field, and the
exponentiation done in `F_q` rather than in `Nat`. So `OrderCert`'s
shape is right and its arithmetic is not: the group changes. The clean
factoring is a shared `Factorization` of the group order plus a
per-group check, and hex-conway carries the `F_q` check with this
library supplying the factorization of `q − 1`. Stated here because
generalising `OrderCert` over an arbitrary group is the tempting move
and it buys nothing: two call sites, two lines each.

## The divisor-function API

```lean
def divisors {n} (F : CheckedFactorization n) : Array Nat   -- ascending
def numDivisors {n} (F : CheckedFactorization n) : Nat     -- τ, ∏ (eᵢ + 1)
def sigmaEntry (entry : PrimePower) (k : Nat) : Nat         -- one geometric sum
def sigma {n} (F : CheckedFactorization n) (k : Nat) : Nat -- σ_k
def totient {n} (F : CheckedFactorization n) : Nat         -- φ
def radical {n} (F : CheckedFactorization n) : Nat         -- ∏ pᵢ
def squarefreePart {n} (F : CheckedFactorization n) : Nat  -- ∏_{eᵢ odd} pᵢ
def squareDivisor {n} (F : CheckedFactorization n) : Nat   -- largest d with d² ∣ n
def isSquarefree {n} (F : CheckedFactorization n) : Bool   -- ∀ i, eᵢ = 1

theorem mem_divisors {n d} (F : CheckedFactorization n) :
    d ∈ (divisors F).toList ↔ d ∣ n
theorem divisors_nodup {n} (F : CheckedFactorization n) :
    (divisors F).toList.Nodup
theorem divisors_sorted {n} (F : CheckedFactorization n) :
    (divisors F).toList.Pairwise (fun a b => a ≤ b)
theorem numDivisors_eq_size {n} (F : CheckedFactorization n) :
    numDivisors F = (divisors F).size
theorem sigma_eq_sum {n k} (F : CheckedFactorization n) :
    sigma F k = ((divisors F).toList.map (fun d => d ^ k)).sum
theorem sigmaEntry_eq_powerSum (entry : PrimePower) (k : Nat) :
    sigmaEntry entry k =
      ((DivisorEnumeration.powers entry.prime entry.exponent 1).map
        (fun q => q ^ k)).sum
theorem totient_eq_count {n} (F : CheckedFactorization n) :
    totient F = ((List.range n).filter (fun a => Nat.Coprime a n)).length
theorem totient_eq_prod {n} (F : CheckedFactorization n) :
    totient F =
      (F.raw.factors.map fun e =>
        e.prime ^ (e.exponent - 1) * (e.prime - 1)).prod
theorem coprimeCount_mul {m n} (hcop : Nat.Coprime m n) :
    ((List.range (m * n)).filter (fun a => Nat.Coprime a (m * n))).length =
      ((List.range m).filter (fun a => Nat.Coprime a m)).length *
        ((List.range n).filter (fun a => Nat.Coprime a n)).length
theorem coprime_primePow_iff {a p e} (he : 0 < e) :
    Nat.Coprime a (p ^ e) ↔ Nat.Coprime a p
theorem coprimeCount_primePow {p e} (hp : Hex.Nat.Prime p) (he : 0 < e) :
    ((List.range (p ^ e)).filter (fun a => Nat.Coprime a (p ^ e))).length =
      p ^ (e - 1) * (p - 1)
theorem prime_dvd_radical_iff {n q} (F : CheckedFactorization n)
    (hq : Hex.Nat.Prime q) : q ∣ radical F ↔ q ∣ n
theorem squareDivisor_eq_prod {n} (F : CheckedFactorization n) :
    squareDivisor F =
      (F.raw.factors.map fun e => e.prime ^ (e.exponent / 2)).prod
theorem squarefreePart_eq_prod {n} (F : CheckedFactorization n) :
    squarefreePart F =
      (F.raw.factors.map fun e => e.prime ^ (e.exponent % 2)).prod
theorem squarefreePart_mul_square {n} (F : CheckedFactorization n) :
    squarefreePart F * squareDivisor F ^ 2 = n
theorem squareDivisor_spec {n} (F : CheckedFactorization n) :
    squareDivisor F ^ 2 ∣ n ∧
      ∀ d, d ^ 2 ∣ n → d ∣ squareDivisor F
theorem isSquarefree_iff {n} (F : CheckedFactorization n) :
    isSquarefree F = true ↔
      ∀ q, Hex.Nat.Prime q → ¬ (q ^ 2 ∣ n)
```

All public divisor functions take a `CheckedFactorization` rather than
a `Nat`, which is the API decision worth defending. Taking a `Nat` would
mean each call re-factors, and would mean each has to answer at `0` and at
inputs the search cannot handle. Taking certified data makes them total
functions whose semantic theorems need no side hypothesis, and makes the
cost model visible: factoring is expensive, while most certificate consumers
are linear in the number of prime-power entries. Divisor enumeration is the
stated exception.
The `coprimeCount_mul` and two `coprime*primePow` theorems are raw-`Nat`
ingredients for the totient proof, rather than additional divisor functions.

`squareDivisor` and `squarefreePart` traverse only the certified factor
list: the former multiplies `pᵢ^(eᵢ / 2)`, and the latter multiplies
`pᵢ^(eᵢ % 2)`. Neither operation scans candidate divisors or values below
the subject.

`divisors` returns ascending, which costs a sort over `∏(eᵢ + 1)`
entries and is what every consumer wants. `numDivisors` exists
separately because it is `O(k)` and computing it by `divisors.size`
would be exponential. The local semantic theorems are deliberate: the
Mathlib bridge proves correspondence with Mathlib's names, but the
Mathlib-free library must already say what each public result means.
At `k = 0`, `sigma` dispatches to `numDivisors`; an implementation using
the geometric-series product must not evaluate its `0 / 0` form. For
`k > 0`, each certified prime-power entry `(p, e)` contributes the exact
geometric sum `(q^(e + 1) - 1) / (q - 1)`, where `q = p^k`, and `sigma`
multiplies those contributions. Checked primality supplies `1 < q`, so
the division is exact; this route never enumerates the divisors.
`sigmaEntry` is total on arbitrary `PrimePower` values: at `k = 0` and
at base `1` it returns `e + 1`, at base `0` with positive `k` it returns
`1`, and in every case `sigmaEntry_eq_powerSum` identifies it with the
finite power sum over `powers p e 1`.

The semantic theorems also name real proof work rather than assumed
infrastructure. `mem_divisors` needs the bounded-exponent
characterization of a divisor of a product of distinct prime powers.
`totient_eq_count` needs two ingredients: the prime-power coprime count
and the multiplicative counting bijection for coprime moduli (a finite
CRT argument). `coprimeCount_primePow` now supplies the first directly in
the Mathlib-free layer by counting periodic blocks modulo the base prime.
`coprimeCount_mul` supplies the second: the forward map sends a residue to
its representatives modulo the two coprime factors, and a constructive
extended-GCD inverse proves the resulting finite lists are permutations.
The zero/unit boundary is included in the theorem. The implementation of
`totient` uses these ingredients to justify the certified product
`∏ pᵢ^(eᵢ-1)(pᵢ-1)`. It traverses only the checked prime-power list and
does not enumerate residues below the subject.

## Complexity

`n` the input, `b = log₂ n`, `p` the smallest nontrivial factor, `k`
the number of distinct primes, `B` a smoothness bound.

| operation | cost | note |
|---|---|---|
| trailing-zero split | five bit operations on `b`-bit naturals | isolated-low-bit identity plus one shift; `O(b)` bit complexity |
| perfect-power test | `O(b²)` bounded multiplications | the committed prime exponents plus only prime candidates above the table; a `k`th-root search has `O(b/k)` probes of a linear, early-aborting power loop |
| trial division to `T` | `O(π(T))` divisions | `π(10^4) = 1229` |
| Pollard rho | `O(√p)` iterations expected and one routine gcd per 32-step batch | `O(n^{1/4})` for a semiprime; cycle boundaries can flush shorter batches |
| Pollard `p − 1` stage 1 | `O(B)` modular mults | `log M = Θ(B)`; smooth `p − 1` is sufficient but not decisive |
| ECM stage 1, one curve | `O(B)` mults | scalar bit length is `Θ(B)`; success depends on the bound |
| `checkFactorization` | `O(Σ eᵢ)` bounded multiplications plus `k` primality replays | `boundedPowMul` is linear in the claimed exponent and aborts above the subject |
| `checkOrder` | `O(k)` modular exponentiations plus `checkFactorization` | includes the order's primality replays |
| `divisors` | `O(τ log τ)` | `τ = ∏(eᵢ + 1)` |
| `sigma` | `O(k)` geometric sums | each entry uses `O(log r + log e)` multiplications for power argument `r`; for fixed `p` and `r`, its output has `Θ(e)` bits |
| `totient` | `O(Σ log eᵢ)` multiplications | `k` certified prime-power contributions; no residue scan |
| everything else in the divisor API | `O(k)` | excludes `divisors` |

These are **arithmetic-operation counts on `Nat`** except where the table says
bit complexity explicitly: the operands are big integers throughout,
`boundedPowMul` uses up to `e` multiplications for `p^e`, and the divisor functions
are `O(k)` only if the output's bit length is ignored. A bit-complexity
model would have to name a multiplication cost and multiply through,
and this SPEC does not attempt one.

The shape of the table is the argument for the dispatch order: each
route's cost is governed by a different parameter, and they are tried
in increasing order of what they can afford to be wrong about.
`L_p[1/2, √2]` denotes the usual subexponential
`exp((√2 + o(1)) √(ln p ln ln p))`.

## Kernel exposure

The replay closure is `checkFactorization`, `checkOrder`, and what they
call: `Nat` multiplication and comparison, hex-primality's
kernel-facing `powModNat`, and `checkPrime`. The reducers in that closure are
`@[expose]`, and `decide +kernel` tests in
`bench/HexBench/IntFactorKernel.lean`, built by the
`HexIntFactorKernelProbe` CI target, fail if any of them stops reducing. The
SPEC does not invent a second public `Hex.powMod` name for the same operation.

Nothing in routes 0 through 3 is in that closure. Rho, `p − 1`, ECM,
the cyclotomic split, and the perfect-power test are search; they never
appear in a proof term and should not pay for exposure.

The divisor-function API sits between the two: it is cheap, it is
sometimes wanted in a proof (`totient` in a Fermat-Euler argument, say),
and it takes already-checked data. It is `@[expose]`. This exposure makes
the factor-list bodies available for definitional reasoning; it does not
promise kernel evaluation of `divisors`, whose asymptotically appropriate
`List.mergeSort` uses well-founded recursion. Proofs about that enumeration
use `mem_divisors`, `divisors_nodup`, and `divisors_sorted`; `numDivisors`
is the kernel-facing operation when only the count is required.

The probe also replays `numDivisors`, `sigma`, `totient`, `radical`,
`squarefreePart`, `squareDivisor`, `isSquarefree`, `carmichaelPrimePower`, and
`carmichael` on bounded inputs; `sigmaEntry` is replayed on a bare
`PrimePower`, matching its total API. Factorization tests reach both the table
and Pocklington primality routes. Valid and corrupt checker cases include a
non-minimal order witness, ensuring the tests exercise the final prime-divisor
criterion rather than merely normalizing constants.

## Conformance

Per [SPEC/testing.md](../../SPEC/testing.md). A driver at
`conformance/HexIntFactor/EmitFixtures.lean` exposed as
`lean_exe hexintfactor_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexIntFactor/intfactor.jsonl`, an oracle at
`scripts/oracle/intfactor_pari.py`, and one tuple appended to
`ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexIntFactor|hexintfactor_emit_fixtures|scripts/oracle/intfactor_pari.py|conformance-fixtures/HexIntFactor/intfactor.jsonl"
```

Fixture kinds: `factor` (a number and its prime-exponent list),
`divisorfn` (a number and `τ`, `σ₀`, `σ₁`, `σ₂`, `φ`, `rad`, `sqfpart`), `order` (a
base, a modulus, and the order), and `cyclotomic` (`b`, `n`, sign, and
the split).

Cases that must be present:

- `1`, `2`, `4`, and the primes and prime powers below `100`.
- **Perfect powers**: `2^{20}`, `3^{13}`, `(10^6 + 3)^2`, and a perfect
  power of a composite, `(6^5)^3`. These are the inputs that stall
  ECM and `p − 1`, and the route-level tests below check that the
  perfect-power detector fired rather than that the answer came out.
- **Semiprimes with balanced factors** at 32, 48, and 64 bits, the
  worst case for rho.
- **Pollard `p − 1` route cases**: a smooth-order semiprime and fixed
  base for which stage 1 yields a proper factor; a case yielding `1`;
  and a case yielding the whole modulus. A non-smooth `p − 1` is not by
  itself a promised failure, because the chosen base can have smaller
  smooth order.
- **`b^n ± 1`** for `b ∈ {2, 3, 5, 7, 10}` and `n` up to `32`,
  checked against the cyclotomic split as well as against the oracle.
  The split's product must equal the input exactly, which catches an
  off-by-one in the Möbius inversion that the factorization would hide.
- **`p^n − 1` for every committed hex-conway entry**, which is the
  consumer test.
- **Rejected certificates** of each kind: a composite listed as prime, a
  product that does not equal the subject, a repeated prime, a zero
  exponent, a descending list. As with hex-primality, no oracle
  produces these and they are constructed by hand.
- **Order cases**: a primitive root mod a prime, a non-primitive
  element, an element modulo a prime power, and an element modulo a
  composite whose unit group is not cyclic -- the last to check that the
  order API makes no cyclicity claim it cannot back.
- `factor 0`, which must be refused rather than answered.

**Oracle choice.** PARI's `factor`, `divisors`, `sigma`, `eulerphi`,
and `znorder` through cypari2 cover the whole surface, and cypari2 is
already installed by the CI dependency step. python-flint's
`fmpz.factor` is the second opinion and is also already installed.

sympy's `factorint` is the more convenient API and is **not installed**:
`.github/workflows/ci.yml` installs `python-flint`, `cypari2`, and
`conway-polynomials` and nothing else. Appending an oracle tuple that
imports sympy would fail. If a sympy oracle is wanted, adding it to
that install step and to the `HEX_REQUIRE_ORACLES` preflight in
`scripts/ci/run_oracles.sh` is part of this library's work, and this
SPEC takes the cheaper route of using the installed pair.

**End-to-end fixtures cannot tell which route ran.** Every route's
candidate goes through `checkFactorization`, and a broken route falls
through to the next one, so a fixture passes even if ECM is entirely
non-functional. The suite therefore needs route-level tests in Lean:
that the two-adic and perfect-power producers fired on their route-specific
inputs, that `p − 1`
distinguished proper-factor, `1`, and whole-modulus outcomes, that rho
found the factor within the expected iteration count for a fixed seed,
that ECM stage 1 distinguished its three gcd outcomes after a setup gcd of
one (including stage-found proper-factor and whole-modulus cases), that a
fixed-seed smooth-route schedule exercised the p−1 and ECM no-factor/whole
retry branches with exact event accounting and advanced random state, and that
`cyclotomicSplit?` ran before the generic dispatch on a `b^n − 1`
input. The internal `countPowerRoutes` diagnostic counts perfect-power
reductions: a pure two-adic split contributes zero, while a combined
two-adic/perfect-power candidate contributes one. This is the same division
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) makes, and it is worth more than the oracle
half.

## Benchmarking

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), with drivers at
`bench/HexIntFactor/Bench.lean`. Native and kernel suites: the kernel
side is `checkFactorization` replay, which is the cost a downstream
proof pays and is therefore the number that matters most.

Families:

- **Table-range inputs**, uniform below `10^8`, where trial division
  finishes. The required property is that the dispatch overhead is
  invisible on the case that dominates call volume.
- **Balanced semiprimes** at 32, 48, 64, and 80 bits. Route 1.
- **Smooth `p − 1` semiprimes** at the same sizes. Route 2; the base is
  fixed so the benchmark measures the specified stage-1 success case.
- **`b^n ± 1`**, with and without the cyclotomic split, which is the
  measurement that justifies the split existing.
- **Unbalanced semiprimes**, a small factor times a large one, where
  ECM is expected to win and rho is expected to as well -- reported
  together, because a route that never wins on any family should be
  removed rather than kept.
- **Certificate replay**, `checkFactorization` in the kernel on
  factorizations with `k` from `1` to `10` and factors up to `64` bits.
- **Order and primitive root**, primes up to `64` bits, reported
  separately from the factorization of `p − 1` they depend on, so the
  check's cost is visible next to the search's.
- **Generalized divisor sums**, with one ladder growing a prime-power
  exponent through multi-million-bit output and one growing the number
  of certified prime-power entries. Per-rung preparation constructs or
  selects the checked factorization outside the timed loop, so these isolate
  the geometric-sum and factor-product costs and rule out divisor enumeration.
  The native wall-clock models include big-integer cost: `n log n` for the
  exponentiation-dominated exponent ladder and `n²` for the sequential product
  of bounded-size table-prime entry sums into a linearly growing accumulator.

**Comparators.** PARI `factor` via cypari2 is **informational**:
PARI dispatches among trial division, SQUFOF, Pollard-Brent rho,
`p − 1`, and MPQS with tuned crossovers, and this library specifies
neither SQUFOF nor MPQS, so a required ratio would check an algorithm
that does not exist here. The written-down expectation is narrower: on
the **table-range** and **balanced semiprime** families the ratio
should be within a small constant, since both sides run the same two
algorithms there, and a large ratio means the rho inner loop is wrong
rather than that the dispatch is. GMP-ECM is **informational** on the
unbalanced family for the same reason and with the same caveat. The
PARI/python-flint oracle pairing is for conformance, not a performance
requirement.

No advance claim is made on anything the quadratic sieve would reach,
because nothing here reaches it.

## The Mathlib layer

```lean
theorem factors_eq (F : Factorization) (h : checkFactorization F = true) :
    F.subject.primeFactorsList =
      F.factors.flatMap fun e => List.replicate e.exponent e.prime

theorem factorization_eq (F) (h : checkFactorization F = true) (p : Nat) :
    F.subject.factorization p = (F.factors.find? (·.prime == p)).elim 0 (·.exponent)

theorem CheckedFactorization.factorization_eq {n} (F : CheckedFactorization n) (p : Nat) :
    n.factorization p = (F.raw.factors.find? (·.prime == p)).elim 0 (·.exponent)

theorem CheckedFactorization.primeFactorsList_eq {n} (F : CheckedFactorization n) :
    n.primeFactorsList =
      F.raw.factors.flatMap fun e => List.replicate e.exponent e.prime

theorem totient_eq {n} (F : CheckedFactorization n) :
    totient F = Nat.totient n
theorem sigma_eq, divisors_eq, divisors_list_eq, numDivisors_eq_card
theorem primeFactors_eq, radical_eq, isSquarefree_iff_squarefree
theorem squarefreePart_mathlib, squareDivisor_mathlib

theorem orderOf_unitOfCoprime {a n} (hn : 1 < n) (ha : Nat.Coprime a n) :
    orderOf (ZMod.unitOfCoprime a ha) = Hex.Nat.orderOf a n

theorem orderOf_natCast {a n} (hn : 1 < n) :
    orderOf (a : ZMod n) = Hex.Nat.orderOf a n

theorem orderOf_eq {c} (h : checkOrder c = true) :
    orderOf (ZMod.unitOfCoprime c.base (coprime_of_checkOrder h)) = c.order
```

`factorization_eq` is the pointwise multiplicity correspondence and
`factors_eq` is its canonical-list counterpart: Mathlib's
`Nat.factorization` is a `Finsupp` and this library's factorization is an
ascending prime-power list. They are outward-facing correspondences for
downstream consumers; checked-data corollaries avoid exposing raw certificate
bookkeeping at call sites. The arithmetic transports in this companion each
compose the core's Mathlib-free semantic theorem -- such as `mem_divisors`,
`totient_eq_count`, `sigma_eq_sum`, `isSquarefree_iff`, or
`squareDivisor_spec` -- with checker facts about products, prime support, and
multiplicity. `primeFactors_eq` exposes that support-shaped correspondence
directly. The `find?` and `flatMap` expressions in the public statements are
normal forms, not separately advertised executable operations. Exact Mathlib
helper declaration names are read from the pinned Mathlib during
implementation; the SPEC deliberately does not depend on remembered names
that may be deprecated or absent.

**No `DecidablePred Squarefree` instance on `Nat`.** Mathlib has one
(`Mathlib/Data/Nat/Squarefree.lean:234`), so a second would be a
duplicate that risks instance-selection churn, exactly as a second
`DecidablePred Nat.Prime` would. What the companion adds instead is the
witness form -- `squarefreePart_mul_square` and `squareDivisor_spec`
above --
which the decision procedure does not produce.

`orderOf_unitOfCoprime` is the function-level correspondence: it proves the
general unit result directly from the positive-power/minimality
characterisations on both sides, without computing an order or constructing a
certificate. `orderOf_natCast` covers every underlying ring element: the
coprime case follows from the unit result, while both sides are zero for a
nonunit. The certificate specialization `orderOf_eq` composes that
correspondence with
`order_eq_of_checkOrder`; the coprimality needed to name the unit is derived
by `coprime_of_checkOrder`, so the caller passes nothing extra.

## Milestones

1. **The certificate and the small routes.** `PrimePower`,
   `Factorization`, `CheckedFactorization`, `checkFactorization` and
   its theorems, `CheckedPartialFactorization`, `factorPartial?`, the
   structural reductions, and trial division against hex-primality's
   table. The whole library starts after
   hex-primality milestone 3, because `PrimePower` carries
   `PrimeCert`. This milestone returns checked partial data on every ordinary
   positive-input outcome; an internal aggregate rejection is explicit and
   retains both its rejected candidate and checked recovery snapshot. It returns
   a complete result when every residual prime can be certified and makes no
   blanket size claim. The committed Conway
   table is a required regression family, not a currently blocked
   consumer.

2. **The divisor-function API.** The total functions, their local
   semantic theorems, divisor-enumeration completeness, the prime-power
   coprime count, and the finite CRT counting bijection named above.

3. **The order API.** `OrderCert`, `CheckedOrderCert`, `checkOrder`,
   `order_eq_of_checkOrder`, the primitive-root result theorems,
   `carmichael`, `pow_carmichael`, and `orderOf_dvd_carmichael`,
   including the prime-power congruence prerequisites named above.

4. **Shared rho and Pollard `p − 1`.** Integrate hex-primality's
   `rhoFactor?` and land route 2 stage 1 upstream beside it (see the
   route description), with route-level tests written before the code.

5. **The cyclotomic candidate.** `cyclotomicSplit?`, its checked product
   theorem, the recursive evaluation candidate, and the `b^n ± 1`
   benchmark family. Ahead of ECM because it is cheaper and directly
   serves the motivating family.

6. **ECM stage 1.** Montgomery curves, Suyama parameterisation, the
   word/direct-`Nat` arithmetic dispatch, and its route-level tests.

7. **The companion.** The pointwise, canonical-list, and prime-support
   factorization correspondences; divisor and squarefree transports; the
   general `orderOf_unitOfCoprime` and `orderOf_natCast` correspondences; and
   the certificate specialization `orderOf_eq`. It adds no duplicate decidability instances. The
   factorization correspondence begins after milestone 1; divisor and
   order transports follow milestones 2 and 3 while later search routes
   proceed independently.

## File organisation

```
HexIntFactor/
  Cert.lean         -- PrimePower, Factorization, checkFactorization, soundness
  Partial.lean      -- PartialFactorization and checkPartial
  DivisorEnumeration.lean -- certified enumeration from prime powers
  Divisors.lean     -- the divisor-function API
  Small.lean        -- trailing zeros, perfect powers, trial division
  Rho.lean          -- adapter from the shared rho primitive to the dispatch
  PMinusOne.lean    -- adapter from the shared p-1 primitive to the dispatch
  Ecm.lean          -- Montgomery-curve ECM stage 1
  Cyclotomic.lean   -- cyclotomicSplit? and the checked candidate
  Order.lean        -- OrderCert, checkOrder, primitive roots, Carmichael
  Factor.lean       -- the dispatch, factor?, factorPartial?
HexIntFactor.lean
HexIntFactorMathlib/
  Factorization.lean -- factorization_eq, factors_eq and consequences
  Order.lean        -- general and certificate-level orderOf correspondences
HexIntFactorMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexIntFactor:
    deps: [HexPrimality, HexArith, HexBasic]
    mathlib: false
    done_through: 0
    status: draft
  HexIntFactorMathlib:
    deps: [HexIntFactor, HexPrimalityMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

`HexConway` need only gain a dependency on `HexIntFactor` if its table
growth is refactored to consume these shared certificates; Tier 2 has
already landed without it. `HexMvGcdMathlib` does **not** gain one: as set out above,
Mathlib already decides squarefreeness on `Nat`; hex-mv-gcd's SPEC has
already been corrected to use that instance and to cite this library
only for factorization-derived witnesses.

Neither `HexPrimality` nor `HexIntFactor` is in `libraries.yml` yet, so
the dependency claims above are draft prose rather than repository
state until those entries land.

## Open questions

- **The default fuel schedule.** Stated above as a function of bit
  length and not fixed. It should be set so that the 64-bit balanced
  semiprime family finishes with margin, measured rather than guessed.
- **Whether SQUFOF is worth adding.** It beats rho on 64-bit semiprimes
  by a useful constant and is a small algorithm, but it needs a
  continued-fraction development and its failure modes are subtler than
  rho's. Worth revisiting if the balanced-semiprime family shows the
  PARI ratio is dominated by that one range.
- **Whether Aurifeuillian factorizations belong in `cyclotomicSplit?`.**
  They are a finite family of identities rather than an algorithm, so
  adding them is a table. Worth doing once the `b^n ± 1` benchmark
  family produces a case where a factor stayed unfactored and an
  Aurifeuillian identity would have split it.
- **How much of the Cunningham tables to commit.** A committed table of
  known factorizations of `b^n ± 1` would make hex-conway Tier 2 cheap
  at any table size, at the cost of a large data file whose entries are
  each individually checkable by `checkFactorization`. This is exactly
  the case [future-work](../../SPEC/future-work.md)'s "Certificate serialization
  and caching" entry describes -- an expensive search run once and
  replayed -- and it should wait for that item rather than inventing a
  format here.
