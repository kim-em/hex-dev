# hex-primality (primality proofs at scale, depends on hex-arith)

Kernel-checkable primality: a Miller-Rabin compositeness witness, a
Pocklington certificate and its cube-root variant, a stored initial
segment with a kernel-reducible sieve behind it, and the `primality`
tactic that produces `Hex.Nat.Prime n` for a literal `n`. Mathlib-free.
The companion `hex-primality-mathlib` relates the predicate to
`Nat.Prime`, supplies
the `norm_num` interoperation, and is where a dependency on an external
Lean primality library may live.

This SPEC expands the "Better primality" entry in
[future-work](../future-work.md). That entry's diagnosis is right -- the
mechanism is in place and what it lacks is scale -- and two of its
recommendations do not survive contact with the repositories they name.
Both are corrected below, with the evidence, under "What PrimeCert
actually is".

## What the tree has today

`Hex.Nat.Prime` (`HexArith/Nat/Prime.lean:86`) is the Mathlib-free
predicate, `2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`, with Euclid's lemma
(`Prime.dvd_mul`), coprimality (`coprime_of_not_dvd`), the freshman's
dream (`add_pow_prime_mod`), and Fermat's little theorem
(`pow_prime_mod`) proved on top of it.

`Hex.Nat.isPrimeTrial` (`:561`) is bounded trial division with a
balanced binary recursion, so kernel reduction depth is logarithmic in
the candidate count while the number of remainder tests stays
`O(√n)`. It has soundness (`isPrimeTrial_isPrime`, `:646`) **and**
completeness (`isPrimeTrial_of_prime`, `:703`), so the pair is a
decision procedure in everything but name -- there is no
`Decidable (Hex.Nat.Prime n)` instance in the tree, and adding one is
two lines.

`HexArith.powMod` (`HexArith/Montgomery/Context.lean:1002`) is modular
exponentiation by repeated squaring, dispatching to Montgomery
arithmetic for odd word-sized moduli (`powModWordOdd`) and to
`HexArith.powModNat` otherwise. That, `Nat.gcd`, and `Nat.sqrt` are
every arithmetic primitive the checkers below need. Extended GCD is
search infrastructure rather than a checker primitive: `HexArith.extGcd`
(`HexArith/ExtGcd.lean:41`) is the pure `Nat` routine and
`HexArith.Int.extGcd` (`:396`) reaches GMP's `mpz_gcdext` through an
`@[extern]`. The namespace is `HexArith`, not `Hex`.

`hex-berlekamp-zassenhaus` carries 94 candidate primes in
`hotPathCandidates` (`HexBerlekampZassenhaus/PrimeSelection.lean:626`),
each built by `smallPrimeCandidateOfTrial p (by decide) (by decide)`,
covering every prime in `[3, 500]`. It proves both directions:
`mem_hotPathCandidates_prime` (every entry is prime and in range) and
`exists_mem_hotPathCandidates_of_prime` (every prime in range is an
entry), the second by `decide` over `Fin 501` at
`maxRecDepth 4096`.

So the shape of what is wanted already exists in miniature: a stored
segment, verified complete over its range, consulted by a caller that
needs "some prime with property `P`". What is missing is a segment
larger than 500 and a way to prove a single prime larger than trial
division reaches.

## What PrimeCert actually is

[future-work](../future-work.md) says PrimeCert is "kernel-only (no
`native_decide`, so compatible with the project proof policy)" and
that "depending on it beats reimplementing Pocklington". The first is
true. The second is not available in the form stated, and a third claim
in that entry -- that initial-segment sieves "remain open" -- is
overtaken by what the repository contains.

Checked against a clone of https://github.com/b-mehta/PrimeCert
(Bhavik Mehta and Kenny Lau) at commit `924f63d9`. Every claim below is
about that revision, and a later one may differ. The repository's
`LICENSE` is **MIT**; individual file headers say "Released under
Apache 2.0 license as described in the file LICENSE", which disagrees
with it. Anyone reusing code from there should resolve that with the
authors first, and nothing in this SPEC depends on the answer, since
what is proposed below is a reimplementation from the published idea
rather than a copy.

- **It requires Mathlib.** `lakefile.toml` pins
  `leanprover-community/mathlib` at a revision, and the substantive
  files import it: `Pocklington.lean` imports
  `Mathlib.Algebra.Field.ZMod` and `Mathlib.Data.Nat.Totient`,
  `SieveCorrect.lean` imports `Mathlib.Data.Nat.Prime.Basic`,
  `SmallPrimes.lean` generates `Nat.Prime` proofs for 2 through 3000 by
  running `norm_num`. Design principle 2 says a Mathlib-free library
  depends only on Lean core and other Mathlib-free Hex libraries -- not
  even on Batteries. So **hex-primality cannot depend on PrimeCert**;
  only `hex-primality-mathlib` can.
- **Its executable cores are Mathlib-free.** `PrimeCert/Sieve.lean`,
  `PrimeCert/ForLean.lean`, and `PrimeCert/PredMod.lean` have no
  imports at all. The correctness proofs are on the Mathlib side of
  that line and the algorithms are not, which is the same split this
  project makes.
- **It implements Pocklington and the cube-root variant**
  (`Pocklington.lean`, `Pocklington3.lean`), with `pock%` and
  `prime_cert%` elaborators (`Meta/`), and certificate search delegated
  to a Python script that calls sympy, GNU `factor`, or a built-in
  Pollard rho.
- **It has a kernel-reducible Sieve of Eratosthenes.**
  `PrimeCert/Sieve.lean` holds the sieve state as a single `Nat` used
  as a bitset over the residues coprime to `6`, with `markMaskK`
  running 32 doubling rounds, covering `M < 2^{32}` and so `n` up to
  roughly `1.3 · 10^{10}`. `PrimeCertTest/SieveVerify1e8.lean` exercises
  it at `10^8`.
- **Its toolchain is `leanprover/lean4:v4.33.0`**; hex-dev is on
  `v4.32.0-rc1` with Mathlib pinned at `v4.32.0-rc1-patch1`. So even the
  companion cannot depend on it today without a toolchain bump on one
  side or the other.

Three consequences, and they are the design decisions this SPEC turns
on.

1. **Pocklington has to be proved here, Mathlib-free.** Not because
   PrimeCert's proof is inadequate, but because the layer that needs it
   is Mathlib-free and the boundary is not negotiable. The good news is
   that the proof is elementary and the tree already has its
   ingredients; the lemma list is under "The Pocklington certificate".
2. **The sieve question is not open.** A kernel-reducible sieve in the
   shape PrimeCert uses is known to work at `10^8`. The future-work
   entry's suggestion -- bootstrap the primes below `10^4` from the
   primes below `10^2` by kernel-reducible trial division -- is a
   strictly weaker technique aimed at the same target, and it should
   not be built. What should be built is the bitset sieve, with its
   correctness proved against `Hex.Nat.Prime`.
3. **Collaboration beats both duplication and dependency.** The
   Mathlib-free executable sieve is 116 lines of `Nat` bit arithmetic
   and its design is the contribution; reimplementing it here from the
   same idea, with attribution, is what the licence and the layering
   allow. Where a result is genuinely wanted on the Mathlib side -- the
   cube-root Pocklington variant is the clearest case -- the right move
   is an upstream contribution to PrimeCert and a companion-side
   dependency once the toolchains line up, not a second implementation
   in this tree.

## Scope

In scope: the `Decidable (Hex.Nat.Prime n)` instance; Miller-Rabin as
an untrusted filter with a proved compositeness direction; the
Pocklington certificate, its checker, and its soundness theorem; the
cube-root variant; a stored initial segment and the sieve that
generates and verifies it; a `primality` tactic; and the
`hex-primality-mathlib` correspondence with `Nat.Prime`.

Not in scope: elliptic curve primality proving (ECPP), which is where
the next order of magnitude lives and is a separate project with a
separate certificate; deterministic Miller-Rabin as a *proof* (see
below); primality of numbers of special form (Lucas-Lehmer, Proth,
Pepin), which are cheap to add later and have no consumer here; and
integer factorization, which is [hex-int-factor](hex-int-factor.md) and
depends on this library.

**Deterministic Miller-Rabin is out of scope as a proof technique, and
the reason is worth recording.** For `n < 3.3 · 10^{24}` the first 13
primes are known to be a sufficient witness set (Sorenson-Webster).
That is a published theorem about a computation over an enormous range,
and formalising it is a research project, not a lemma. So the bases-are-
sufficient result may be used to decide *what to try*, and may never
appear in a proof term. `isProbablePrime` therefore has soundness in
one direction only, and the API says so in its name and its theorem
list.

## The predicate stays in hex-arith

`Hex.Nat.Prime` and `isPrimeTrial` do **not** move here.
`HexModArith.Prime` builds `ZMod64.PrimeModulus` on `Hex.Nat.Prime`,
and hex-mod-arith depends only on hex-arith. Moving the predicate up
would put hex-mod-arith above hex-primality and drag the whole `F_p`
stack with it.

So the layering is: hex-arith owns the predicate, Fermat, Euclid's
lemma, and trial division; hex-primality owns everything that scales
past trial division. `hex-primality` deps:
`[HexArith, HexBasic]` -- hex-basic for `Hex.Rand`, which
[hex-finite-field](hex-finite-field.md) introduces and sites there.
This is the one authoritative dependency list; the `libraries.yml`
block at the end repeats it and nothing else in this file states it
again.

Three additions hex-arith should take, all of which its own theorems
nearly earn already:

```lean
instance : DecidablePred Hex.Nat.Prime :=
  fun n => decidable_of_iff (isPrimeTrial n = true)
    ⟨isPrimeTrial_isPrime, isPrimeTrial_of_prime⟩

theorem exists_prime_dvd (h : 2 ≤ d) : ∃ q, Prime q ∧ q ∣ d
theorem exists_prime_le_sqrt (h : 2 ≤ n) (hcomp : ¬ Prime n) :
    ∃ p, Prime p ∧ p ∣ n ∧ p * p ≤ n
```

The instance belongs next to the two theorems that prove it, and makes
`decide` available on small `n` without importing this library. The two
existence lemmas are what the Pocklington argument finishes with;
hex-arith has `exists_trial_divisor` (`HexArith/Nat/Prime.lean:609`),
which is `private` and produces a divisor rather than a *prime*
divisor, so it can be neither imported nor used as it stands.

There is also a **kernel-facing modular exponentiation** amendment,
under "Kernel exposure" below, which is where the real work in this
list is.

## Miller-Rabin

```lean
namespace Hex.Nat

/-- Multiplicative order of `a` modulo `n`, defined for `1 < n` and
`Nat.Coprime a n` as the least `k > 0` with `a ^ k % n = 1 % n`, and
`0` on every other input. The junk value is a deliberate choice: it
makes `0 < orderOf a n` the hypothesis that says "this is a real
order", and every theorem below carries it. -/
def orderOf (a n : Nat) : Nat

/-- The Miller-Rabin test at base `a`. `false` is a proof of
compositeness; `true` is evidence and nothing more. -/
def millerRabin (n a : Nat) : Bool

/-- Run `millerRabin` over a base list. -/
def isProbablePrime (n : Nat) (bases : List Nat := defaultBases) : Bool
```

`millerRabin` branches, in this order, and the branch list is part of
the specification rather than an implementation detail:

| condition | result | reason |
|---|---|---|
| `n < 2` | `false` | not prime |
| `n = 2` | `true` | prime |
| `n` even | `false` | composite |
| `a % n = 0` | `true` | inconclusive; `a` carries no information |
| `1 < Nat.gcd a n` | `false` | a proper divisor, so composite |
| otherwise | the strong test | below |

The strong test: write `n - 1 = 2^s · d` with `d` odd. The base `a` is
a **witness for compositeness** when `a^d ≢ 1 (mod n)` and
`a^{2^i d} ≢ n - 1 (mod n)` for every `i < s`. `millerRabin n a`
returns `false` exactly when `a` is such a witness, and each step is one
`HexArith.powMod` followed by squarings, so the test is `O(log n)`
modular multiplications.

```lean
theorem not_prime_of_millerRabin_false {n a : Nat}
    (h : millerRabin n a = false) : ¬ Hex.Nat.Prime n
```

The `a % n = 0` branch is not tidiness, it is what makes the theorem
true. An implementation that runs the strong test on `a = 0` returns
`false` at `n = 3`, and `¬ Prime 3` is false. An earlier draft of this
SPEC omitted the branch and asserted the opposite: that `n ∣ a` makes
the first witness clause *fail*. It makes it hold, since `0 ≢ 1`.

The proof, for the `otherwise` branch, with `n` odd, `n > 2`, and
`Nat.gcd a n = 1`. Suppose `n` is prime. hex-arith proves Fermat in the
form `a^p % p = a % p` (`pow_prime_mod`, `HexArith/Nat/Prime.lean:527`),
not in the multiplicative form, so the first step is a cancellation
lemma giving `a^{n-1} % n = 1 % n` from coprimality; that lemma is a
prerequisite, listed below. Then the sequence
`a^d, a^{2d}, …, a^{2^s d} = a^{n-1}` ends at `1`. If it does not start
at `1`, take the least `i` with `a^{2^{i+1} d} ≡ 1` and set
`x = a^{2^i d} % n`. Then `n ∣ x² - 1 = (x-1)(x+1)`, so by Euclid's
lemma (`Prime.dvd_mul`, already in hex-arith) `n ∣ x - 1` or
`n ∣ x + 1`. The first contradicts the choice of `i`; the second says
`x = n - 1`, contradicting the witness clause. Coprimality gives
`x ≠ 0`, which is what licenses the factorisation of `x² - 1` in `Nat`
without truncated subtraction.

Prerequisite lemmas, none of which the tree has:

```lean
theorem pow_pred_mod (hp : Prime p) (h : Nat.Coprime a p) : a ^ (p - 1) % p = 1 % p
theorem orderOf_pos (h1 : 1 < n) (h : Nat.Coprime a n) : 0 < orderOf a n
theorem orderOf_dvd_of_pow_eq_one (h : a ^ k % n = 1 % n) (hk : 0 < k) :
    orderOf a n ∣ k
theorem orderOf_dvd_pred (hp : Prime p) (h : Nat.Coprime a p) : orderOf a p ∣ p - 1
theorem prime_dvd_of_two_le (h : 2 ≤ d) : ∃ q, Prime q ∧ q ∣ d
theorem exists_prime_le_sqrt (h : 2 ≤ n) (hcomp : ¬ Prime n) :
    ∃ p, Prime p ∧ p ∣ n ∧ p * p ≤ n
```

The last is the composite-witness lemma the Pocklington argument
finishes with. hex-arith has a version of it, but
`exists_trial_divisor` (`HexArith/Nat/Prime.lean:609`) is `private`
and returns a divisor rather than a *prime* divisor, so it can be
neither imported nor used as it stands. Exporting a prime-divisor form
from hex-arith is a prerequisite amendment, and it is the same
statement `isPrimeTrial_isPrime` already needs internally.

**No completeness theorem accompanies `isProbablePrime`**, and none
should be attempted. `isProbablePrime n = true` proves nothing about
`n`; it is consumed only as a filter ahead of certificate construction,
and every one of its call sites is a search, never a proof.

`defaultBases` is the first 13 primes. Sorenson-Webster show those
suffice for every `n < 3.3 · 10^{24}`
([arXiv:1509.00864](https://arxiv.org/abs/1509.00864)). That result is
not assumed by any proof in this library: the bases are a search filter
unless and until their bounded sufficiency is separately formalised,
which would need a formally checked exhaustive computation. The
distinction is narrower than an earlier draft of this SPEC drew it --
the base computations themselves may perfectly well appear in a proof
term, and do, inside `checkPrime`; it is the sufficiency claim that may
not.

## The Pocklington certificate

```lean
/-- A primality certificate. One inductive rather than two mutually
recursive declarations, because a `structure` referring forward to
`PrimeCert` while `PrimeCert` refers back to it does not elaborate. -/
inductive PrimeCert where
  /-- `n` is an entry of the stored table. -/
  | small (n : Nat)
  /-- Pocklington. `factors` partially factors `n - 1`: each entry is a
  base `a` and a certificate for a prime `q`, with exponent `e + 1`, so
  the exponent is positive by construction. -/
  | pock  (n : Nat) (factors : List (Nat × Nat × PrimeCert))   -- a, e, cert for q
  /-- The cube-root variant; see below. -/
  | pock3 (n : Nat) (r s : Nat) (factors : List (Nat × Nat × PrimeCert))

/-- The number a certificate is about. -/
def PrimeCert.subject : PrimeCert → Nat
  | .small n | .pock n _ | .pock3 n _ _ _ => n

def checkPrime (c : PrimeCert) : Bool
```

The prime `q` of each factor entry is **not stored**; it is read off as
`cert.subject`. An earlier draft stored both and did not check they
agreed, which let a certificate for `2` be attached to a claimed factor
`4` while the soundness proof assumed the claimed factor prime. Reading
it from the child removes the check by removing the redundancy, which
is the better of the two fixes.

`checkPrime` on `pock n factors` verifies, cheapest first:

1. `2 ≤ n` and `n` is odd.
2. The subjects `q` of the child certificates are pairwise distinct.
3. Each child is accepted by `checkPrime`, recursively.
4. `F = ∏ q^(e+1)` divides `n - 1`.
5. `n < F * F`.
6. For each `(a, e, child)`, with `q = child.subject`:
   `powMod a (n-1) n = 1 % n` and
   `Nat.gcd ((powMod a ((n-1)/q) n + n - 1) % n) n = 1`.

Step 5 is `n < F * F` rather than `n.sqrt < F`. The two are equivalent
and the multiplication is cheaper and easier to reason about than
`Nat.sqrt`.

Step 6's gcd argument is written modularly. The checker cannot form the
literal `a^{(n-1)/q}`, only its residue `x`, and `Nat.gcd (x - 1) n` is
the wrong expression at `x = 0` because `Nat` subtraction truncates.
`(x + n - 1) % n` is `x - 1` modulo `n` at every residue.

**No `gcd(F, R) = 1` condition is needed.** The square-root Pocklington
theorem concludes "every prime divisor `p` of `n` satisfies `F ∣ p - 1`"
from `F ∣ n - 1`, the certified complete factorization of `F`, and the
per-prime conditions alone. The coprimality hypothesis belongs to the
cube-root variant, not to this one.

Step 6 is two modular exponentiations and one `Nat.gcd` per factor;
step 4 is one multiplication and one division. So one level of the
checker costs `O(k)` modular exponentiations for `k` factors, each
`O(log n)` modular multiplications.

```lean
theorem prime_of_checkPrime {c : PrimeCert} (h : checkPrime c = true) :
    Hex.Nat.Prime c.subject
```

The soundness proof, in the order the pieces should be built. The order
lemmas are the ones listed under Miller-Rabin above; these are the
additional ones.

- **`prime_pow_dvd_orderOf`**: if `q` is prime, `q^j ∣ m`,
  `a^m ≡ 1 (mod p)`, and `a^{m/q} ≢ 1 (mod p)`, then
  `q^j ∣ orderOf a p`. Stated with `q^j ∣ m` as a hypothesis rather
  than through a `q`-adic valuation, so that no valuation API is needed
  for this one use.
- **`dvd_of_coprime_prime_powers`**: a product of powers of distinct
  primes, each dividing `m`, divides `m`. This is what turns the
  per-factor conclusions into `F ∣ orderOf a p`.
- **gcd-to-noncongruence transport**: `Nat.gcd ((x + n - 1) % n) n = 1`
  and `p ∣ n` give `x ≢ 1 (mod p)`.
- **The Pocklington step**: let `p` be any prime divisor of `n`. Step 6
  gives `a^{(n-1)/q} ≢ 1 (mod p)` and `a^{n-1} ≡ 1 (mod p)`, so
  `q^(e+1) ∣ orderOf a p` for each factor, hence `F ∣ orderOf a p`,
  and `orderOf a p ∣ p - 1`, so `F ≤ p - 1` and `p ≥ F + 1`. If `n`
  were composite it would have a prime divisor `p` with `p * p ≤ n`, and
  `n < F * F ≤ (p-1) * (p-1) < p * p` contradicts that. So `n` is
  prime.

That inventory is longer than an earlier draft of this SPEC suggested,
and it is the honest cost of the Mathlib-free boundary: multiplicative
Fermat, order existence, order divisibility, prime-power extraction,
gcd-to-noncongruence transport, coprime-prime-power products, and the
prime small-divisor lemma are seven developments, none individually
hard, none currently present.

### The cube-root variant

Pocklington needs `F > √n`, which needs `n - 1` factored past half its
bits. The Brillhart-Lehmer-Selfridge extension relaxes that to roughly
`F > n^{1/3}`, which is a large practical difference because the cost
of producing a certificate is dominated by how far into `n - 1` the
factorization has to reach.

An earlier draft of this SPEC stated it as "`n = mF + 1` with
`0 ≤ m < F`, and `m = 2Fs + r`, provided `r² - 8s` is not a perfect
square". That is wrong and self-defeating: `m < F` forces `s = 0`, which
collapses the test back to the square-root regime and makes the
discriminant condition vacuous. The quantity being decomposed is the
*cofactor* `R = (n-1)/F`, not a residue below `F`.

`checkPrime` on `pock3 n r s factors` verifies, with `F` as above:

1. Everything the `pock` arm verifies except step 5.
2. `F` is even.
3. `R = (n-1)/F` is odd. (The classical hypothesis is
   `gcd(F, R) = 1`; `R` odd is the weaker condition the proof actually
   uses once `F` is even, and it is what the formalised statement
   takes.)
4. `R = 2 F s + r` with `1 ≤ r < 2 F`.
5. `n < (F + 1) * (2 * F * F + (r - 1) * F + 1)`.
6. `s = 0`, or `r * r < 8 * s`, or `r * r - 8 * s` is not a square.

Condition 6's middle disjunct is not redundant: `r² < 8s` makes
`r² - 8s` negative, hence automatically a non-square, and writing it out
avoids encoding a negative quantity with truncated `Nat` subtraction.
The integer square test is `let t := Nat.sqrt m; t * t == m`.

The hypothesis set above is the one in the formalised Coq treatment,
Grégoire, Théry and Werner, "A Computational Approach to Pocklington
Certificates in Type Theory",
https://www-sop.inria.fr/members/Benjamin.Gregoire/Publi/pock.pdf, and
matching it is deliberate: PrimeCert's `Pocklington3.lean` states the
same theorem, so a future companion-side dependency becomes a
substitution rather than a translation.

### What an accepted certificate proves, and what it does not

`prime_of_checkPrime` is **checker soundness**: an accepted certificate
proves its subject prime. Four further statements are distinct from it
and none is claimed:

- *certificate existence*: every prime has a `PrimeCert`. True, by
  induction, but not proved here and not needed.
- *checker completeness*: every mathematically valid certificate is
  accepted. Worth having as a regression test, not as a theorem.
- *search completeness*: `primeCert?` finds one. False, and the
  `Option` in its type says so.
- *the certificate carries no second witness obligation*. This one does
  hold, and it is what makes this item cheap relative to most of
  [future-work](../future-work.md): primality is the whole conclusion,
  with no minimality, maximality, or completeness clause left over.

The certificate is also small -- `O(k)` numbers of at most `log n` bits
per level, recursively -- and the search that finds it, which needs a
partial factorization of `n - 1`, runs entirely untrusted.

That last point is why the dependency runs the way it does.
hex-int-factor depends on hex-primality, because a factorization
certificate has to prove its factors prime. hex-primality does **not**
depend on hex-int-factor, because the factorization of `n - 1` it needs
is search, not proof. To keep it that way, hex-primality owns
`partialFactor`: trial division by the stored table followed by Pollard
rho, with a fuel bound.

`partialFactor` is **internal**, not part of the public API. An earlier
draft exposed it with "no correctness theorem at all", which is safe
only if every consumer checks everything, and its return type said
nothing about what it had produced. It keeps one theorem, which is what
both consumers need and all they need:

```lean
/-- Candidate partial factorization: bases with positive exponents, and
an unfactored residual. No primality and no completeness is claimed. -/
structure PartialFactors where
  factors  : List (Nat × Nat)
  residual : Nat

private def partialFactor (n fuel : Nat) : PartialFactors

private theorem partialFactor_prod (n fuel : Nat) (hn : 0 < n) :
    ((partialFactor n fuel).factors.map (fun e => e.1 ^ e.2)).prod
      * (partialFactor n fuel).residual = n
```

hex-int-factor reuses this same Pollard rho rather than introducing a
second one: the primitive lives in the lower library and the elaborate
version, with Brent's cycle detection, `p - 1`, and ECM, lives in the
higher one.

**The multiplicative order is the new development**, and it is the
thing to build first because [hex-int-factor](hex-int-factor.md) needs
it too, for its primitive-root API. It belongs here, in
`HexPrimality/Order.lean`, and hex-int-factor consumes it.

### The cube-root variant

Pocklington needs `F > √n`, which needs a factorization of `n - 1` that
gets past half its bits. The Brillhart-Lehmer-Selfridge extension
relaxes that to `F > n^{1/3}` at the cost of a further condition: write
`n = m F + 1` with `0 ≤ m < F`, and `m = 2 F s + r` -- then `n` is prime
provided `r² - 8s` is not a perfect square (and `s = 0` or the
usual side conditions hold).

That is a materially better test in practice, because the difficulty of
producing a certificate is dominated by how far into `n - 1` the
factorization has to reach, and a cube root is much easier to reach
than a square root. It is milestone 4 rather than milestone 2 because
the perfect-square condition needs an exact integer square root and its
correctness argument, and because Pocklington alone is enough for every
consumer this tree has today.

PrimeCert's `Pocklington3.lean` is the reference for the exact
hypothesis set (`pocklington3_test (N F R m r s)` there), and its
statement is what this SPEC's version should match, so that a future
companion-side dependency is a substitution rather than a translation.

### The certificate is complete

Unlike most items in [future-work](../future-work.md), this one needs
no second witness. `checkPrime c = true` establishes `Prime c.subject`
outright: primality is the whole conclusion, and there is no
minimality, maximality, or completeness clause left over. The
certificate is also small -- `O(k)` numbers of at most `log n` bits for
`k` factors, recursively -- and the search that finds it, which needs a
partial factorization of `n - 1`, runs entirely untrusted.

That last point is why the dependency runs the way it does.
hex-int-factor depends on hex-primality, because a factorization
certificate has to prove its factors prime. hex-primality does **not**
depend on hex-int-factor, because the factorization of `n - 1` it needs
is search, not proof. To keep it that way, hex-primality owns a small
untrusted `partialFactor`: trial division by the stored segment
followed by Pollard rho, with a fuel bound and no correctness theorem
at all. hex-int-factor then builds on that same rho rather than
introducing a second one -- the primitive lives in the lower library and
the elaborate version lives in the higher one.

## Initial segments

Two products, and conflating them is the mistake to avoid: a **stored
table** that callers consult, and a **sieve** that generates and
verifies it.

```lean
/-- Every prime below `primeTableBound`, ascending. A committed literal,
checked against one `sieve` evaluation by `decide +kernel`; it is not
recomputed from the sieve at use time. -/
def primeTable : Array Nat

/-- Membership, by binary search. -/
def isTablePrime (n : Nat) : Bool

theorem primeTable_sorted : primeTable.toList.Chain' (· < ·)
theorem mem_primeTable_prime {n : Nat} (h : n ∈ primeTable) : Hex.Nat.Prime n
theorem mem_primeTable_of_prime {n : Nat} (hp : Hex.Nat.Prime n)
    (hlt : n < primeTableBound) : n ∈ primeTable
theorem isTablePrime_iff {n : Nat} : isTablePrime n = true ↔ n ∈ primeTable
```

`primeTable_sorted` gives distinctness and is what the binary search
needs; `isTablePrime_iff` is what lets a caller conclude anything from
a lookup. `PrimeCert.small n` is accepted by `checkPrime` exactly when
`isTablePrime n = true`.

Both directions, because the second is what a caller needs to conclude
anything from a *failed* lookup, and because
`exists_mem_hotPathCandidates_of_prime` shows an existing consumer
already needs exactly that shape.

The sieve is the kernel-reducible bitset described above: state a
single `Nat`, bits indexed by the residues coprime to `6`, marking by
subtracting a mask built with doubling rounds. Its correctness theorem
is

```lean
/-- Index `t` names the number `numOfIndex t`, running over the
residues coprime to `6`: `0 ↦ 1, 1 ↦ 5, 2 ↦ 7, 3 ↦ 11, …`. -/
def numOfIndex (t : Nat) : Nat

theorem sieve_testBit_iff {bound sqrtBound t : Nat}
    (hsqrt : bound ≤ sqrtBound * sqrtBound) (ht : 0 < t)
    (hrange : numOfIndex t < bound) :
    (sieve bound sqrtBound).testBit t = true ↔ Hex.Nat.Prime (numOfIndex t)
```

The three hypotheses are all load-bearing and an earlier draft of this
SPEC had none of them. Without `hrange` the statement is false: above
the represented range every bit is clear while `numOfIndex t` may well
be prime. Without `ht` it is false at `t = 0`, where `numOfIndex 0 = 1`.
And `hsqrt` is what makes the marking loop complete.

Indexing the residues coprime to `6` excludes `2` and `3` by
construction, so the table's construction adds them explicitly and
`primeTable`'s two theorems, not the sieve's, are what a caller uses.

The table is then a `decide +kernel` consequence of one sieve
evaluation, not 168 or 3000 separate `decide` calls.

**`primeTableBound` is set by measurement, not chosen.** The bound is
whatever keeps the table's own verification inside the "few minutes on
the benchmark machine" budget that
[hex-conway](../../HexConway/SPEC/hex-conway.md) sets for its committed
table, and the same rule applies for the same reason. The
[future-work](../future-work.md) entry says timing targets belong in
the SPEC that adopts the technique, measured in this repository, so
this SPEC commits to the measurement and to the budget rule, and to no
number. The bench family "table verification" below is the measurement.

`hotPathCandidates` in hex-berlekamp-zassenhaus becomes a view of
`primeTable` restricted to `[3, 500]`, keeping its two existing
theorems as corollaries of the table's. That is the migration that
proves the table is the right shape: if it cannot replace the 94-entry
list without loss, it is not.

Two things that migration requires and an earlier draft of this SPEC
left out. `hotPathCandidates` is a `List SmallPrimeCandidate`
(`HexBerlekampZassenhaus/PrimeSelection.lean:499`), not a list of
naturals: each entry bundles a `ZMod64.Bounds p` instance and a
`Hex.Nat.Prime p` field, so the view is a proof-carrying map from table
entries rather than a projection. And it makes `HexBerlekampZassenhaus`
depend on `HexPrimality`, which its `libraries.yml` entry
(`[HexBerlekamp, HexHensel, HexLLL]`) does not record; that amendment
lands with the migration, not before.

**Statements of the form "every prime in `[1, x]` satisfies `P`"** are
what the sieve unlocks and what the table alone does not: the table
gives a list, and the completeness direction plus a `decide +kernel`
fold over it gives the universally quantified statement. That is the
case [future-work](../future-work.md) calls open, and it is open only
in the sense that nobody has run it.

## The API

```lean
namespace Hex.Nat

def isPrime (n : Nat) : Bool
def primeCert? (n : Nat) (r : Rand) (fuel : Nat) : Option (PrimeCert × Rand)
def checkPrime (c : PrimeCert) : Bool
def nextPrime? (n fuel : Nat) : Option Nat
def primesIn (lo hi : Nat) : Array Nat

theorem isPrime_iff {n : Nat} : isPrime n = true ↔ Hex.Nat.Prime n
theorem mem_primesIn {lo hi n : Nat} :
    n ∈ primesIn lo hi ↔ lo ≤ n ∧ n < hi ∧ Hex.Nat.Prime n
theorem nextPrime?_spec {n fuel p : Nat} (h : nextPrime? n fuel = some p) :
    n < p ∧ Hex.Nat.Prime p ∧ ∀ q, n < q → q < p → ¬ Hex.Nat.Prime q
```

`isPrime` dispatches: table lookup below `primeTableBound`; trial
division below a measured second threshold; `isProbablePrime` as a
filter; then `primeCert?` and `checkPrime`, falling back to trial
division whenever the search returns `none` or the checker rejects.
`isPrime_iff` is an iff, not a one-directional "soundness": trial
division is always available as a last resort and always terminates,
slowly and correctly, so the function decides.

`nextPrime?` is fuel-bounded rather than total. A total "least prime
greater than `n`" needs Euclid's theorem and a well-founded search, and
this tree has neither Mathlib-free; an earlier draft of this SPEC
declared `nextPrime : Nat → Nat` with no account of either. Adding
Euclid would make the total form available and is not on any consumer's
critical path, so the `Option` is what is specified, with the theorem
recording that the answer is the *least* such prime.

`primeCert?` returns `none` on fuel exhaustion, and fuel exhaustion is
reachable: the certificate search needs `n - 1` factored past a square
root (or a cube root), and there are `n` for which that is out of
reach. It threads `Rand` because `partialFactor` runs Pollard rho.
The `Option` propagates rather than being papered over, which is
design principle 8's third remedy again.

## The tactic

```
primality n         -- term: Hex.Nat.Prime n
primality           -- tactic: closes a `Hex.Nat.Prime e` goal
```

Following `factor_poly` and `irreducibility` in hex-berlekamp: the
search runs at elaboration time as untrusted compiled code, and the
emitted term is `prime_of_checkPrime (c := ⟨…⟩) (by decide +kernel)`
with the certificate reified as a literal. The kernel replays only
`checkPrime`, which is `O(k log n)` modular multiplications on
GMP-backed `Nat`, and never the search.

The companion adds `Nat.Prime n` through that correspondence, and
registers a
`norm_num` extension so `norm_num` picks it up on numerals too large
for `Mathlib/Tactic/NormNum/Prime.lean`'s trial division. Which of the
two runs on a given numeral is a threshold, and the threshold is
measured, not assumed.

## Kernel exposure

The replay closure is `checkPrime` and what it calls: a kernel-facing
modular exponentiation, `Nat.gcd`, `Nat.sqrt`, `Nat.mod`, and the
table's binary search.

**hex-arith needs an amendment before that closure exists**, and this
is the largest prerequisite in this SPEC. `HexArith.powMod`
(`HexArith/Montgomery/Context.lean:1002`) branches on whether the
modulus fits a `UInt64` and whether it is odd, taking a Montgomery path
in the good case, so the kernel has to be sent down the `Nat` route
instead. But:

- `HexArith.powModNat` (`:694`) is `@[expose]`, while its worker
  `powModNatGo` (`:685`) and `bitLength` (`:645`) are not, so kernel
  reduction stalls at the module boundary;
- `powModNat_eq` (`:795`) is `private`, so a downstream checker cannot
  use its correctness theorem at all;
- there is no `@[csimp]` relating `powMod` to `powModNat`, so the
  dispatching form and the kernel form are two unrelated functions.

The amendment: expose the recursion (an `@[expose]` parent with a
`where` helper is the cleanest shape), export the correctness theorem,
make the `p = 0` behaviour agree between the two forms, and register a
proved unconditional `@[csimp]` equality naming which is the
kernel-facing specification and which is the runtime twin. That is
principle 11's pattern, and until it lands `checkPrime` has no
kernel-reducible exponentiation to call. The bench family "kernel
replay" below is what confirms the choice was the right one.

An earlier draft of this SPEC also said every member of the closure is
`@[expose]`. That is not literally true -- core `Nat.gcd` is
extern-backed without the annotation -- and what matters is that each
reduces in the kernel, which the `decide +kernel` regression test in a
downstream module is what actually confirms.

The sieve is `@[expose]` and kernel-reducible by construction, since
generating the committed table is a kernel computation. Miller-Rabin,
`partialFactor`, Pollard rho, and `primeCert?` are search, appear in no
proof term, and are not exposed.

## Complexity

`n` the input, `b = log₂ n` its bit length, `k` the number of prime
factors in the certificate's factored part.

| operation | cost | note |
|---|---|---|
| `isTablePrime` | `O(log |primeTable|)` | binary search |
| `isPrimeTrial` | `O(√n)` remainder tests | hex-arith, unchanged |
| `millerRabin` one base | `O(b)` modular multiplications | |
| `isProbablePrime` | `O(13 b)` | fixed base list |
| `checkPrime`, one Pocklington level | `O(k b)` modular multiplications | |
| `checkPrime`, full tree | `O(K b)` modular multiplications | `K` = total factor entries over all nodes |
| `primeCert?` | dominated by `partialFactor` | unbounded; fuel-limited |
| sieve to `N` | `O(N / log N)` marking rounds | each a bit operation on an `N/3`-bit `Nat` |

These are operation counts, not bit complexity; the operands are big
integers and a bit-complexity model would have to name a multiplication
cost and multiply through. The recursion depth claim in an earlier
draft -- that each `q` is "at most half the bit length" of `n` -- was
wrong: `q` is at most about half the *value*, so the bit length drops
by roughly one per level, and the depth is `O(b)` rather than
`O(log b)`.

The one to watch is the sieve. The state is a single `Nat` of `N/3`
bits, so every marking step is a GMP `shiftLeft`, `lor`, and `land` on
a large integer rather than an array write. **Whether a compiled
`ByteArray` sieve would beat it is a benchmark hypothesis, not a
theorem** -- compiled `Nat` bit operations are big-integer operations
too. The two are nonetheless different products and the SPEC keeps them
apart: the bitset sieve exists to verify the committed table in the
kernel, and `primesIn` for runtime use is the array version. The
"segment generation" bench family below measures both.

## Conformance

Per [SPEC/testing.md](../testing.md). A driver at
`conformance/HexPrimality/EmitFixtures.lean` exposed as
`lean_exe hexprimality_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexPrimality/primality.jsonl`, an oracle at
`scripts/oracle/primality_pari.py`, and one tuple appended to
`ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexPrimality|hexprimality_emit_fixtures|scripts/oracle/primality_pari.py|conformance-fixtures/HexPrimality/primality.jsonl"
```

Fixture kinds: `isprime` (a number and the verdict), `certcheck` (a
certificate and whether the checker accepts), and `segment` (a range
and the list of primes in it).

Cases that must be present:

- `0`, `1`, `2`, `3`, `4`, and the first few primes and composites.
- Perfect squares of primes, and semiprimes `p·q` with `p` just below
  `√n` -- the inputs that break a trial-division bound off by one.
- **Carmichael numbers** -- `561`, `1105`, `1729`, `2465`, `6601`,
  `8911` -- where the Fermat test fails and Miller-Rabin must not. A
  Fermat test implemented by mistake passes every other fixture and
  fails these.
- **Strong pseudoprimes to specific bases**: `2047` (base 2), `1373653`
  (bases 2 and 3), `25326001` (2, 3, 5), `3215031751` (2, 3, 5, 7).
  These are the inputs that catch a base list quietly truncated.
- `n - 1` a power of two (`n = 2^k + 1`), where the Pocklington
  factorization is trivial and `F = n - 1 > √n` immediately.
- `n - 1` with a large prime factor, forcing certificate recursion two
  and three levels deep.
- A **rejected** certificate of each kind: `F ≤ √n`, a composite listed
  as a factor, a base failing the gcd condition, a factor not dividing
  `n - 1`. The checker's negative cases matter as much as its positive
  ones and no oracle produces them, so these are constructed by hand.
- Segments `[1, 100]`, `[1, 10^4]`, and one segment straddling
  `primeTableBound`, checking the table and the fallback agree across
  the boundary.
- The 94 `hotPathCandidates` entries, checking the migrated view has
  the same contents in the same order.

**Oracle choice.** PARI's `isprime`, `nextprime`, and `primes`
through cypari2 cover the whole surface, and cypari2 is already
installed by the CI dependency step; PARI's `isprime` with flag `1`
also returns a Pocklington-style certificate, which makes it the
natural cross-check for the `certcheck` fixtures. hex's checker should
accept PARI's certificates after translation, which is a stronger test
than agreeing on a verdict. python-flint's `fmpz.is_prime` is the
second opinion on the large cases and is likewise already installed.

sympy is **not installed**: `.github/workflows/ci.yml` installs
`python-flint`, `cypari2`, and `conway-polynomials` and nothing else, so
an oracle importing sympy would fail. Adding it would mean amending that
step and the `HEX_REQUIRE_ORACLES` preflight in
`scripts/ci/run_oracles.sh`; this SPEC uses the installed pair
instead.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexPrimality/Bench.lean`. Both native and kernel suites, because
the kernel side is the point of the library.

Families:

- **Table verification**, the `decide +kernel` cost of the committed
  table at bounds `10^4`, `10^5`, `10^6`, `10^7`. This family sets
  `primeTableBound`: the largest bound whose verification stays inside
  the few-minutes budget wins, and the number is committed only after
  it is measured here.
- **Kernel replay**, `checkPrime` on certificates for primes of `32`,
  `64`, `128`, `256`, and `512` bits. Decides the `powModNat`-versus-
  Montgomery question under "Kernel exposure".
- **Native decision**, `isPrime` across the same bit lengths, which is
  where the trial-division-to-certificate threshold is read off.
- **Certificate search**, `primeCert?` at the same sizes, reported
  separately because its cost is dominated by `partialFactor` and is
  therefore the family whose variance is largest and whose numbers say
  the least about this library.
- **Segment generation**, `primesIn` over ranges of `10^4` to `10^7`,
  native only.

**Comparators.** PARI `isprime` via cypari2 is **informational**: PARI
uses BPSW plus APRCL and a Pocklington-style certificate only on
request, so it is answering a different question by a different
method, and a required ratio would compare a checker against a prover.
sympy is the oracle, not a comparator. The right benchmarked
comparison for the kernel side is **PrimeCert itself**, and it is
`informational` for a reason worth stating: it is the closest prior art
and the one number a reader will want, and it cannot be run in this
repository until the toolchains agree. The comparison is recorded as a
figure to obtain, in a separate checkout, rather than as a CI
comparator.

## The Mathlib layer

```lean
theorem prime_iff {n : Nat} : Hex.Nat.Prime n ↔ Nat.Prime n

theorem primeTable_spec : ∀ n < primeTableBound, n ∈ primeTable ↔ Nat.Prime n
theorem primesIn_spec (lo hi) : ∀ n, n ∈ primesIn lo hi ↔ lo ≤ n ∧ n < hi ∧ Nat.Prime n
```

`prime_iff` is the whole correspondence, and it is one lemma: the two
predicates are the same definition modulo Mathlib's `Irreducible`
packaging, and `Nat.prime_def_lt` or `Nat.prime_def` closes it.
Everything else transports along it.

**No `DecidablePred Nat.Prime` instance.** Mathlib already declares
`Nat.decidablePrime` with its own `@[csimp]` runtime twin
(`Mathlib/Data/Nat/Prime/Defs.lean:162`, `:334`), so a second global
instance would be a duplicate and would risk instance-selection churn.
An earlier draft of this SPEC proposed one. What the companion offers
instead is the tactic and the `norm_num` extension, which is where the
scale actually helps.

The companion also carries the `norm_num` extension, the `Nat.Prime`
form of the `primality` tactic, and the universally quantified segment
statements ("every prime in `[1, x]` satisfies `P`") in the form a
Mathlib consumer would state them, over `Finset.filter Nat.Prime`.

**Where a PrimeCert dependency would go.** If the toolchains are
aligned, `hex-primality-mathlib` may depend on PrimeCert and re-export
`pock%` / `prime_cert%` for numerals beyond what this library's search
reaches, exactly as hex-rcf's SPEC allows a Mathlib-side tactic to
consume Mathlib-side infrastructure. That is an accelerator, never a
substitute: the Mathlib-free `checkPrime` and its soundness theorem
remain the tree's primality story, because every Mathlib-free consumer
-- hex-mod-arith's `PrimeModulus`, hex-berlekamp-zassenhaus's prime
selection, hex-gfq's field construction -- lives below the companion and
cannot see it.

## Milestones

0. **The hex-arith amendments.** The kernel-facing modular
   exponentiation with its exposed recursion, exported correctness
   theorem, and `@[csimp]` twin; `DecidablePred Hex.Nat.Prime`;
   `exists_prime_dvd` and `exists_prime_le_sqrt`. Everything below
   assumes these, and nothing below can be finished without them.

1. **The table and the sieve.** `sieve`, `sieve_testBit_iff` with its
   three hypotheses, `primeTable` with sortedness and both directions,
   `isTablePrime`, `primesIn`, and the `hotPathCandidates` migration
   with the `libraries.yml` amendment it forces. Independently useful,
   and the only part of this SPEC with no dependency on the certificate
   machinery.

2. **Miller-Rabin and the order.** `orderOf` with `orderOf_pos`,
   `orderOf_dvd_of_pow_eq_one`, and `orderOf_dvd_pred`; `pow_pred_mod`;
   `millerRabin` with its full branch list;
   `not_prime_of_millerRabin_false`; `isProbablePrime`. The order
   development is the prerequisite for milestone 3 and for
   [hex-int-factor](hex-int-factor.md).

3. **Pocklington.** `PrimeCert` as one inductive, `checkPrime`,
   `prime_of_checkPrime` with `prime_pow_dvd_orderOf` and
   `dvd_of_coprime_prime_powers` beneath it, the private
   `partialFactor` with `partialFactor_prod`, `primeCert?`, and
   `isPrime` with `isPrime_iff`. The `primality` tactic lands here.

4. **The cube-root variant.** `Pocklington3Cert` and its checker arm,
   with the exact integer square root it needs.

5. **The companion.** `prime_iff`, the transports, the `norm_num`
   extension, and the segment statements. Begins after milestone 1.

## File organisation

```
HexPrimality/
  Sieve.lean        -- the kernel-reducible bitset sieve and its correctness
  Table.lean        -- primeTable, isTablePrime, primesIn, both directions
  Order.lean        -- multiplicative order mod n, orderDvd, ord_dvd_pred
  MillerRabin.lean  -- millerRabin, isProbablePrime, the compositeness theorem
  Cert.lean         -- PrimeCert, PocklingtonCert, checkPrime, soundness
  Cert3.lean        -- the cube-root variant
  Search.lean       -- partialFactor, rho, primeCert?, isPrime, nextPrime?
  Elab.lean         -- the primality tactic
HexPrimality.lean
HexPrimalityMathlib/
  Prime.lean        -- prime_iff and the transports
  NormNum.lean      -- the norm_num extension
  Segment.lean      -- Finset-level segment statements
HexPrimalityMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexPrimality:
    deps: [HexArith, HexBasic]
    mathlib: false
    done_through: 0
    status: draft
  HexPrimalityMathlib:
    deps: [HexPrimality]
    mathlib: true
    done_through: 0
    status: draft
```

`HexBasic` is for the array and bit-manipulation shims; if none turn
out to be needed the dependency comes out.

## Open questions

- **`primeTableBound`.** Set by the table-verification benchmark. Until
  it is measured the table is built at `10^4`, which comfortably covers
  every consumer in the tree today and is certain to fit the budget.
- **Whether the sieve's correctness proof is worth its cost.** The
  alternative is to commit the table with a per-entry `isPrimeTrial`
  proof, as `hotPathCandidates` does today, which scales to perhaps
  `10^4` and no further. The sieve's proof is the larger investment and
  it is the only route past that bound. If milestone 1 stalls on the
  proof, committing the table with per-entry proofs at `10^4` is a
  complete and useful deliverable, and the sieve becomes milestone 6.
- **Whether ECPP belongs on the roadmap at all.** It is the next order
  of magnitude and it is a large project with an elliptic-curve
  prerequisite this tree does not have.
  [future-work](../future-work.md) notes that Bhavik Mehta has elliptic
  curve computations in flight, which is the strongest argument for
  waiting rather than starting.
- **How the `primality` tactic and `norm_num` should divide the range.**
  Both will be available on the Mathlib side and both will answer small
  numerals. A threshold is the obvious answer and the measurement is
  cheap; whether `norm_num` should simply delegate everything above a
  bound, or whether the two should stay independent, is a question
  about Mathlib-side ergonomics rather than about this library.
- **Whether `partialFactor` should live here or in hex-arith.** It has
  no correctness obligation, so it could sit lower and be shared. It is
  here because its only two consumers are this library's certificate
  search and [hex-int-factor](hex-int-factor.md), and moving it down
  would put Pollard rho in the arithmetic root for no gain.
