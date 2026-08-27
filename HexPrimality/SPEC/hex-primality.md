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
[future-work](../../SPEC/future-work.md). That entry's diagnosis is right -- the
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

`Hex.Nat.isPrimeTrial` (`:702`) is bounded trial division with a
balanced binary recursion, so kernel reduction depth is logarithmic in
the candidate count while the number of remainder tests stays
`O(√n)`. It has soundness (`isPrimeTrial_isPrime`) **and**
completeness (`isPrimeTrial_of_prime`), and `instDecidablePrime`
routes `decide` through the pair. (An earlier draft of this SPEC said
no `Decidable` instance existed and adding one was two lines; an
instance did exist, built on the linear `prime_iff_forall_lt`, and
the amendment below *replaced its body* rather than adding a second
instance, which would have risked instance-selection churn.)

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
`hotPathCandidates` (`HexBerlekampZassenhaus/PrimeSelection.lean:647`),
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

[future-work](../../SPEC/future-work.md) says PrimeCert is "kernel-only (no
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
- **Its toolchain is `leanprover/lean4:v4.33.0`**; hex-dev currently
  uses `v4.33.0-rc1` with Mathlib pinned to the matching release
  candidate. Stable and release-candidate Lean packages are not
  interchangeable, so a companion dependency still requires aligned
  pins. The exact gap must be rechecked at implementation time.

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

In scope: the hex-arith amendment adding the
`Decidable (Hex.Nat.Prime n)` instance; Miller-Rabin as
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
integer factorization, which is [hex-int-factor](../../SPEC/Libraries/hex-int-factor.md) and
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
[hex-finite-field](../../SPEC/Libraries/hex-finite-field.md) introduces and sites there.
This is the one authoritative dependency list; the `libraries.yml`
block at the end repeats it and nothing else in this file states it
again.

Three amendments hex-arith has taken, all of which its own theorems
nearly earned already:

```lean
instance instDecidablePrime (p : Nat) : Decidable (Prime p) :=
  decidable_of_iff (isPrimeTrial p = true)
    ⟨isPrimeTrial_isPrime, isPrimeTrial_of_prime⟩

theorem exists_prime_dvd (h : 2 ≤ d) : ∃ q, Prime q ∧ q ∣ d
theorem exists_prime_le_sqrt (h : 2 ≤ n) (hcomp : ¬ Prime n) :
    ∃ p, Prime p ∧ p ∣ n ∧ p * p ≤ n
```

The instance sits next to the two theorems that prove it, and makes
`decide` available on small `n` without importing this library. The two
existence lemmas are what the Pocklington argument finishes with, and
`exists_trial_divisor` (a nontrivial divisor yields one at most the
square root) is exported alongside them.

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
form `a^p % p = a % p` (`pow_prime_mod`, `HexArith/Nat/Prime.lean:668`),
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

Prerequisite lemmas (the last two are the hex-arith amendments above;
the rest are new here):

```lean
theorem pow_pred_mod (hp : Prime p) (h : Nat.Coprime a p) : a ^ (p - 1) % p = 1 % p
theorem orderOf_pos (h1 : 1 < n) (h : Nat.Coprime a n) : 0 < orderOf a n
theorem coprime_of_pow_mod_eq_one (h1 : 1 < n) (hk : 0 < k)
    (h : a ^ k % n = 1 % n) : Nat.Coprime a n
theorem orderOf_dvd_of_pow_eq_one (h1 : 1 < n) (hk : 0 < k)
    (h : a ^ k % n = 1 % n) :
    orderOf a n ∣ k
theorem orderOf_dvd_pred (hp : Prime p) (h : Nat.Coprime a p) : orderOf a p ∣ p - 1
theorem exists_prime_dvd (h : 2 ≤ d) : ∃ q, Prime q ∧ q ∣ d
theorem exists_prime_le_sqrt (h : 2 ≤ n) (hcomp : ¬ Prime n) :
    ∃ p, Prime p ∧ p ∣ n ∧ p * p ≤ n
```

The last is the composite-witness lemma the Pocklington argument
finishes with; it lives in hex-arith with `exists_prime_dvd` and the
exported `exists_trial_divisor` beneath it.

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
  /-- The cube-root variant; see below. `w` is the integer-square-root
  witness for the discriminant test: `Nat.sqrt` is well-founded recursion
  and does not kernel-reduce, so the checker verifies `w` with two
  multiplications instead of computing a root. -/
  | pock3 (n r s w : Nat) (factors : List (Nat × Nat × PrimeCert))

/-- The number a certificate is about. -/
def PrimeCert.subject : PrimeCert → Nat
  | .small n | .pock n _ | .pock3 n _ _ _ => n

def checkPrime (c : PrimeCert) : Bool

/-- An accepted certificate tied to the number requested by its caller. -/
structure CheckedPrimeCert (n : Nat) where
  raw       : PrimeCert
  subject_eq : raw.subject = n
  valid     : checkPrime raw = true
```

The indexed wrapper is the public result of certificate search. The subject
equality is load-bearing: `checkPrime` proves primality of `c.subject`, not of
an unrelated input that happened to request `c`.

The prime `q` of each factor entry is **not stored**; it is read off as
`cert.subject`. An earlier draft stored both and did not check they
agreed, which let a certificate for `2` be attached to a claimed factor
`4` while the soundness proof assumed the claimed factor prime. Reading
it from the child removes the check by removing the redundancy, which
is the better of the two fixes.

`checkPrime` on `pock n factors` verifies, with cheap structural and
arithmetic rejections before recursive certificate replay:

1. `2 ≤ n` and `n` is odd.
2. The subjects `q` of the child certificates satisfy `2 ≤ q` and are
   pairwise distinct.
3. `F = ∏ q^(e+1)` divides `n - 1`; each power is accumulated by a
   bounded loop and the whole product aborts as soon as its running
   value exceeds `n - 1`, rather than constructing an attacker-chosen
   enormous power.
4. `n < F * F`.
5. For each `(a, e, child)`, with `q = child.subject`:
   `HexArith.powModNat a (n-1) n = 1 % n` and
   `Nat.gcd ((HexArith.powModNat a ((n-1)/q) n + n - 1) % n) n = 1`.
6. Each child is accepted by `checkPrime`, recursively.

Step 4 is `n < F * F` rather than `n.sqrt < F`. The two are equivalent
and the multiplication is cheaper and easier to reason about than
`Nat.sqrt`.

Step 5's gcd argument is written modularly. The checker cannot form the
literal `a^{(n-1)/q}`, only its residue `x`, and `Nat.gcd (x - 1) n` is
the wrong expression at `x = 0` because `Nat` subtraction truncates.
`(x + n - 1) % n` is `x - 1` modulo `n` at every residue.

**No `gcd(F, R) = 1` condition is needed.** The square-root Pocklington
theorem concludes "every prime divisor `p` of `n` satisfies `F ∣ p - 1`"
from `F ∣ n - 1`, the certified complete factorization of `F`, and the
per-prime conditions alone. The coprimality hypothesis belongs to the
cube-root variant, not to this one.

Step 5 is two modular exponentiations and one `Nat.gcd` per factor;
step 3 is one bounded product and one division. So one level of the
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
  primes, each dividing `m`, divides `m`.
- **gcd-to-noncongruence transport**: `Nat.gcd ((x + n - 1) % n) n = 1`
  and `p ∣ n` give `x ≢ 1 (mod p)`.
- **The Pocklington step**: let `p` be any prime divisor of `n`. For
  each entry's own witness `a_q`, step 5 gives
  `a_q^{(n-1)/q} ≢ 1 (mod p)` and `a_q^{n-1} ≡ 1 (mod p)`, so
  `q^(e+1) ∣ orderOf a_q p ∣ p - 1`. Combining those pairwise-coprime
  prime powers gives `F ∣ p - 1`; there is no common witness and no
  claim that `F` divides one common multiplicative order. Thus
  `F ≤ p - 1` and `p ≥ F + 1`. If `n`
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

1. Everything the `pock` arm verifies except step 4 (the `n < F * F`
   bound, which the size condition below replaces). The per-factor
   witness conditions of step 5 are retained: they are the only route
   to "every prime divisor of `n` is `≡ 1 (mod F)`", which this
   variant needs exactly as the square-root one does. (An earlier
   draft said "except step 5", which would have been unsound.)
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
The non-square test verifies the stored witness:
`w * w < r * r - 8 * s && r * r - 8 * s < (w + 1) * (w + 1)`. An earlier
draft prescribed `let t := Nat.sqrt m; t * t == m`, but core `Nat.sqrt`
is defined by well-founded recursion and does not reduce in the kernel;
certificate search computes `w` with `Nat.sqrt` at runtime, where that
is harmless.

The hypothesis set above is the `m = 1` specialization of the
Brillhart-Lehmer-Selfridge theorem formalised in
Grégoire, Théry and Werner, "A Computational Approach to Pocklington
Certificates in Type Theory",
https://www-sop.inria.fr/members/Benjamin.Gregoire/Publi/pock.pdf, and
in PrimeCert's `Pocklington3.lean`. PrimeCert states the stronger form
with an extra parameter `m`, a check excluding divisors `lF + 1` for
`1 ≤ l < m`, and the corresponding relaxed bound. A future
companion-side dependency may instantiate it at `m = 1`; this checker
does not claim that stronger parameterised interface.

### What an accepted certificate proves, and what it does not

`prime_of_checkPrime` is **checker soundness**: an accepted certificate
proves its subject prime. Four further statements are distinct from it
and none is claimed:

- *certificate existence*: every prime has a `PrimeCert`. This is
  mathematically true using existence of suitable multiplicative-order
  witnesses, but it is not proved here and is not needed.
- *checker completeness*: every mathematically valid certificate is
  accepted. Worth having as a regression test, not as a theorem.
- *search completeness*: `primeCert?` finds one. False, and the
  `PrimeCertStop.exhausted` result in its type says so.
- *the certificate carries no second witness obligation*. This one does
  hold, and it is what makes this item cheap relative to most of
  [future-work](../../SPEC/future-work.md): primality is the whole conclusion,
  with no minimality, maximality, or completeness clause left over.

The certificate is also small -- `O(k)` numbers of at most `log n` bits
per level, recursively -- and the search that finds it, which needs a
partial factorization of `n - 1`, runs entirely untrusted.

That last point is why the dependency runs the way it does.
hex-int-factor depends on hex-primality, because a factorization
certificate has to prove its factors prime. hex-primality does **not**
depend on hex-int-factor, because the factorization of `n - 1` it needs
is search, not proof. To keep it that way, hex-primality owns the shared
untrusted Brent-rho primitive and an internal `partialFactor`: trial
division by the stored table followed by that primitive, with a fuel
bound.

```lean
/-- Why a proper-factor search stopped without a factor. -/
inductive RhoStop where
  | invalidInput
  | exhausted

/-- A resumable failure, following the tree's randomized-search convention. -/
structure RhoFailure where
  stop     : RhoStop
  attempts : Nat
  rand     : Rand

/-- A dynamically validated proper-factor candidate. -/
def rhoFactor? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure (Nat × Rand)

theorem rhoFactor?_spec {n d r r' fuel}
    (h : rhoFactor? n r fuel = .ok (d, r')) :
    1 < d ∧ d < n ∧ d ∣ n

structure Internal.RhoSuccess where
  factor   : Nat
  attempts : Nat
  rand     : Rand

def Internal.rhoFactorCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except RhoFailure Internal.RhoSuccess

theorem Internal.rhoFactorCounted?_spec {n r fuel success}
    (h : Internal.rhoFactorCounted? n r fuel = .ok success) :
    1 < success.factor ∧ success.factor < n ∧ success.factor ∣ n
```

The compatible pair-returning API is backed by the counted internal result
`Internal.RhoSuccess`, whose `factor`, `attempts`, and `rand` fields are
returned by `Internal.rhoFactorCounted?`. One attempt is one accepted restart
draw and Brent run, including the successful restart; rejection draws used to
choose that restart remain part of the same attempt. The ordinary
`rhoFactor?` projection does not rerun the search or alter its final state.
The deterministic even-input shortcut returns factor `2` with zero attempts
and an unchanged generator because it runs no restart.

`rhoFactor?` validates range and divisibility before returning.
Randomness and fuel affect only whether it finds a factor. The advanced
state is returned even on `.error`, so callers can resume rather than
accidentally reuse the same failed stream. `.invalidInput` covers
`n < 4`; `exhausted` includes prime inputs and any composite for which
no proper factor was found, and makes no primality claim. It is public
because hex-int-factor reuses this exact primitive; it does not certify
that `d` is prime and makes no completeness claim.

One restart uses Brent's power-of-two cycle schedule and accumulates up
to 32 differences modulo `n` before taking a gcd. Cycle boundaries also
flush a shorter batch. If a batched gcd is the whole modulus, the route
replays just that batch one difference at a time; the caller accepts only
a dynamically validated proper divisor. Each restart draws `c` from
`[1, n - 1]` and a start from `[0, n - 1]`. It globally rejects the
degenerate map `x ↦ x² - 2`; other offsets are rejected only with a start
that makes a fixed point of `x ↦ x² + c`. The rejection loop and each
restart's inner work are bounded. Both current worklist consumers share an
eight-restart cap before retaining the residual or trying later routes.

`partialFactor` is **internal**, not part of the public API. An earlier
draft exposed it with "no correctness theorem at all", which is safe
only if every consumer checks everything, and its return type said
nothing about what it had produced. It keeps the one theorem its
certificate-search consumer needs:

```lean
/-- Candidate partial factorization: bases with positive exponents, and
an unfactored residual. No primality and no completeness is claimed. -/
structure PartialFactors where
  factors  : List (Nat × Nat)
  residual : Nat

private def partialFactor (n : Nat) (r : Rand) (fuel : Nat) :
    PartialFactors × Rand

private theorem partialFactor_prod (n r fuel) (hn : 0 < n) :
    (((partialFactor n r fuel).1.factors.map
      (fun e => e.1 ^ e.2)).prod * (partialFactor n r fuel).1.residual) = n
```

hex-int-factor reuses `rhoFactor?` rather than introducing a second rho.
Brent's batched cycle detection and whole-modulus recovery are already
part of the lower primitive; the
higher library adds structural reductions, ECM, complete-factorization
assembly, and their dispatch. The routes by which its advances flow
back into this library's search are fixed below.

**The multiplicative order is the new development**, and it is the
thing to build first because [hex-int-factor](../../SPEC/Libraries/hex-int-factor.md) needs
it too, for its primitive-root API. It belongs here, in
`HexPrimality/Order.lean`, and hex-int-factor consumes it.

### Taking up downstream factoring advances

hex-int-factor's stronger factorization reaches this library's search
without inverting the proof dependency, in three ways:

1. **Certificate hand-off** (works today). `PrimeCert` is plain data
   and `checkPrime` accepts a certificate from any producer, so a
   caller that factors `n - 1` better than `partialFactor` assembles
   the node itself and lets the checker decide. hex-int-factor needs
   exactly this to prove its own certificate's factors prime.
2. **Shared stage-1 primitives sit here.** `rhoFactor?` does, and
   Pollard `p − 1` stage 1 joins it beside rho when hex-int-factor
   lands, under the same dynamically validated proper-factor contract
   and resumable-failure shape: both libraries want it, and it widens
   `partialFactor`'s reach cheaply. Its public smoothness request is capped by
   `smoothBound B = min B (primeTableBound - 1)`, so the committed table
   contains every required prime and `pMinusOneStage1_bound` identifies every
   larger request with that capped call. ECM stays downstream; curve
   arithmetic is a real dependency, not a shared primitive.
3. **An optional search hook**, deferred until hex-int-factor exists to
   consume it. A `primeCert?With
   (factor : Nat → Rand → Nat → PartialFactors × Rand)` variant
   parameterizes the untrusted search (defaulting to `partialFactor`),
   and the `primality` tactic and companion `norm_num` extension may
   additionally consult an elaboration-time extension that downstream
   libraries register under a well-known declaration name (the
   `Hex.FactorTactic.Extension` / `extensionNames` pattern of
   `HexBerlekamp/PolynomialTactic.lean`, with its ABI-version guard),
   so importing hex-int-factor transparently strengthens the tactic. This is the one route that
   adds public API surface, which is why it waits for its consumer.

Soundness is indifferent to all three: whatever finds the factors, the
kernel replays `checkPrime`.

## Initial segments

Two products, and conflating them is the mistake to avoid: a **stored
table** that callers consult, and a **sieve** that generates and
verifies it.

```lean
/-- Every prime below `primeTableBound`, ascending. A committed literal,
checked against one mathematical sieve run through bounded kernel-replayed
batches; it is not recomputed from the sieve at use time. -/
def primeTable : Array Nat

/-- Membership, by binary search. -/
def isTablePrime (n : Nat) : Bool

theorem primeTable_sorted : primeTable.toList.Pairwise (· < ·)
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
    (hmask : indexWidth bound ≤ 2 ^ 32)
    (hsqrt : bound ≤ sqrtBound * sqrtBound) (ht : 0 < t)
    (hrange : numOfIndex t < bound) :
    (sieve bound sqrtBound).testBit t = true ↔ Hex.Nat.Prime (numOfIndex t)
```

(`indexWidth bound` is the exact index count for values below `bound`;
an earlier draft wrote the mask hypothesis as `(bound - 1) / 3 < 2^32`,
tied to a width formula that over-counts at `bound ≡ 5 (mod 6)`. Each
doubling round also truncates to the width and skips shifts that alone
exceed it: an untruncated round at the 32-round budget would materialise
numbers of `step · 2^31` bits.)

The four hypotheses are all load-bearing. `hmask` is the range promised
by the fixed 32 doubling rounds; without it the marking masks no longer
cover the represented bitset. Without `hrange` the statement is false: above
the represented range every bit is clear while `numOfIndex t` may well
be prime. Without `ht` it is false at `t = 0`, where `numOfIndex 0 = 1`.
And `hsqrt` is what makes the marking loop complete.

Indexing the residues coprime to `6` excludes `2` and `3` by
construction, so the table's construction adds them explicitly and
`primeTable`'s two theorems, not the sieve's, are what a caller uses.

The table is a consequence of one sieve run, but not one monolithic
reduction. A Mathlib-free elaborator computes the bitset with a compiled
twin, emits equations for fixed-size batches of sieve steps, kernel-checks
each equation by reduction, and chains the equations to the final literal.
This is PrimeCert's `run_sieve` architecture and is required here: a
single enormous `decide +kernel` expression is not the scaling claim.

**`primeTableBound` is set by measurement, not chosen.** The bound is
whatever keeps the table's own verification, generated source size, and
incremental compile cost inside the "few minutes on
the benchmark machine" budget that
[hex-conway](../../HexConway/SPEC/hex-conway.md) sets for its committed
table, and the same rule applies for the same reason. The
[future-work](../../SPEC/future-work.md) entry says timing targets belong in
the SPEC that adopts the technique, measured in this repository, so
this SPEC commits to the measurement and to the budget rule, and to no
number. The bench family "table verification" below is the measurement;
its multi-bound sweep is still pending, so the committed `10^4` stands
on the budget rule alone.

`hotPathCandidates` in hex-berlekamp-zassenhaus becomes a view of
`primeTable` restricted to `[3, 500]`, keeping its two existing
theorems as corollaries of the table's. That is the migration that
proves the table is the right shape: if it cannot replace the 94-entry
list without loss, it is not.

Two things that migration requires and an earlier draft of this SPEC
left out. `hotPathCandidates` is a `List SmallPrimeCandidate`
(`HexBerlekampZassenhaus/PrimeSelection.lean:519`), not a list of
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
case [future-work](../../SPEC/future-work.md) calls open, and it is open only
in the sense that nobody has run it.

## The API

```lean
namespace Hex.Nat

inductive PrimeCertStop where
  | composite
  | exhausted

structure PrimeCertFailure where
  stop     : PrimeCertStop
  attempts : Nat
  rand     : Rand

structure PrimeDecisionFailure where
  attempts : Nat
  rand     : Rand

structure NextPrimeFailure where
  attempts : Nat
  rand     : Rand

def defaultPrimeFuel (n : Nat) : Nat

structure Internal.PrimeCertSuccess (n : Nat) where
  cert     : CheckedPrimeCert n
  attempts : Nat
  rand     : Rand

def Internal.primeCertCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (Internal.PrimeCertSuccess n)

theorem Internal.primeCertCounted?_composite {n r fuel f}
    (hresult : Internal.primeCertCounted? n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n

def primeCert? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (CheckedPrimeCert n × Rand)
def checkPrime (c : PrimeCert) : Bool
def isPrime? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeDecisionFailure (Bool × Rand)
def isPrime (n : Nat) : Bool
def nextPrime? (n : Nat) (r : Rand) (fuel : Nat) :
    Except NextPrimeFailure (Nat × Rand)
def primesIn (lo hi : Nat) : Array Nat

theorem isPrime_iff {n} : isPrime n = true ↔ Hex.Nat.Prime n
theorem isPrime?_spec {n r fuel b r'}
    (h : isPrime? n r fuel = .ok (b, r')) :
    b = true ↔ Hex.Nat.Prime n
theorem primeCert?_composite {n r fuel f}
    (hresult : primeCert? n r fuel = .error f)
    (hstop : f.stop = .composite) :
    ¬ Hex.Nat.Prime n
theorem mem_primesIn {lo hi n : Nat} :
    n ∈ primesIn lo hi ↔ lo ≤ n ∧ n < hi ∧ Hex.Nat.Prime n
theorem nextPrime?_spec {n r r' fuel p}
    (h : nextPrime? n r fuel = .ok (p, r')) :
    n < p ∧ Hex.Nat.Prime p ∧ ∀ q, n < q → q < p → ¬ Hex.Nat.Prime q
```

`isPrime?` dispatches: table lookup below `primeTableBound`; trial
division below a measured second threshold; `isProbablePrime` as a
filter; then `primeCert?`. A failed base returns a certified `false`, an
accepted certificate returns `true`, and an exhausted certificate search
returns `.error` rather than falling into an unbounded computation. The
indexed success prevents a certificate for one number from answering a
request about another.

`isPrime` is the pure total convenience API. It runs `isPrime?` with
`defaultPrimeFuel n` from the reproducible seed `Rand.ofSeed n` and
falls back to `isPrimeTrial` only if the bounded path exhausts its fuel.
Thus `isPrime_iff` is an
iff, while callers that need a real time bound and resumable random
state use `isPrime?`. No `fuel` argument is attached to a computation
whose worst-case fallback it does not bound.

`nextPrime?` is fuel-bounded rather than total. A total "least prime
greater than `n`" needs Euclid's theorem and a well-founded search, and
this tree has neither Mathlib-free; an earlier draft of this SPEC
declared `nextPrime : Nat → Nat` with no account of either. Adding
Euclid would make the total form available and is not on any consumer's
critical path, so `NextPrimeFailure` reports exhaustion with the attempt
count and advanced state. The theorem records that a success is the
*least* such prime.

`primeCert?` distinguishes `PrimeCertStop.composite`, justified by trial
division or a failed Miller-Rabin base, from `.exhausted`, which makes
no primality claim. Exhaustion is reachable: the certificate search needs `n - 1`
factored past a square root (or a cube root), and there are `n` for
which that is out of reach. `PrimeCertFailure` retains the advanced state and
exact attempt count because `partialFactor` runs Pollard rho.
`Internal.primeCertCounted?` also exposes that count on success, while
`primeCert?` is its compatibility projection. Certificate metering counts
every rho restart and every tried witness candidate, including successful
ones, throughout recursive child construction; deterministic table lookup,
Miller--Rabin filtering, and checker replay are not search attempts. Earlier
successful child and witness searches are accumulated before a later failure,
and both entry points return the same advanced state without duplicate work.
The failure propagates
rather than being papered over, which is
design principle 8's third remedy again.

## The tactic

```
primality n         -- term: Hex.Nat.Prime n
primality           -- tactic: closes a `Hex.Nat.Prime e` goal
primality n         -- tactic: adds `this : Hex.Nat.Prime n`
primality h : n     -- tactic: adds `h : Hex.Nat.Prime n`
```

Following `factor_poly` and `irreducibility` in hex-berlekamp: the
search runs at elaboration time as untrusted compiled code. The emitted
term applies `prime_of_checkPrimeAt` to the requested numeral, the inductive
certificate reified by its constructors, and one `Eq.refl true` slot. The
kernel reduces the subject-equality and `checkPrime` Boolean in that slot, so
it replays `O(k log n)` modular multiplications on GMP-backed `Nat`, and never
the search.

For reproducible syntax with no seed argument, the elaborator uses
`Rand.ofSeed n`; the lower `primeCert?` API remains explicitly seeded,
and diagnostics report the seed and attempts if certificate search
exhausts its fuel.

The companion adds `Nat.Prime n` through that correspondence. Bare
`primality` uses the certificate route directly. Pinned Mathlib's
`Nat.Prime` `norm_num` extension was registered first, so ordinary imports
retain Mathlib's trial-division behavior; the later Hex registration cannot
transparently pre-empt it. A module explicitly opts into the supported Hex
policy with `use_hex_primality_norm_num`. Under that policy, numerals below
`2^24` use a guarded alias of Mathlib's trial extension and larger numerals
use bounded Hex certificate search. The opt-in erasure is local to the
module and does not persist when that module is imported.

The `2^24` boundary comes from fresh one-goal modules on the pinned
toolchain. Each arm was a fresh importing module containing only one
`Nat.Prime` example. The trial arm used the ordinary Mathlib registration;
the certificate arm invoked the opt-in with the threshold temporarily set to
zero. Representative wall times in seconds were:

| numeral | trial division | certificate |
|---:|---:|---:|
| 100003 | 1.7 | 2.1 |
| 300007 | 1.4 | 1.0 |
| 1000003 | 1.6 | 1.7 |
| 3000017 | 1.5 | 3.6 |
| 10000019 | 3.1 | 3.4 |
| 30000001 | 3.4 | 3.5 |
| 33554467 | 2.4 | 1.7 |

These are policy measurements rather than a Phase-4 performance verdict:
they establish the crossover region while exposing that certificate search
is input-dependent. Mathlib's generated trial proof also reaches the pinned
default kernel recursion limit on the 31-bit Mersenne prime. Choosing the
power-of-two boundary keeps the full 24-bit range on the simpler route and
puts every 25-bit input on the bounded route. If certificate production or
factor search exhausts, the guarded trial alias also declines at that tier;
the opt-in never silently starts a large unbounded trial search.

## Kernel exposure

The replay closure is `checkPrime` and what it calls: a kernel-facing
modular exponentiation, `Nat.gcd`, `Nat.mod`, and the table's binary
search. `Nat.sqrt` is deliberately absent: it is well-founded recursion
and does not kernel-reduce, which is why the square bound is checked as
`n < F * F` and the cube-root discriminant through the stored witness.

**The hex-arith amendment that creates that closure** is the largest
prerequisite in this SPEC, and it is landed. `HexArith.powMod`
branches on whether the modulus fits a `UInt64` and whether it is odd,
taking a Montgomery path in the good case, so the kernel is sent down
the `Nat` route instead:

- `HexArith.powModNat`, its worker `powModNatGo`, and `bitLength` are
  all `@[expose]`, so kernel reduction no longer stalls at the module
  boundary;
- `powModNat_eq` is exported (with `0 < p`), alongside
  `powModNat_modulus_zero`;
- `powModNat` guards `p = 0` to `0`, matching `powMod`, which is what
  makes the `@[csimp]` equality `powModNat_eq_powMod` unconditional:
  `powModNat` is the kernel-facing specification and `powMod` the
  runtime twin (principle 11's pattern; the earlier state had
  `powModNat a n 0 = a ^ n`, a full unreduced power).

`checkPrime` is therefore written against `powModNat`. The bench
family "kernel replay" below is what confirms the choice was the
right one.

An earlier draft of this SPEC also said every member of the closure is
`@[expose]`. That is not literally true -- core `Nat.gcd` is
extern-backed without the annotation -- and what matters is that each
reduces in the kernel, which the `decide +kernel` regression test in a
downstream module is what actually confirms.

The sieve is `@[expose]` and kernel-reducible by construction, since
generating the committed table is a kernel computation. Miller-Rabin,
`rhoFactor?`, `partialFactor`, `primeCert?`, `isPrime?`, `isPrime`, and
`nextPrime?` are search or runtime dispatch, appear in no proof term,
and are not exposed. The `DecidablePred` instance continues to use
hex-arith's kernel-reducible `isPrimeTrial`.

## Complexity

`n` the input, `b = log₂ n` its bit length, `k` the number of prime
factors in the certificate's factored part.

| operation | cost | note |
|---|---|---|
| `isTablePrime` | `O(log |primeTable|)` | binary search |
| `isPrimeTrial` | `O(√n)` remainder tests | hex-arith, unchanged |
| `millerRabin` one base | `O(b)` modular multiplications | |
| `isProbablePrime` | `O(13 b)` | fixed base list |
| successful `isPrime?` | front end plus certificate search | bounded by explicit fuel after the fixed front end |
| `isPrime` worst case | `O(√n)` remainder tests | exact fallback after default search exhaustion |
| `checkPrime`, one Pocklington level | `O(k b)` modular multiplications | |
| `checkPrime`, full tree | `O(K b)` modular multiplications | `K` = total factor entries over all nodes |
| `primeCert?` | dominated by `partialFactor` | unbounded; fuel-limited |
| sieve to `N` | `O(√N + π(√N) · 32)` loop/doubling rounds | each marking round is a bit operation on an `N/3`-bit `Nat` |

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
apart: the bitset sieve exists to verify the committed table in the kernel,
while `primesIn` is the unrestricted trial-division range/filter route whose
result is converted to an `Array`. The "segment generation" bench family
below measures `primesIn`; the bitset sieve is priced by the "table
verification" family's module-elaboration cost.

## Conformance

Per [SPEC/testing.md](../../SPEC/testing.md). A driver at
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
through cypari2 cover the verdict surface, and cypari2 is already
installed by the CI dependency step. Current PARI exposes certificates
through `primecert`, not through the result of `isprime(n, 1)`;
`primecert(n,,1)` requests its N-1 certificate form. The oracle validates
that object with `primecertisvalid`, translates the cases satisfying this
checker's `m = 1` hypotheses, and commits accepted translations as
`certcheck` fixtures. Agreement on all `isprime` verdicts remains required
even when PARI chooses another certificate form. python-flint's
`fmpz.is_prime` is the second opinion on the large cases and is likewise
already installed.

sympy is installed by CI alongside `python-flint`, `cypari2`, and
`conway-polynomials` (an earlier draft of this SPEC said otherwise),
but PARI plus python-flint already cover the verdict surface and the
second opinion, so this SPEC uses that pair and adds no third
dependency.

## Benchmarking

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), with drivers at
`bench/HexPrimality/Bench.lean`. Both native and kernel suites, because
the kernel side is the point of the library.

Families:

- **Table verification**, the batched kernel-replay cost and generated
  artifact size of the committed table. Measured today only at the
  committed `10^4` (2.2 s of module elaboration after the sieve swap);
  the `10^5`-to-`10^7` sweep that would justify raising
  `primeTableBound` is a pending `scripts/bench` fresh-module family,
  and until it runs the committed bound is a floor chosen for safety,
  not the sweep's output.
- **Kernel replay**, `checkPrime` on certificates for primes of `31`,
  `61`, `123`, `256`, and `511` bits (the table-smooth ladder). Decides
  the `powModNat`-versus-Montgomery question under "Kernel exposure".
- **Native decision**, bounded `isPrime?` across the same bit lengths.
  The total `isPrime` gets no separate row: it differs only on the
  exhausted-search path, where its exact trial-division fallback is
  deliberately unbounded and would time out any row at these sizes.
- **Certificate search**, `primeCert?` at the same sizes, reported
  separately because its cost is dominated by `partialFactor` and is
  therefore the family whose variance is largest and whose numbers say
  the least about this library.
- **Segment generation**, `primesIn` over ranges of `10^3` to
  `3.2 * 10^4`, native only, capped by the CI bench-verify wallclock
  budget rather than by the API.

**Comparators.** PARI `isprime` via cypari2 is **informational**: PARI
uses BPSW plus APRCL and a Pocklington-style certificate only on
request, so it is answering a different question by a different
method, and a required ratio would compare a checker against a prover.
PARI is the oracle and python-flint the second opinion; neither is a
performance comparator. The right benchmarked
comparison for the kernel side is **PrimeCert itself**, and it is
`informational` for a reason worth stating: it is the closest prior art
and the one number a reader will want, and it cannot be run in this
repository until the toolchains agree. The pins are rechecked when the
benchmark is implemented; while they differ, the comparison is a figure
to obtain in a separate checkout rather than a CI comparator.

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
instead is the tactic and the explicitly opted-in `norm_num` policy, which
is where the scale actually helps.

The companion also carries the opt-in `norm_num` extensions and command,
the `Nat.Prime` form of the `primality` tactic, and the universally
quantified segment statements ("every prime in `[1, x]` satisfies `P`")
in the form a Mathlib consumer would state them, over
`Finset.filter Nat.Prime`.

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
   four hypotheses, the batched replay elaborator, `primeTable` with
   sortedness and both directions,
   `isTablePrime`, `primesIn`, and the `hotPathCandidates` migration
   with the `libraries.yml` amendment it forces. Independently useful,
   and the only part of this SPEC with no dependency on the certificate
   machinery.

2. **Miller-Rabin and the order.** `orderOf` with `orderOf_pos`,
   `coprime_of_pow_mod_eq_one`, `orderOf_dvd_of_pow_eq_one`, and
   `orderOf_dvd_pred`; `pow_pred_mod`;
   `millerRabin` with its full branch list;
   `not_prime_of_millerRabin_false`; `isProbablePrime`. The order
   development is the prerequisite for milestone 3 and for
   [hex-int-factor](../../SPEC/Libraries/hex-int-factor.md).

3. **Pocklington.** `PrimeCert` as one inductive, `checkPrime`,
   `prime_of_checkPrime` with `prime_pow_dvd_orderOf` and
   `dvd_of_coprime_prime_powers` beneath it, `CheckedPrimeCert`,
   the resumable failure types, the
   shared `rhoFactor?` with `rhoFactor?_spec`, the private
   `partialFactor` with `partialFactor_prod`, indexed `primeCert?`, and
   bounded `isPrime?` plus total `isPrime` with their result theorems.
   The `primality` tactic lands here.

4. **The cube-root variant.** The `PrimeCert.pock3` checker arm and its
   soundness case, with the stored square-root witness replacing any
   in-checker integer square root.

5. **The companion.** `prime_iff`, the transports, the explicit opt-in
   `norm_num` policy, and the segment statements. Begins after milestone 1.

## File organisation

```
HexPrimality/
  Sieve.lean        -- the kernel-reducible bitset sieve and its correctness
  SieveElab.lean    -- batched compiled generation and kernel replay
  Table.lean        -- primeTable, isTablePrime, primesIn, both directions
  Order.lean        -- multiplicative order mod n, orderDvd, ord_dvd_pred
  MillerRabin.lean  -- millerRabin, isProbablePrime, the compositeness theorem
  Cert.lean         -- PrimeCert, CheckedPrimeCert, checkPrime, soundness
  Cert3.lean        -- the cube-root variant
  Search.lean       -- rhoFactor?, partialFactor, primeCert?, isPrime?, isPrime, nextPrime?
  Elab.lean         -- the primality tactic
HexPrimality.lean
HexPrimalityMathlib/
  Prime.lean        -- prime_iff and the transports
  NormNum.lean      -- Nat.Prime tactic reach and opt-in norm_num policy
  Segment.lean      -- Finset-level segment statements
HexPrimalityMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexPrimality:
    deps: [HexArith, HexBasic]
    mathlib: false
    done_through: 0
    status: active
  HexPrimalityMathlib:
    deps: [HexPrimality]
    mathlib: true
    done_through: 0
    status: active
```

`HexBasic` is required for `Hex.Rand`; array and bit-manipulation shims
may add further uses, but the dependency does not depend on them.

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
  [future-work](../../SPEC/future-work.md) notes that Bhavik Mehta has elliptic
  curve computations in flight, which is the strongest argument for
  waiting rather than starting.
- **Whether `rhoFactor?` should eventually move to hex-arith.** It is
  here because its only two consumers are this library's certificate
  search and [hex-int-factor](../../SPEC/Libraries/hex-int-factor.md), and moving it down
  would put Pollard rho in the arithmetic root for no present gain.
  Pollard `p − 1` stage 1 will join it here for the same two consumers
  (see "Taking up downstream factoring advances"), which sharpens the
  question rather than settling it.
