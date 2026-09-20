# hex-primality (primality proofs at scale, depends on hex-arith)

Kernel-checkable primality: a Miller-Rabin compositeness witness, a
Pocklington certificate and its cube-root variant, a stored initial
segment with a kernel-reducible sieve behind it, and the `primality`
tactic that produces `Hex.Nat.Prime n` for a literal `n`. Mathlib-free.
The companion
[hex-primality-mathlib](../../HexPrimalityMathlib/SPEC/hex-primality-mathlib.md)
owns the `Nat.Prime` correspondence, transports, tactic registration, and
opt-in `norm_num` policy. This SPEC remains the sole normative owner of the
Mathlib-free search, certificate, checker, and core elaboration algorithms.

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
`HexArith.powModBits` otherwise. That, `Nat.gcd`, and `Nat.sqrt` are
every arithmetic primitive the checkers below need. Extended GCD is
search infrastructure rather than a checker primitive: `HexArith.extGcd`
(`HexArith/ExtGcd.lean:41`) is the pure `Nat` routine and
`HexArith.Int.extGcd` (`:396`) reaches GMP's `mpz_gcdext` through an
`@[extern]`. The namespace is `HexArith`, not `Hex`.

`hex-berlekamp-zassenhaus` carries 94 candidate primes in
`hotPathCandidates`, as two proof-carrying windows of `primeTable`, covering
every prime in `[3, 500]` in ascending order. It proves both directions:
`mem_hotPathCandidates_prime` (every entry is prime and in range) and
`exists_mem_hotPathCandidates_of_prime` (every prime in range is an
entry), directly from the corresponding `primeTable` membership theorems.

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
about that revision, and a later one may differ. The implementation claims
below have not been rechecked against the later comparator revision. The repository's
`LICENSE` is **MIT**; individual file headers carry an Apache 2.0 notice.
The primality checker is a separate implementation of the published ideas.
The modular-power accumulator in HexArith adapts `powModK` from the later
PrimeCert revision `7d3a2de`;
`HexArith/Montgomery/Context.lean` preserves both the file's Apache notice
and the complete root MIT permission notice from the pinned comparator
revision `7d3a2de`. This attribution does not introduce a PrimeCert or Mathlib
dependency.

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
- **The measured checkout uses `leanprover/lean4:v4.33.0`**; hex-dev
  uses `v4.34.0` with Mathlib pinned to a compatible commit.
  Packages built with different Lean toolchains are not
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
  | pock3Sieve (n r s w m : Nat) (factors : List (Nat × Nat × PrimeCert))

/-- The number a certificate is about. -/
def PrimeCert.subject : PrimeCert → Nat
  | .small n | .pock n _ | .pock3 n _ _ _ _ | .pock3Sieve n _ _ _ _ _ => n

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
   in strictly ascending order. This canonical order implies pairwise
   distinctness and is checked with one lower-bound comparison per entry
   (the first against `1`, then each later subject against its predecessor).
3. `F = ∏ q^(e+1)` divides `n - 1`. Powers use bounded multiplication,
   with a checked shift for powers of two. The kernel square-root checker
   combines exponent-one factors with one multiplication and a bound check,
   using zero to record overflow. The positive-subject precondition comes
   from step 2; zero cannot pass the subsequent square-root check. Each such
   multiplication has at most the sum of its operands’ bit lengths, and
   an oversized exponent is rejected without constructing its full power.
   The compiled checker retains its division-before-multiplication loop.
4. `n < F * F`.
5. For each `(a, e, child)`, with `q = child.subject`:
   `HexArith.powModNat a (n-1) n = 1 % n` and
   `Nat.gcd ((HexArith.powModNat a ((n-1)/q) n + n - 1) % n) n = 1`.
6. Each child is accepted by `checkPrime`, recursively.

For generated libraries that already hold the child-primality proofs,
`prime_of_pocklington` accepts `checkPockArith n factors = true` and
`∀ x ∈ factors, Prime x.2.2.subject`. It reuses the same Pocklington
soundness argument while sharing child proofs across parents. This API uses
the child subjects and their supplied primality proofs; it does not assert
that the child certificate payloads pass `checkPrime`. A `.small q` payload
may therefore name any separately proved prime in this API. The recursive
`checkPrime` and `CheckedPrimeCert` interfaces retain their full child checks.

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

Step 2 is at most `k` subject comparisons. Step 3 performs at most
`O(k log n)` bounded ordinary multiplications even on rejected input:
because step 2 established `q ≥ 2`, each entry either finishes or exceeds
the `n - 1` bound within `O(log n)` iterations. Step 5 uses one modular
exponentiation, one division, and one `Nat.gcd` per factor, plus a Fermat
exponentiation per group of adjacent equal witness bases. Thus one level
costs `O(k log n)` modular multiplications, `O(k log n)` bounded ordinary
multiplications, and `O(k)` subject comparisons, divisions, and gcds. The
factor list comes from untrusted certificate data; search sorts its candidate
list, but acceptance depends only on this kernel-replayed canonical-order
check.

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
with an extra parameter `m`. The `pock3Sieve n r s w m factors` constructor
implements that stronger form, proved by the Mathlib-free `pocklington3Sieve`:
it additionally checks `1 ≤ m ≤ pocklingtonSieveCap` (currently 64), excludes
divisors `lF + 1` for `1 ≤ l < m`,
and replaces condition 5 by `2s + m² < (2F + r)m + 2`. It retains all other
arithmetic, child-primality, ordering and witness checks. The cap and size bound
are checked before the sieve; even a rejected untrusted literal performs at
most 63 divisor tests. Construction uses the smaller of `maxSieveBound` and
this checker cap. The original `pock3`
constructor and literal proofs retain their sieve-free behavior. Neither form
requires an odd prime in the factor product; a power of two alone is valid.

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
untrusted Pollard `p − 1` and Brent-rho primitives and an internal
`partialFactor`: trial division by the stored table, one bounded stage-1
call, then rho, with a fuel bound.

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

inductive PMinusOneResult where
  | noFactor
  | factor (value : Nat)
  | whole

structure PMinusOneAttempt where
  result   : PMinusOneResult
  attempts : Nat
  rand     : Rand

def pMinusOneStage1 (n base bound : Nat) : PMinusOneResult

def pMinusOneStage1Counted (n base bound : Nat) (r : Rand) :
    PMinusOneAttempt

theorem pMinusOneStage1Counted_spec
    (h : (pMinusOneStage1Counted n base bound r).result = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n
```

The compatible pair-returning API is backed by the counted internal result
`Internal.RhoSuccess`, whose `factor`, `attempts`, and `rand` fields are
returned by `Internal.rhoFactorCounted?`. One attempt is one semantic restart:
its bounded sampling, any rejected pairs, and its Brent run, including the
successful restart. Sampler-internal and pair rejections advance `rand` but do
not add attempt units. If bounded sampling or the pair-draw loop exhausts, the
restart under construction counts once, retains its exact advanced state, and
the next allocated restart continues from there. The ordinary
`rhoFactor?` projection does not rerun the search or alter its final state.
The deterministic even-input shortcut returns factor `2` with zero attempts
and an unchanged generator because it runs no restart.

The p−1 counted boundary records all three terminal gcd outcomes. Every call
has `attempts = 1`; because stage 1 is deterministic, its returned `rand` is
exactly the supplied state. Thus callers charge a semantic p−1 attempt without
pretending it consumed a generator word. Both partial factorization and
hex-int-factor consume this boundary directly.

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
that makes a fixed point of `x ↦ x² + c`. Both coordinates use `Rand.nat`,
which concatenates enough 64-bit words for the arbitrary-precision bound and
rejects the incomplete top interval instead of reducing one word modulo the
bound. Each coordinate sample has 64 tries, and one semantic restart admits
eight pair draws. Sampler exhaustion or eight rejected pairs ends that restart
with the exact state; no undrawn fallback pair is substituted. The next
allocated restart continues from that state, and exhaustion of the overall
restart allocation returns `RhoStop.exhausted`. Each restart's inner work is
bounded as well. Both current worklist consumers share an eight-restart cap
before retaining the residual or trying later routes.

`partialFactor` itself is **internal**, not part of the public API. The stable
extension boundary is instead an explicitly untrusted result carrying the
candidate, resumed generator state, and semantic attempt count. A producer
receives the complete recursive, partial-factor, and rho allocation for that
invocation; it may return any candidate data, but only the final certificate
checker can accept it. The built-in adapter remains the default route and
retains the reconstruction theorem used internally:

```lean
/-- Candidate partial factorization: bases with positive exponents, and
an unfactored residual. No primality and no completeness is claimed. -/
structure PartialFactors where
  factors  : List (Nat × Nat)
  residual : Nat

structure FactorSearchResult where
  raw      : PartialFactors
  rand     : Rand
  attempts : Nat

structure FactorSearchBudget where
  primeBudget : PrimeCertBudget
  primeFuel   : Nat
  factorFuel  : Nat
  smoothBounds : List Nat := []
  smoothBases : List Nat := []

abbrev FactorSearch :=
  FactorSearchBudget → Nat → Rand → FactorSearchResult

def defaultFactorSearch : FactorSearch

private structure PartialSearch where
  raw      : PartialFactors
  rand     : Rand
  attempts : Nat

private def partialFactor (budget : PrimeCertBudget) (n : Nat)
    (r : Rand) (fuel : Nat) : PartialSearch

private theorem partialFactor_prod (budget n r fuel) :
    prodPows (partialFactor budget n r fuel).raw.factors *
      (partialFactor budget n r fuel).raw.residual = n
```

After table division, positive fuel permits one stage-1 call on a composite
cofactor, at base `2` and bound `64`. Zero fuel, a trivial cofactor, or a
probable-prime cofactor skips that call. A proper factor seeds the rho
worklist with the divisor and cofactor; a probable-prime cofactor enters the
factor list directly so rho does not repeat the same screen; `noFactor` and
`whole` both retain the original cofactor unsplit. Rho then receives the same
worklist-step fuel.
Every actual p−1 call contributes exactly one to `PartialSearch.attempts` and
leaves `PartialSearch.rand` unchanged.

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

### Pollard p-minus-one stage 2

This is the implementation contract for the continuation in
`HexPrimality/PMinusOne.lean`. The existing stage-1 API remains compatible;
the continuation, counted trace, and search-policy extensions below are new
work. They are Mathlib-free, untrusted search, shared with HexIntFactor.
They do not change certificate formats or the checker trust boundary.
For background on stage-2 continuation see Montgomery and Kruppa,
[Improved Stage 2 to P ± 1 Factoring Algorithms](https://antsmath.org/ANTSVIII/files/kruppa.pdf).
The bounded prime-by-prime baby/giant schedule here does not implement
their polynomial multipoint extension.

#### Bounds and stage boundary

For natural-number requests `B₁, B₂`, set
`b₁ = smoothBound B₁ = min B₁ 524288` and
`b₂ = stage2Bound B₂ = min B₂ 4194304`. The separate
`Hex.Nat.PMinusOne.stage2BoundCap = 4194304` (with `stage2Bound` in the
same namespace) is independent of `smoothBoundCap`, the ordinary
9999 policy cap, and the size of `primeTable`. It is a work ceiling, not a
claim of usefulness at that ceiling. Never raise either requested bound.
When `b₂ ≤ b₁`, the interval is empty; do not swap bounds or increase `b₂`.
Bounds 0 and 1 are accepted, with empty stage-1 exponent product `M = 1`.

The standalone call accepts all `Nat` inputs. As in stage 1, `n < 4`,
`a ≤ 1`, or `n ≤ a` gives `noFactor` before arithmetic. For `n ≥ 4` and
`1 < a < n`, compute `gcd(a,n)` first: a proper divisor returns `factor`
immediately. Otherwise `gcd(a,n) = 1`, and stage 1 computes

```
M = ∏ {ℓ prime | ℓ ≤ b₁} ℓ^(max {e | ℓ^e ≤ b₁})
x = a^M mod n
g₁ = gcd((x + n - 1) % n, n).
```

Execute the existing successive prime-power exponentiations, not an explicit
construction of `M`. A stage-1 `factor` or `whole` is terminal for this call;
stage 2 is entered only after `g₁ = 1` and a nonempty interval. Preserve `x`
at this boundary: no consumer may recompute `a^M` to start stage 2. Stage-1
`whole` cannot be repaired by further exponentiation of that residue.

Use the following new API in namespace `Hex.Nat.PMinusOne` (the existing
`Hex.Nat.pMinusOneStage1` names and their counted contracts stay available).
The excerpt assumes `Event` and its nested batch record, whose data schema
is specified below, are declared first:

```lean
structure Stage1 where
  result : PMinusOneResult
  residue : Option Nat
  event : Event

def start (n a B₁ : Nat) : Stage1
def stage2 (n x B₁ B₂ : Nat) : PMinusOneResult
def search (n a B₁ B₂ : Nat) : PMinusOneResult

structure Run where
  result : PMinusOneResult
  attempts : Nat
  rand : Rand
  events : List Event

def stage2Counted (n x B₁ B₂ : Nat) (r : Rand) : Run
def searchCounted (n a B₁ B₂ : Nat) (r : Rand) : Run

theorem stage2_spec (h : stage2 n x B₁ B₂ = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n
theorem search_spec (h : search n a B₁ B₂ = .factor d) :
    1 < d ∧ d < n ∧ d ∣ n
```

`start.result = pMinusOneStage1 n a B₁` exactly. Its residue is `some x`
exactly on valid input with both setup gcd and `g₁` equal to 1; in that case
prove `x < n`, `x = a^M % n`, and `gcd(x,n) = gcd((x+n-1)%n,n) = 1`.
Invalid-input `noFactor` has no residue. Its event records the branch and
work performed by this execution, without re-running setup to reconstruct
that diagnostic. `search` runs `start` once and, if
there is a residue and `b₂ > b₁`, runs `stage2`; otherwise it returns the
stage-1 result. An interval containing no primes returns `noFactor`.

The public raw-residue `stage2` is total and does not trust provenance:
`n < 4` returns `noFactor`; otherwise normalize `x % n`, then check
`gcd(x,n)` and `gcd((x+n-1)%n,n)`, in that order. Return a proper factor
from either check, or `whole` on gcd `n`, before enumerating candidates.
Only two gcds equal to 1 enter the interval algorithm. Thus an arbitrary
residue cannot invalidate `stage2_spec`; only the success lemma referring
to the original base requires `x = a^M % n`. The continuation receives no
base and performs no stage-1 exponentiation. Internal reuse of already
established gcd checks is permitted only with an equality to this public
result and an accurate trace of the work actually executed.

Every factor exit, including setup and recovery, dynamically tests
`1 < d ∧ d < n ∧ n % d = 0`. Prove the same proper-divisor theorem for
both counted projections, and projection equalities to the uncounted calls.
Prove equality of results when replacing both bounds by `(b₁,b₂)`; traces
retain requested as well as effective bounds, so do not assert equality of
whole traces under capping. Prove idempotence of each bound function.

One executed `stage2Counted` costs exactly one semantic attempt on every
outcome, including invalid or empty input. Batches and recovery add no
attempt units. `searchCounted` costs one for stage 1 plus one if it invokes
the continuation; an invalid standalone call still costs one, matching the
existing counted convention. A caller that already charged `start` must
charge only `stage2Counted`, not call `searchCounted` again. Each returned
`rand` equals its input, on success and failure alike.

#### Enumeration, layout, and gcd schedule

Enumerate `Q = (primesBelow (b₂ + 1)).filter (b₁ < ·)` when `b₂ > b₁`.
Prove `q ∈ Q ↔ Hex.Nat.Prime q ∧ b₁ < q ∧ q ≤ b₂`, strict ascending
order, and no duplicates, using `mem_primesBelow`,
`primesBelow_pairwise_lt`, and `primesBelow_nodup`. Neither primality of
enumerated candidates nor completeness may rely on an unverified committed
table. An empty interval skips sieve construction entirely. A nonempty
interval with `Q = []` skips residue-table construction.

Choose step `D = 210`. Use all remainders `0 ≤ j < D`, not a wheel that
silently omits primes 2, 3, 5, or 7. Build `u[0] = 1 % n` and
`u[j+1] = (u[j]*x) % n` through `j+1 = D`; retain babies `u[0..D-1]`
and step `h = u[D]`. For each prime use the unique index map
`i = q / D`, `j = q % D`, so `q = iD+j`. Initialize
`i₀ = Q.head / D`, `v = h^i₀ % n` by one binary exponentiation. In
ascending prime order, advance `v = v*h % n` once per increment of `i`,
including intervening blocks with no prime. Within one block reuse `v`.
The candidate term is

```
t(q) = ((v*u[j]) % n + n - 1) % n
v*u[j] ≡ x^(iD+j) = x^q (mod n).
```

This identity is exact for every enumerated prime. There is no inversion,
sign pairing, rounding of interval endpoints, or test at composite indices.
It needs no fresh exponentiation per prime. A prime equal to `b₂` is tested;
a prime equal to `b₁` is excluded. Primes dividing `D` use the same map.

Accumulate `P = (P*t(q)) % n`, initially `1 % n`, and retain the terms
with their primes in a buffer of at most `K = 32` entries. Flush after
exactly 32 candidates or at the final nonempty partial batch. Giant-block
boundaries and prime gaps do not flush. Do not take an extra gcd after a
final full batch, and do not take one for an empty batch.

At each flush compute `g = gcd(P,n)`:

- `g = 1`: discard that buffer, reset `P = 1 % n`, continue.
- `1 < g < n`: validate and return `factor g` immediately.
- `g = n`: scan the retained terms in ascending prime order, computing
  `gcd(t(q),n)` individually. Skip both 1 and `n`; return the first proper
  divisor after validation. In particular, a leaf with gcd `n` does not stop
  recovery before later leaves. If no leaf gives a proper divisor, return
  `whole` and stop this continuation. Never turn `whole` into a successful
  split, and do not continue into later batches after unsuccessful recovery.

No replayed exponentiation or product tree is needed for recovery. `noFactor`
means the interval ended with every batch gcd equal to 1 (or a documented
invalid/empty input); it makes no primality claim.

`Event` records stage-1 and continuation calls in execution order. A call
event contains the subject, base (stage 1 only), requested and effective
bounds, terminal outcome, and a reason for an invalid/empty early return.
A continuation event also contains the number of candidates evaluated,
giant advances, modular multiplications, and actual setup gcd count. Nested
batch records contain first/last prime, length, batch gcd, and the ordered
recovery gcds actually taken. Stage-1 events distinguish setup-factor,
stage-factor, stage-whole, and ready-residue outcomes. Within an enabled policy, skipping an eligible continuation
for budget or policy-cap reasons emits a zero-attempt diagnostic with the
reason and intended bounds. A disabled policy emits no new events; its
existing trace remains unchanged. Attempt totals come from counted results, not trace length;
diagnostics and nested batch records are not attempts. Traces are untrusted
data, never checker evidence. Define the nested batch record and `Event`
before `Run`; both are ordinary data types deriving `Repr, DecidableEq`,
as do `Stage1` and `Run`. The event fields and early-return reasons above
are the required data schema, not proof fields.

#### Conditional success

Let `p` be prime, `p ∣ n`, `gcd(a,n) = 1`, and `x = a^M % n`, for valid
standalone input. For each `q ∈ Q`, prove

```
p ∣ t(q) ↔ ord_p(a) ∣ M*q.
```

After stage-1 gcd 1, `ord_p(a) ∤ M`. This is a mathematical opportunity,
not a guarantee of a proper divisor: other components of `n` may divide
the same term or different terms in its batch. For a batch `C` actually
reached, define `P_C = (∏ q∈C t(q)) % n`. If such a `q` is in `C`, then
`p ∣ gcd(P_C,n)` and that gcd is greater than 1. If additionally
`gcd(P_C,n) < n`, the algorithm returns a proper factor at that flush.
If `gcd(P_C,n) = n`, recovery returns a proper factor exactly when some
leaf has `1 < gcd(t(q),n) < n`; otherwise it reports `whole`.

One sufficient, checkable proper-factor hypothesis is `n = p*r` for
distinct primes and `r ∤ t(s)` for every `s ∈ C`, while `p ∣ t(q)` for
some `q ∈ C`: then the batch gcd is `p`. These statements require that
the batch is reached; an earlier unrecoverable whole batch can terminate
the search. They are not equivalences with smoothness of `p-1`.
Even for stage 1, the sufficient condition is `p-1 ∣ M`, not merely that
all prime divisors of `p-1` are small: their powers must fit `M` too.

#### Work, storage, and arithmetic choice

Let `L = |Q|`, `G = floor(Q.last/D) - floor(Q.head/D)` for `L > 0`,
and `ell(k)` be binary bit length, with `ell(0) = 0`. A full continuation
uses at most

```
D + 2*ell(floor(Q.head/D)) + G + 2*L modular multiplications,
2 + ceil(L/32) + 32 gcds,
D + 32 + 10 working residues modulo n (excluding the optional trace).
```

The terms pay for babies/step, the initial giant, giant advances, and
candidate evaluation plus accumulation. The two gcds are raw-residue
preflight; at most one whole batch is recovered. For `L = 0`, no modular
multiplications or batch gcds occur. Proper-divisor validation adds at most
one division/remainder test on a factor exit. Every multiplication includes
reduction modulo `n`; operands have at most `bitLength(n)` bits and the
unreduced product at most twice that. A residue subtraction adds an addition
and a remainder per candidate. Stage 1 separately costs at most
`2*Σ_{ℓ≤b₁, prime} ell(ℓ^floor(log_ℓ b₁))` modular multiplications and
two gcds including setup. Initial base/residue normalization is separate.

Enumeration is additional work: `primesBelow (b₂+1)` has the sieve cost
specified under Complexity plus linear readback/filter work. It stores an
`O(b₂)`-bit sieve and up to `π(b₂)` prime indices (each at most `b₂`),
including any retained filtered list. This is not constant-memory search.
The bound 4194304 caps enumeration, `L`, `G`, and trace size independently
of the modulus; arbitrary-size input arithmetic still depends on `n`.
Full traces add `O(L)` small indices and up to `ceil(L/32)+32` gcd values
of at most `bitLength(n)` bits. Benchmarks report trace-enabled overhead
separately; counters may replace retained batch detail only in an explicitly
selected trace-disabled mode with identical results and accounting.

The stage-2 reference implementation uses direct `Nat` multiplication
and remainder on every modulus size (GMP-backed for large naturals).
Stage 1 retains its existing word-Montgomery `powMod` dispatch. The 64-bit
track therefore compares their actual implementations, not the abstract
cost of equal modular operations. Label that backend difference in the
report; no claim that all-`Nat` is optimal on words follows from this choice.
A word-`MontCtx` stage-2 variant may be compared in adjacent paired runs
with setup and conversions included and the same residue/gcd semantics. Existing `MontCtx` is word-sized and must not be called an
arbitrary-precision modular context. A prepared big-integer context is not
assumed to exist. Before default enablement, apply the benchmark decision
below to direct `Nat`: if it passes the route-usefulness gate, retain it;
if it fails, leave defaults disabled. A prepared-context implementation may
then be evaluated, but must specify its representation, reduction equality,
one setup per modulus, entry/exit conversions, and storage first. Select it
only if the same paired benchmark passes with context setup and conversions
included in total time. No backend crossover or performance result is claimed
by this specification; those require implementation measurements.

#### Acceptance fixtures and measurements

These exact fixtures all use `a = 2`, `b₁ = 5`, `M = 60`, setup gcd 1,
and stage-1 gcd 1. For `b₂ = 13`, `Q = [7,11,13]`; the partial batch
is flushed at the endpoint. Orders are modulo the displayed prime factors.

| `n` | orders | `x` | `b₂` | terms in prime order | batch product mod `n` | result |
|---|---|---|---|---|---|---|
| `1081 = 23*47` | `11,23` | 216 | 13 | `486,299,11` | 736 | `factor 23` |
| `1081 = 23*47` | `11,23` | 216 | 7 | `486` | 486 | `noFactor` |
| `2047 = 23*89` | `11,11` | 32 | 13 | `3,0,1023` | 0 | `whole`; leaf gcds `1,2047,1` |
| `1219 = 23*53` | `11,52` | 998 | 13 | `969,989,954` | 0 | recovery returns 23; leaf gcds `1,23,53` (last not executed) |

Also require setup `search 1081 23 5 13 = factor 23`, stage-1 factor
`search 161 2 5 13 = factor 7`, and stage-1 whole
`search 15 2 5 13 = whole`, all without continuation. Conformance covers
invalid bases/moduli, raw nonunit residues, empty/reversed intervals, bounds
0 and 1, the primes dividing 210, prime endpoints, multiple giant blocks
and gaps, lengths 31/32/33/64, cap equality, exact attempt totals,
deterministic state, and budget skips. CI checks cap arithmetic and the
proved result equalities (also using early-exit inputs), not a full scan at
4194304; endpoint-scale performance runs belong to the manual benchmark
suite. Test the recovery helper separately
on a synthetic buffer with a whole leaf before a proper leaf (for example
terms `[0,23]` modulo 1081); this is not claimed to arise from the prime
sequence of a valid continuation.
Cross-check candidate terms against independent modular powers; this slow
oracle is for tests, not the executable route. Check the fixture orders by
minimality, not just by a single power returning 1.

The route benchmark family fixes `b₁ = 64`, base 2, and the following
extra primes and factors, with `b₂ = q` and a second track `b₂ = 2*q`:

| `q` | prime `p = k*q+1` | `k` |
|---|---|---|
| 67 | 4175126843 | 62315326 |
| 127 | 1245980999 | 9810874 |
| 257 | 2889804119 | 11244374 |
| 509 | 4034518259 | 7926362 |
| 1021 | 1984454399 | 1943638 |
| 2039 | 3821489723 | 1874198 |
| 4093 | 1266840803 | 309514 |
| 8191 | 2407646159 | 293938 |
| 16381 | 3346015823 | 204262 |
| 32749 | 3530931683 | 107818 |

Each row has `k ∣ M = lcm(1..64)`, `2^M mod p ≠ 1`, and
`2^(M*q) mod p = 1`, so `ord_p(2)/gcd(ord_p(2),M) = q`.
Choose and commit distinct prime cofactors `r`
giving total sizes 64, 128, 256, and 512 bits, with stage-1 gcd 1 and
`ord_r(2) ∤ M*s` for every interval prime `s`; publish factor/order
witnesses and reject unsuitable fixtures during preparation, outside timing.
These factors exceed the trial-division table. Integration measurements
must additionally show from events that the continuation actually executes;
successes entirely due to preceding rho are not stage-2 usefulness evidence.
The same prepared family with `b₂ = q-1`, for `q ≥ 127`, provides
full-scan misses. The empty interval at `q = 67, b₂ = 66` is a separate
early-exit control and carries no scaling evidence; add fixed whole/recovery
controls from the table above.

Ordinary factorization runs rho before p−1, so the small-factor table alone
cannot justify its dispatch. Its integration arm instead uses the following
larger factors at total sizes 128, 256, and 512 bits, with the same cofactor
conditions and the actual policy bounds `(64,4096)`: rows with `q ≤ 4093`
are opportunities, and the last three rows are full-scan miss controls.
Construction and
primitive measurements retain the smaller table. All five fixed seeds
`[0,1,2,3,4]` participate, including trials where rho succeeds first; only
trials whose events show stage 2 executing can establish its usefulness.
Do not infer route participation from factor size alone. If no trial reaches
it, the integration evidence is inconclusive and defaults remain disabled.

| `q` | prime `p = k*q+1` | `k` | primality witness `w` |
|---|---|---|---|
| 67 | 640593315381498719 | 9561094259425354 | 14 |
| 127 | 989082332266914563 | 7788049860369406 | 5 |
| 257 | 109241628152434139 | 425064700982234 | 2 |
| 509 | 152168461520334179 | 298955720079242 | 2 |
| 1021 | 525357598587673739 | 514552006452178 | 2 |
| 2039 | 73929628837078823 | 36257787561098 | 5 |
| 4093 | 100085828142782543 | 24452926494694 | 5 |
| 8191 | 277827051595988963 | 33918575460382 | 2 |
| 16381 | 369205211213026103 | 22538624700142 | 5 |
| 32749 | 738117420304950359 | 22538624700142 | 7 |

Here again `k ∣ M`, `2^M mod p ≠ 1`, and `2^(M*q) mod p = 1`.
The additional witness satisfies `w^(p-1) mod p = 1` and
`gcd(w^((p-1)/ℓ)-1,p) = 1` for every prime `ℓ ∣ p-1`. The complete
factorization of `p-1` is obtained by trial-dividing `k` by the primes at
most 64 and adjoining `q`; the full-order criterion therefore verifies
primality without a probable-prime assumption. Retain these witnesses in
the committed implementation fixtures. The ordinary-policy miss controls
must run the actual `(64,4096)` allocation, not the varying standalone bounds.

Register separate measurements for (1) setup: normalization, base gcd,
enumeration for both stages, and any modular-context construction;
(2) stage-1 exponentiation and final gcd
on prepared primes/context; (3) stage-2 babies, giants, products, and gcds
from a saved stage-1 residue and prepared interval; (4) total standalone
stage 1 plus continuation, including all setup. Also measure continuation
including its interval enumeration to expose the actual adapter cost.
Do not bill stage-1 exponentiation twice or omit setup from total time.
Record executed bounds, outcome, attempts, operation counts, peak storage,
trace mode, and all timings. Use the full-scan miss track for the
`D + 2*ell(i₀) + G + 2*L` modular-operation upper-bound model at fixed
modulus size, retaining the fixed baby-table cost. Use the nonempty rungs
`q ≥ 2039` for the scaling fit; smaller rungs measure setup amortization.
For the reference binary-power schedule, also record the exact power cost
(the bit/popcount count, zero at `i₀ = 0`) so the expected timing model
tracks executed operations rather than fitting an asymptotic bound alone;
measure enumeration separately under the sieve model. Compare varying
modulus sizes as fixed operand-size tracks, not as unit-cost arithmetic.

Use native Mathlib-free bench drivers and also the interpreted construction
path for `primality?`. Follow the shared-host policy and fixed trial-major
schedule in [benchmarking](../../SPEC/benchmarking.md). Compare enabled
and disabled policies in eight adjacent blocks alternating AB/BA, retaining
all samples and allowing at most one unchanged inconclusive rerun. A consumer
passes the usefulness gate if the enabled policy either completes a checked
factorization/certificate that the disabled policy exhausts on, or has median
total time at most 0.90 of disabled on the successful extra-prime family;
on the full-scan misses and existing balanced/smooth/table regression
families its median total time must be at most 1.10 of disabled. Compare at
equal seeds and existing rho/ECM work caps, equal factor-worklist fuel and
per-cofactor smooth caps for ordinary factorization, and equal global
`maxAttempts` for construction. Report success counts separately from timing,
and never time an exhaustion as a successful result. Across all required families, the enabled policy
must retain every checked success of the disabled policy. Ordinary
factorization and construction pass independently; #10291's four inputs are
an additional fixed corpus, not evidence of an extra-prime base order or a promised success family.

The internal comparator is the identical bounded policy with continuation
disabled. An external p−1 comparator is optional and **informational**, never a
Phase-4 gate; if added, pin its version, base, both stage bounds, and one
persistent subprocess protocol, and record
protocol overhead under the repository comparator rules. A default-bound
`factor` subprocess is not a stage-2 comparison. These registrations extend
the existing bench/conformance targets and single CI job, never a new job
or matrix. The fixtures above are SPEC evidence; benchmarks and default
enablement are implementation acceptance gates, not completed measurements.
The new families become required Phase-4 evidence when primality milestone 6
or int-factor milestone 8 exposes the corresponding implementation. At that
point add their `phase4.input_families` entries in `libraries.yml` and
revalidate the affected performance surface before claiming it complete.
The existing `done_through` attestations concern the implemented stage-1
surface; this SPEC-only extension does not attest stage 2 or invalidate
those measurements.

#### Certificate-search allocation

Add `pMinusOneStage2 : Bool := false` to `FactorSearchBudget`.
`ConstructionBudget` carries it through its existing `factor` field;
do not add a second flag with competing precedence. The tactic option
`primality? (pMinusOneStage2 := true)` sets that nested field for explicit
bounded experiments. The ordinary `primality`/`primeCert?`
core keeps its one base-2/bound-64 stage-1 call and no continuation.
For construction, after each configured stage-1 call returning a residue,
the enabled policy tries at most one continuation with
`b₂ = 8*b₁` only when `b₁ ≤ 4096`, before advancing to the next
base/bound pair. This construction policy caps stage 2 at 32768, independently
of the primitive ceiling; the default two-base ladder can execute at most
six continuations per worklist entry. Skip larger stage-1 bounds, `b₂ ≤ b₁`,
or a depleted total attempt allocation. No batch is charged as a separate
attempt: the interval cap supplies the per-attempt work bound. `factor`
splits as usual;
`noFactor` and `whole` both advance to the next pair, then bounded rho,
then retain an unresolved residual. There is no retry inside a continuation.
Charge each continuation immediately against the same global `maxAttempts`
as stage 1, rho, recursive construction, and witness candidates. Zero
remaining attempts performs no stage arithmetic, sieve, or random draw.

The factor-result boundary gains `events : List FactorEvent`, retained
in construction diagnostics on both success and exhaustion. Define this
Mathlib-free upstream diagnostic type with a `pMinusOne` case containing
the shared `PMinusOne.Event`, and a `route` case containing a route name
and a list of string key/value fields. The latter carries downstream
diagnostics without an upstream dependency on downstream types. The
HexIntFactor adapter serializes every ECM event as route `ecm`, with fields
`subject`, `sigma`, requested/effective bound, `outcome` (`noFactor`,
`factor`, or `whole`), `factor` when present, and `attempts = 1`. Preserve
event order and p−1 skip reasons; do not drop ECM events. These fields
are diagnostics only; counted results remain the accounting source. When
implementing these budget and result extensions, advance `SearchExtension`
ABI from 2 to 3 and update registrations together; reject incompatible registrations before execution.
A producer unable to honor a requested policy or total attempt limit declines
without work, retaining the input residual and state. The current downstream
adapter's refusal of a total-limit construction allocation remains valid.
Default construction enablement is false until its independent usefulness
gate passes in a reviewed report. Passing the ordinary factorization gate
does not turn it on. Only dynamically validated proper divisors enter
assembly, and the existing certificate checker remains the final authority.

### Taking up downstream factoring advances

hex-int-factor's stronger factorization reaches, or is intended to reach, this
library's search without inverting the proof dependency through two current
routes and one deferred extension:

1. **Certificate hand-off** (works today). `PrimeCert` is plain data
   and `checkPrime` accepts a certificate from any producer, so a
   caller that factors `n - 1` better than `partialFactor` assembles
   the node itself and lets the checker decide. hex-int-factor needs
   exactly this to prove its own certificate's factors prime.
2. **Shared factor-search primitives sit here.** `rhoFactor?` and Pollard
   `p − 1` stages 1 and 2 live beside each other, under the same dynamically
   validated proper-factor contract and counted/resumable boundary. Both
   libraries consume stage 1, and the fixed base-2/bound-64 call widens
   `partialFactor`'s reach cheaply. Its public smoothness request is capped by
   `smoothBound B = min B 524288`, independently of the committed table;
   ordinary certificate search still requests bound 64; `pMinusOneStage1_bound`
   identifies every larger request with that capped call. ECM stays downstream;
   curve arithmetic is a real dependency, not a shared primitive.
   The stage-2 contract above defines the separate interval ceiling, residue
   reuse, counted continuation, and benchmark-gated construction policy.
3. **The optional search hook.** `primeCertWith?` and its counted internal
   form parameterize certificate construction by `FactorSearch`; `primeCert?`
   still selects `defaultFactorSearch` and stays on the original route.
   `Hex.PrimalityTactic.SearchExtension` currently uses ABI version 2;
   stage-2 budget/trace integration advances it to version 3 as specified
   above. A downstream
   registration names an ordinary compiled `FactorSearch` declaration; the
   elaborator checks the registration type, ABI version, declaration presence,
   and factor-declaration type before evaluation. Names are tried in the fixed
   `searchExtensionNames` order, only after core exhaustion, resuming from the
   core failure's `Rand`. Each route receives the same recursive,
   partial-factor, witness, and rho allocations through `FactorSearchBudget`,
   and an exhausted diagnostic sums every route's semantic attempts. Importing
   `HexIntFactor.Primality` registers `Hex.Nat.intFactorSearch` without making
   hex-primality depend on hex-int-factor.

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

/-- Final verified sieve bitset, indexed by `numOfIndex`. -/
def primeBits : Nat

/-- Compiled binary-search implementation. -/
def tableSearch (n : Nat) : Bool

/-- Kernel bit lookup, with an equal compiled binary-search implementation. -/
def isTablePrime (n : Nat) : Bool

theorem primeTable_sorted : primeTable.toList.Pairwise (· < ·)
theorem mem_primeTable_prime {n : Nat} (h : n ∈ primeTable) : Hex.Nat.Prime n
theorem mem_primeTable_of_prime {n : Nat} (hp : Hex.Nat.Prime n)
    (hlt : n < primeTableBound) : n ∈ primeTable
theorem isTablePrime_iff {n : Nat} : isTablePrime n = true ↔ n ∈ primeTable
```

Kernel reduction of `isTablePrime` reads the corresponding bit of the
committed, verified final sieve state, including the exceptional primes 2
and 3 and a check that the input is represented at that index. This avoids
forcing the array's list representation when checking small certificate
leaves. An equality proved for all inputs supplies a
`@[csimp]` replacement with the existing binary search at runtime. The
committed prime table and sieve bound remain unchanged; exposing the final
state requires no new generated table or primality assumption.

The adjacent old/new replay evidence is
`reports/bench-results/hex-primality-table-replay-issue-10268.json`, reproduced
by `scripts/bench/primality_table_replay.py --output /tmp/table-replay.json`.
One old lookup costs about as much as the complete multi-leaf check in these
samples, consistent with shared array reduction within one kernel replay;
the evidence does not multiply that cost by the number of leaves. The new
lookup alone is indistinguishable from fresh-build overhead at this scale.

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

The mask depth is `max 32 (width.log2 + 1)`, so the masks cover the
requested width without a fixed enumeration ceiling. The round count remains
32 at the required 524288 endpoint; the generalization supplies an unrestricted
correctness theorem, rather than accelerating this endpoint. `sieve_prime_iff`
requires only `hsqrt`, `ht`, and `hrange`; `sieve_testBit_iff` retains the
original signature for existing callers. The first 32 rounds remain the
minimum, preserving table replay at its existing bound.

`primesBelow bound` runs that sieve with `bound.sqrt + 1`, reads it back,
and adds the exceptional primes `2` and `3` when they are below the bound.
Its public contract is:

```lean
n ∈ primesBelow bound ↔ n < bound ∧ Hex.Nat.Prime n
```

`primesBelow_pairwise_lt` and `primesBelow_nodup` give strict ascending order
and uniqueness. This compiled runtime API is independent of `primeTable`.
Pollard p-minus-one and ECM enumerate `primesBelow (effectiveBound + 1)`,
so every prime up to the effective bound participates in stage one. The
primitive cap is 524288; ordinary search retains its existing 9999 ladder
cap. Generated lists are never embedded as proof evidence. `primesIn`
keeps its current implementation pending comparative segment measurements.

Compiled `bitsToList` readback processes 64 candidate bits per extracted
word. The structural one-bit scan remains its specification, with a
`@[csimp]` equality proved for every bitset, starting index, and count. This
reduces large-integer shifts from one per candidate to one per 64 candidates;
it preserves the exact list and its order. Pollard p-minus-one and ECM retain
the same coverage and deterministic attempt schedules. The sieve itself is
unchanged by this readback optimization. The interpreted `#eval` comparison
in `reports/bench-results/hex-primality-readback-issue-10268.json`, reproduced
by `scripts/bench/primality_readback.py --output /tmp/readback.json`, measures
the regime used by `primality?`; it is not a native-executable benchmark.

The table is a consequence of one sieve run, but not one monolithic
reduction. A Mathlib-free elaborator computes the bitset with a compiled
twin, emits equations for fixed-size batches of sieve steps, kernel-checks
each equation by reduction, and chains the equations to the final literal.
This is PrimeCert's `run_sieve` architecture and is required here: a
single enormous `decide +kernel` expression is not the scaling claim.

**`primeTableBound = 10^5` is the accepted measured policy.** The controlled
fresh-module sweep runs the standard generator at `10^4`, `10^5`, `10^6`, and
`10^7`, retaining generation/replay time, source/olean/generated-C size, and
native compile-and-readback results. The `10^5` replay is comfortably inside the
"few minutes on the benchmark machine" budget that
[hex-conway](../../HexConway/SPEC/hex-conway.md) sets for its committed table.
Its 9,592-entry literal does make generated `leanc` warn that the static
object-size metadata field truncates, but a standalone program containing that
literal is explicitly code-generated, linked, and executed; it reads back the
full length, endpoints, and checksum. That warning is therefore recorded as
metadata overflow but not treated as a failed representation constraint. At
`10^6` fresh replay exhausts the default heartbeat budget, and `10^7`
generation exceeds the five-minute command budget. Thus `10^5` is the largest
candidate satisfying the stated fresh-build budget. The raw samples,
environment provenance, and exact reproduction command are in
`reports/bench-results/hex-primality-table-issue-9757-chungus2.json` and
`scripts/bench/primality_table_sweep.py`. The standard committed-table
regeneration check is `python3 scripts/bench/check_prime_table.py`; CI runs the
same command after building the Hex libraries.

`hotPathCandidates` in hex-berlekamp-zassenhaus is a proof-carrying view of
`primeTable` restricted to `[3, 500]`. Its entries are `ZMod64.Prime` values:
each bundles the modulus, a `ZMod64.Bounds` instance, and a `Hex.Nat.Prime`
proof. Its soundness and coverage theorems are corollaries of the table's two
membership directions, while sortedness preserves the deterministic ascending
order and tie-breaking policy. The dependency is recorded explicitly in both
`libraries.yml` and the released repository pins.

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
  rejectedCandidates : Nat
  certAttempts       : Nat
  rand               : Rand

def defaultPrimeFuel (n : Nat) : Nat

structure PrimeCertBudget where
  rhoRestarts : Nat
  rhoSteps    : Nat

def defaultPrimeCertBudget : PrimeCertBudget

structure Internal.PrimeCertSuccess (n : Nat) where
  cert     : CheckedPrimeCert n
  attempts : Nat
  rand     : Rand

def Internal.primeCertCounted? (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (Internal.PrimeCertSuccess n)

def Internal.primeCertCountedWith? (budget : PrimeCertBudget)
    (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (Internal.PrimeCertSuccess n)

def Internal.primeCertCountedUsing? (factor : FactorSearch)
    (budget : PrimeCertBudget) (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (Internal.PrimeCertSuccess n)

def primeCertWith? (factor : FactorSearch) (n : Nat) (r : Rand) (fuel : Nat) :
    Except PrimeCertFailure (CheckedPrimeCert n × Rand)

theorem primeCertWith?_composite {factor n r fuel f}
    (hresult : primeCertWith? factor n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n

theorem Internal.primeCertCountedWith?_composite {budget n r fuel f}
    (hresult : Internal.primeCertCountedWith? budget n r fuel = .error f)
    (hstop : f.stop = .composite) : ¬ Prime n

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

`isPrime?` dispatches: table lookup below `primeTableBound`; a Miller--Rabin
composite filter; exact trial division below the accepted
`isPrimeTrialThreshold = 6·10^6`; then `primeCert?`. Fixed-shape primes cross
earlier, so the policy is set by Cunningham-chain primes: the MR-plus-trial arm
wins at the measured `5,011,967` rung, while the bounded certificate arm wins
at `6,007,559`. The accepted threshold is the round boundary between those two
rungs. Balanced semiprimes are rejected by the shared Miller--Rabin filter at
roughly the same cost on both arms, rather than being sent through full trial
division up to the prime-case crossover.
A failed base returns a certified `false`, an
accepted certificate returns `true`, and an exhausted certificate search
returns `.error` rather than falling into an unbounded computation. The
indexed success prevents a certificate for one number from answering a
request about another.

Certificate fuel bounds construction depth after the fixed deterministic
front end, not the front end itself. At every recursive `primeCert?` invocation,
the size check, complete table lookup, and fixed Miller--Rabin base scan run
before fuel is inspected; these tiers consume no attempts and leave `Rand`
unchanged. Therefore a table prime can return its small certificate at fuel
zero, and a composite proved by size, table completeness, or a Miller--Rabin
witness returns `.composite` at every fuel. Only a candidate at or above
`primeTableBound` that passes every fixed base needs construction fuel: zero
returns `.exhausted` without starting factorization, while a positive fuel
begins one certificate node and passes its predecessor to every child. A table
child can consequently close when that predecessor is zero, whereas a child
that itself needs construction exhausts. Thus the fuel bounds the number of
constructed certificate nodes along any root-to-leaf path; it neither counts
deterministic verdict work nor bounds the randomized attempt total within a
node.

**`defaultPrimeFuel n = n.log2 + 1` is the settled depth policy.** This gives
one construction unit per input bit. For an odd subject above the table, the
partial-factor product invariant makes every positive-exponent child a factor
of `n - 1`. A child that reaches construction is odd and therefore has a
complementary factor of at least two, so its bit length is strictly smaller.
The complete table closes inputs below 17 bits without construction; the
structural maximum is consequently at most the input bit length minus 16.
The settled policy retains those 16 spare units while removing the former
unexplained factor-of-two and additive margin. This is only a recursion-depth
bound: partial factorization and witness search remain separately bounded and
may honestly exhaust, so no certificate-search completeness is claimed.

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
counts and advanced state. The units are separate: `rejectedCandidates`
counts only candidates conclusively proved composite, while `certAttempts`
counts certificate-search attempts consumed by the candidate
whose decision exhausted. An undecided candidate is not included in
`rejectedCandidates`. If the candidate window itself is exhausted,
`certAttempts` is zero. In either case `rand` is the exact state after all
reported search work, so a caller can replay or resume without losing work.
Deterministic p−1 calls contribute to `certAttempts` but leave `rand` unchanged;
table lookup, trial division, and Miller--Rabin filtering contribute to
neither. In particular, every conclusively rejected candidate leaves both this
count and `rand` unchanged. A failure with
`rejectedCandidates = fuel` exhausted the whole candidate window. Otherwise
the undecided candidate is `n + 1 + rejectedCandidates`, so the two failure
modes and the resumption point are recoverable from the call and its failure.
The theorem records that a success is the *least* such prime.

`primeCert?` distinguishes `PrimeCertStop.composite`, justified by the size
check, table completeness, or a failed Miller-Rabin base, from `.exhausted`,
which makes no primality claim. Exhaustion is reachable: the certificate search needs `n - 1`
factored past a square root (or a cube root), and there are `n` for
which that is out of reach. `PrimeCertFailure` retains the advanced state and
exact attempt count because `partialFactor` runs Pollard p−1 and rho.
`Internal.primeCertCounted?` also exposes that count on success, while
`primeCert?` is its compatibility projection. Certificate metering counts
every p−1 call, rho restart, and tried witness candidate, including successful
ones, throughout recursive child construction. A p−1 call changes the count
but not `rand`; table lookup, trial division, Miller--Rabin filtering, and
checker replay are not search attempts. Earlier
successful child and witness searches are accumulated before a later failure,
and both entry points return the same advanced state without duplicate work.
Rho coordinates and certificate witness bases use the same 64-try
`Rand.nat` route over their full arbitrary-precision intervals. Rejected
sampler candidates consume words and advance the returned state, but remain
inside one counted rho restart or witness candidate. Exhausting that sampler
counts the semantic attempt already under construction and continues the next
candidate or restart from the sampler's exact advanced state. Exhausting that
outer allocation returns `.exhausted` with the final state. The failure
propagates rather than being papered over, which is design principle 8's third
remedy again.

`Internal.primeCertCountedUsing?` applies the same assembly and final
`checkPrime` acceptance to any `FactorSearch`. The producer's factor claims,
attempt count, and returned state are data, not evidence; malformed factors can
only turn a possible success into `.exhausted`. A producer is required to honor
the supplied `FactorSearchBudget`; the built-in and registered producers do so,
while termination of an arbitrary caller-supplied function is intentionally
outside the theorem boundary. `primeCertWith?_composite` retains the default
API's verdict theorem because only the fixed size, complete table, and
Miller--Rabin tiers can emit `.composite`.

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
`Rand.ofSeed n`; the lower `primeCert?` API remains explicitly seeded.

After the fixed core route exhausts, the elaborator looks up registered search
extensions in deterministic order and resumes each from the preceding route's
advanced `Rand`. It never runs an extension after core success or a core
`.composite` verdict. The concrete regression witness is the 81-bit prime
`1208925821721293454442757 = 4 * 549755814367^2 + 1`: the core tactic
allocation exhausts after 8 semantic attempts, while the registered
HexIntFactor producer recognizes the squared factor and finishes a certificate.
`lake build HexIntFactor.PrimalityConformance` is the untimed proof and
accounting reproduction; it also pins the resumed states and extension
subtotal and the unchanged composite diagnostic. The 512-bit registered-route
exhaustion case is pinned separately by
`HexIntFactor.ProofProbe.PrimalityExhausted` in
`lake build HexPrimalityElabProbe`: both routes finish bounded work and report
33 accumulated attempts. Modules without the downstream registration execute
exactly the same core call as before.

**The supported positive-certificate elaboration policy is at most 512 input
bits, at most 512 recursive certificate-search fuel, at most 2 Brent restarts
per partial-factor worklist entry, and at most 32768 Brent cycle steps per
restart.** Every elaboration-time certificate route uses
`primalityFuel n = min (defaultPrimeFuel n) primalityFuelBudget`, where
`primalityFuelBudget` is definitionally the 512-bit input ceiling. At the exact
boundary the default contributes 512. The recursive fuel bounds
certificate-construction depth. Partial factorization is bounded separately by
`2 * n.log2 + 8` worklist
steps at each certificate node and the rho restart/cycle allocation above. The
fixed witness budget remains 32 candidates per factor entry; the registered
HexIntFactor producer additionally admits at most eight p−1/ECM attempts within
each supplied worklist step. The exact attempt counter includes p−1 calls, rho
restarts, ECM curves, and witness candidates and can therefore exceed the
recursive fuel used at a node. Inputs above 512 bits are rejected before
Miller--Rabin or certificate search. Search exhaustion reports the seed,
selected recursive and root factor fuel, exact attempt count, and explicit rho
maxima, and says that no total decision was attempted.

The ceiling is the largest rung with both compiled and kernel evidence. The
exact-boundary prime `100297^22 * 2^146 + 1`, namely
`9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177`, is 512 bits. Its table factors alone do not meet the
Pocklington threshold: the accepted core and companion routes use bounded rho
work to discover the above-table factor `100297`, finish after 34 counted
attempts, reify its recursive certificate, and replay it in the kernel. The
same prepared certificate is checked by `HexPrimalityKernelProbe` and the
native `runDecision`, `runCertSearch`, and `runChecker` families. The paired
fresh-module sweep also exercises the non-smooth 512-bit probable-prime input
`11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123`,
which reaches bounded rho work in a recursive child and exhausts after 10
attempts at fuel 512, and the 513-bit value `2^512`, which is rejected before
search. The core route has a 10-second absolute fresh-module wall-clock budget
on the designated benchmark host; the companion route is gated identically
under its own SPEC. The harness compares the
largest raw candidate wall time in every substantive sample set against that
budget and makes any failure invalidate `release_quality`; it does not use the
reference-subtracted tactic delta for this contract. This single end-to-end
budget includes Lake startup and build-graph traversal, importing, compiled
search, compiled self-check, reification, and kernel replay. Rejection and
exhaustion may be indistinguishable from their import-only controls, but their
absolute wall times remain budget-gated.
The paired null controls remain in the record to classify those deltas; their
spread is not a release gate for this absolute-only contract. Per-arm CPU and
SMT-sibling interference checks remain hard gates for every accepted sample.
The refreshed raw paired samples for the settled fuel policy and their host
provenance are committed at
`reports/bench-results/hex-primality-fuel-elab-issue-9784-chungus2.json`.
The earlier ceiling-selection record remains at
`reports/bench-results/hex-primality-elaborator-policy-issue-9779-chungus2.json`;
the refreshed record supersedes its timings for the current fuel policy.
They reproduce with:

```bash
cpu=$(python3 scripts/bench/idle_core.py)
taskset -c "$cpu" python3 scripts/bench/primality_elab_sweep.py --samples 6 \
  --shared-host --cpu "$cpu" --timeout 30 --warm-timeout 600 \
  --output reports/bench-results/hex-primality-fuel-elab-issue-9784-chungus2.json
```

`lake build HexPrimalityElabProbe` is the untimed build-only reproduction.
`primality` first calls `primeCertCountedWith?` with the explicit allocation
above, then calls `primeCertCountedUsing?` once per registered extension only
after exhaustion. It never calls the total `isPrime`, whose exact trial
fallback is intentionally unbounded.

The companion consumes this positive-certificate policy without widening it.
Its `Nat.Prime` registration and precedence rules, negative factor-search
budget, decline behavior, and bridge proof-performance evidence are normative
only in the
[hex-primality-mathlib SPEC](../../HexPrimalityMathlib/SPEC/hex-primality-mathlib.md#natprime-elaboration-routes).

## Kernel exposure

The replay closure is `checkPrime` and what it calls: a kernel-facing
modular exponentiation, `Nat.gcd`, `Nat.mod`, and the table's verified
sieve-bit lookup (binary search remains its compiled implementation).
`Nat.sqrt` is deliberately absent: it is well-founded recursion
and does not kernel-reduce, which is why the square bound is checked as
`n < F * F` and the cube-root discriminant through the stored witness.

**The hex-arith amendment that creates that closure** is the largest
prerequisite in this SPEC, and it is landed. `HexArith.powMod`
branches on whether the modulus fits a `UInt64` and whether it is odd,
taking a Montgomery path in the good case, so the kernel is sent down
the `Nat` route instead:

- `HexArith.powModNat` and its raw `Nat.rec`/`Bool.rec` workers are
  exposed. Fixed windows of six bits through `2^64`, four bits through
  `2^512`, three bits through `2^1024`, and two bits through `2^2048`
  reduce kernel work. Larger moduli use
  narrower windows for small reduced bases or binary square-and-multiply.
  The exact algorithm and intermediate-size
  bounds belong to the hex-arith SPEC;
- `powModNat_eq` is exported (with `0 < p`), alongside
  `powModNat_modulus_zero`;
- `powModNat` guards `p = 0` to `0`, matching `powMod`, which is what
  makes the `@[csimp]` equality `powModNat_eq_powMod` unconditional:
  `powModNat` is the kernel-facing specification and `powMod` the
  runtime twin (principle 11's pattern; the earlier state had
  `powModNat a n 0 = a ^ n`, a full unreduced power).

`boundedPowMul` uses a checked shift for base `2`: for positive exponent `e`,
it compares `acc` with `bound >>> e` before returning `acc <<< e`. Other bases
use raw recursors. The kernel definition is proved equal to the compiled
structural loop at every input, including zero exponents, zero accumulators,
and oversized exponents. It retains the same early overflow rejection and
accepted results. Table lookup and the arithmetic checks use primitive Nat
comparisons. Subject ordering uses a direct list fold, and `checkPrime` uses
the certificate’s structural recursor instead of generated course-of-values
recursion. `checkWitnesses` shares a Fermat result only after that base passes;
a changed base starts a new group. Each public checker is a `noncomputable` kernel specification with a proved
`@[csimp]` rewrite to its compiled counterpart for every input. Compiled table lookup still uses
binary search. The internal `pockProduct` sentinel is proved equivalent to
`certProduct` for positive subjects; callers establish that precondition
before using it, and the final arithmetic check rejects the zero sentinel.
Both cube-root arithmetic arms use this bounded product and primitive order comparisons,
just as the square-root arm does. Their unconditional equality theorems retain
the original compiled arithmetic, including rejection on zero subjects,
overflowing exponents, invalid ordering, invalid interval witnesses, and sieve
bounds outside the cap. Optimizing replay must also check complete `primality?`
and native construction for regressions; a smaller kernel timer alone is insufficient.

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

`n` the input, `b = log₂ n` its bit length, `k` the number of factor
entries at one certificate node, and `K` the total number of factor entries
in the part of a certificate tree replayed before acceptance or rejection.
For stage 2, `i₀ = floor(Q.head/210)` and `ell` is binary bit length
(`ell(0) = 0`); the empty interval skips all residue-table work.

| operation | cost | note |
|---|---|---|
| `isTablePrime` | compiled: `O(log |primeTable|)` comparisons; kernel: a constant number of Nat operations on the input and fixed 33,333-bit state | binary search at runtime, verified bit lookup in the kernel |
| `isPrimeTrial` | `O(√n)` remainder tests | hex-arith, unchanged |
| `millerRabin` one base | `O(b)` modular multiplications | |
| `isProbablePrime` | `O(13 b)` | fixed base list |
| successful `isPrime?` | front end plus certificate search | bounded by explicit fuel after the fixed front end |
| `isPrime` worst case | `O(√n)` remainder tests | exact fallback after default search exhaustion |
| `checkPrime`, one Pocklington level | `O(k b)` modular multiplications; `O(k b)` bounded ordinary multiplications; `O(k)` subject comparisons, divisions, and gcds | canonical subject preflight is linear on accepted and rejected lists |
| `checkPrime`, full tree | `O(Σᵥ kᵥ bᵥ)` modular and bounded ordinary multiplications; `O(K)` subject comparisons, divisions, and gcds | `kᵥ`, `bᵥ` are the entry count and subject bit bound at each visited node; arithmetic preflight bounds each replayed child's subject below its parent, so the sum is `O(K b)` for root bit length `b` |
| `primeCert?` | dominated by `partialFactor` | bounded by recursive fuel, one base-2/bound-64 p−1 call per nontrivial partial search, per-node worklist fuel, and `defaultPrimeCertBudget` rho restarts/cycle steps |
| `primeCertWith? factor` | dominated by `factor` plus the same certificate assembly | one producer invocation per non-table certificate node with explicit recursive, worklist, and rho allocations; the producer must honor the allocation and supplies its remaining cost model |
| Pollard p−1 stage 2 | at most `210 + 2*ell(i₀) + G + 2*L` modular multiplications; `2 + ceil(L/32) + 32` gcds | `L` interval primes, `G` giant advances; residue, sieve, index, and trace storage are specified in the stage-2 contract; enumeration is additional |
| sieve to `N` | `O(√N · max(32, log N))` loop/doubling rounds | each marking round is a bit operation on an `N/3`-bit `Nat` |

These are operation counts, not bit complexity; subject comparisons,
divisions, gcds, and both kinds of multiplication operate on big integers,
so a bit-complexity model would have to price each primitive. In particular,
the canonical-order preflight removes the former quadratic number of subject
comparisons on any pairwise-distinct list that passed structural preflight,
whether it was accepted or rejected later; it does not claim that a comparison
of arbitrary-size `Nat` values has unit bit cost. The recursion
depth claim in an earlier draft -- that each `q` is "at most half the bit
length" of `n` -- was
wrong: `q` is at most about half the *value*, so the bit length drops
by roughly one per level, and the depth is `O(b)` rather than
`O(log b)`.

The one to watch is the sieve. The state is a single `Nat` of `N/3`
bits, so every marking step is a GMP `shiftLeft`, `lor`, and `land` on
a large integer rather than an array write. **Whether a compiled
`ByteArray` sieve would beat it is a benchmark hypothesis, not a
theorem** -- compiled `Nat` bit operations are big-integer operations
too. The bitset sieve supplies both kernel table verification and compiled
`primesBelow` enumeration. The latter adds `O(N)` index tests and list
construction to read back an initial segment. `primesIn` remains the
unrestricted trial-division range/filter route whose result is converted to an
`Array`; changing it requires a separate comparative measurement. The existing
segment family measures `primesIn`, while the runtime enumeration has a fixed
524289-bound target alongside table-verification and sieve-family evidence.

## Conformance

The stage-2 implementation must cover the exact residues, base orders,
setup/stage-1 exits, interval and batch boundaries, recovery, cap equalities,
and budget/state cases in
[its acceptance contract](#pollard-p-minus-one-stage-2). These are search
tests and proper-divisor theorems, not new certificate-checker assumptions.

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
  `n - 1`, duplicate factor subjects, and distinct subjects outside the
  canonical ascending order. The checker's negative cases matter as much as
  its positive ones and no oracle produces them, so these are constructed by
  hand.
- Segments `[1, 100]`, `[1, 10^4]`, and one segment straddling
  `primeTableBound`, checking the table and the fallback agree across
  the boundary.
- The 94 `hotPathCandidates` entries in the downstream
  `HexBerlekampZassenhaus` conformance target, checking that the table view has
  the same contents in the same order.

**Oracle choice.** PARI's `isprime`, `nextprime`, and `primes` through
cypari2 independently cover verdicts, next-prime results, and segments.
Certificate fixtures are replayed by a separate Python implementation of the
checker; PARI supplies every small-leaf primality verdict and independently
confirms the subject of every accepted certificate. The rejected certificates
are hand-constructed clause tests, so their independent evidence is agreement
with that replay rather than a PARI certificate format. python-flint's
`fmpz.is_prime` is a required second opinion on every primality verdict used by
the oracle, including certificate leaves. Both dependencies are already
installed by the CI dependency step.

sympy is installed by CI alongside `python-flint`, `cypari2`, and
`conway-polynomials` (an earlier draft of this SPEC said otherwise),
but PARI plus python-flint already cover the verdict surface and the
second opinion, so this SPEC uses that pair and adds no third
dependency.

**Mode: required.** The existing single-job oracle tail installs and preflights
PARI/cypari2 and python-flint, diffs fresh deterministic emission against the
committed snapshot, and fails if either the dependency or a comparison is
unavailable. The all-oracle local sweep may record a missing dependency as a
skip unless `HEX_REQUIRE_ORACLES=1` or `--require-oracles` selects this required
profile. Fixtures are limited to results the oracle can recompute from the
original input: verdicts, next-prime results, certificate-checker replay, and
prime segments.
Multiplicative-order laws, p−1 and Brent routes, exact search accounting and
bounded failures, sieve representation, total fallback, and the term/tactic
surface are covered by `HexPrimality.Conformance`; PARI cannot independently
establish those implementation-level properties, so emitting them would add
ceremony rather than independent evidence.

## Benchmarking

Pollard p−1 stage 2 adds the separate setup, stage-1, stage-2, total, and
adapter-continuation measurements defined in
[its acceptance contract](#pollard-p-minus-one-stage-2), including the
extra-prime order family and full-scan misses. Native measurements determine
the arithmetic choice; construction additionally measures the interpreted
path. Default enablement requires the consumer-specific usefulness gate.

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), with drivers at
`bench/HexPrimality/Bench.lean`. Both native and kernel suites, because
the kernel side is the point of the library.

Policy-selection evidence, retained as input to but not a claim about Phase 4:

- **Table verification**, the standard generator plus fresh emitted replay at
  `10^4`, `10^5`, `10^6`, and `10^7`. The controlled driver records every raw
  wall-time sample, source/olean/generated-C size, deterministic source hash,
  and native compile/readback result. The committed record is
  `reports/bench-results/hex-primality-table-issue-9757-chungus2.json`.
- **Decision dispatch**, counterbalanced warm native timings for the production
  Miller--Rabin-plus-trial arm and bounded certificate arm on fixed primes,
  Cunningham-chain primes, and balanced semiprimes from `10^5` through `10^7`.
  A deterministic independent 64-bit Miller–Rabin implementation checks both
  results before a sample is accepted. The committed raw record is
  `reports/bench-results/hex-primality-policy-issue-9757-chungus2.json`.
- **Certificate depth fuel**, ascending/descending warm native ladders over
  table-smooth primes at 31, 61, 123, and 256 bits; p-minus-one-friendly and
  recursively certified primes requiring depths two and three; the rho-backed
  512-bit boundary prime; and honest bounded exhaustion at 512 bits. The exact
  success thresholds are one, two, and three construction levels. Rungs above
  the threshold retain the same outcome and attempt count, while the selected
  one-unit-per-bit policy remains a conservative structural bound. Every
  successful probe results receive an untimed same-implementation
  `checkPrime` replay; exhaustion makes no primality claim.
  The runtime ceiling is the benchmark family's existing five seconds per
  native call, and the elaboration ceiling is ten seconds per fresh module.
  The native ladder uses an idle pinned core and retains host snapshots but has
  no interference rejection gate, so its outcome and attempt columns select
  the policy while its wall times are indicative. The paired fresh-module
  record enforces per-arm CPU and SMT-sibling interference gates.
  Raw counterbalanced samples and host provenance are in
  `reports/bench-results/hex-primality-fuel-issue-9784-chungus2.json`; the
  refreshed paired elaboration samples are in
  `reports/bench-results/hex-primality-fuel-elab-issue-9784-chungus2.json`.
  These records are inputs to the later Phase-4 report rather than a separate
  benchmark family to rerun.

  ```bash
  python3 scripts/bench/primality_fuel_sweep.py --rounds 6 --repeats 3 \
    --output reports/bench-results/hex-primality-fuel-issue-9784-chungus2.json
  cpu=$(python3 scripts/bench/idle_core.py)
  taskset -c "$cpu" python3 scripts/bench/primality_elab_sweep.py --samples 6 \
    --shared-host --cpu "$cpu" --timeout 30 --warm-timeout 600 \
    --output reports/bench-results/hex-primality-fuel-elab-issue-9784-chungus2.json
  ```

The Phase-4 evidence tracks are assigned below. Each advertised operation has
exactly one owner. The proof rows measure theorem elaboration and kernel
acceptance, not a second compiled timing of the executable checker or search.

| advertised operation or surface | evidence owner | controlled family |
|---|---|---|
| `millerRabin` | compiled `runMillerRabin` | committed table-smooth primes, 31--511 bits |
| `isProbablePrime` | compiled `runProbablePrime` | the same prime ladder, forcing all fixed bases |
| `isPrime?` | compiled `runDecision` plus fixed `runDecision512` | table-smooth ladder plus the exact rho-backed 512-bit boundary |
| total `isPrime` | compiled `runTotalDecision` | successful bounded-route ladder; the deliberately unbounded exhausted fallback is excluded |
| `primeCert?` | compiled `runCertSearch` plus fixed `runCertSearch512` | rho-free ladder plus the structurally distinct rho-backed boundary |
| `checkPrime` | compiled `runChecker` plus fixed `runChecker512` | prepared certificates sharing the exact emitted literals with the proof track |
| Pocklington-3 checker arm | fixed compiled `runPock3Checker` | the canonical 199 certificate |
| `sieve` plus `bitsToList` | compiled `runSieve` | bounds `10^3`--`3.2 * 10^4` |
| `isTablePrime` | compiled `runTableLookup` | batches of 4096--65536 fixed-table lookups |
| `orderOf` | compiled `runOrder` | committed primitive-root moduli 1009--32003 |
| `pMinusOneStage1Counted` | compiled `runPMinusOne` | smoothness bounds 64--8192 on a fixed 61-bit prime |
| `Internal.rhoFactorCounted?` | compiled `runRho` | balanced semiprimes with fixed seeds and least factors 100003--30000001, beyond the fixed gcd-batch floor |
| `primesIn` | compiled `runSegment` | initial segments `10^3`--`3.2 * 10^4` |
| `nextPrime?` | compiled `runNextPrime` | exact committed table-route gaps 4--64 |
| input elaboration, production-search attribution, and emitted certificate literal | matched fresh modules | 31, 61, 123, 256, 511, and 512 bits |
| `prime_of_checkPrimeAt` theorem instantiation and kernel replay | matched fresh modules | the same exact emitted certificates and allowed axiom set |
| Mathlib-free `primality` elaboration | matched fresh modules | the same size family, including the accepted 512-bit ceiling |
| `Construction.run` | fixed compiled `runConstruction` | Curve25519, mode 3 |
| `primesBelow` through the construction bound | fixed compiled `runRuntimePrimes` | bound 524289, mode 3 |
| emitted Curve25519 checker | fixed compiled `runCurveChecker` and adjacent fresh replay modules | pinned three-node literal and five-node reference |
| `primality?` input, search, literal, rendering, replay, and end-to-end costs | adjacent fresh modules | Curve25519 |

All six proof sizes use an import-only baseline, separate input, search,
literal, replay, and full-tactic modules. The external runner rotates the
thirty substantive pairs, alternates pair orientation, includes baseline,
123-bit, and 512-bit null controls, records source and artifact hashes plus
axiom sets, and enforces a 10-second absolute fresh-module budget. The
scientific modules are deliberately absent from the CI target; the existing
boundary, exhaustion, and over-budget modules remain the single-job build
smoke.

The six bit-size registrations from `runMillerRabin` through `runChecker` use
mode 2.  A tight family-specific model is unavailable because GMP changes
multiplication algorithms across this range and the certificate tree shrinks
by input-dependent amounts.  The published schoolbook bound is nevertheless
applicable: binary powering performs `O(b)` multiplications of `b`-bit
integers, each costing `O(b^2)`, hence `O(b^3)` per fixed number of witnesses
or certificate levels (Brent and Zimmermann, *Modern Computer Arithmetic*,
chapter 1).  The `table-smooth-certificates` ladder exercises the modular
powering and certificate phases, and the inclusive profile below attributes
the dominant cost to those paths.  Faster observations therefore mean
"within declared upper bound (observed faster)", never a two-sided
complexity match.  `runSieve`, `runTableLookup`, `runOrder`, `runPMinusOne`,
`runRho`, `runSegment`, and `runNextPrime` use mode 1 with the family-specific
derivations at their registrations.  The exact 512-bit rho-backed decision,
search, and replay plus the sole Pocklington-3 constructor use mode 3 fixed
budgets: their structurally distinct single boundary inputs do not admit an
honest one-parameter family.

**Comparators.** PARI `isprime` via cypari2 and FLINT `fmpz_is_prime`
via python-flint are **informational native comparators**. They return proven
primality decisions but do not produce Lean proof terms; the Hex construction
route produces and self-checks reusable certificate data. Their different
outputs and algorithms preclude a required speed ratio. PARI remains the
conformance oracle and FLINT its independent cross-check.

The native Hex comparator is the lake-built `hexprimality_policy_probe
construction N` executable. Input parsing, startup, and certificate formatting
are outside its timer. `#eval` search probes execute through Lean's interpreter
under the current library configuration and are labeled as tactic-search
observations, separately from native-executable timings. Full `primality?`
builds include that search regime, proof emission, and kernel checking.

The kernel comparator is **PrimeCert**, also informational. Fresh-module
measurements retain imports, literal elaboration, and kernel checking, with
adjacent baseline modules exposing overhead. The six existing bit-family
witnesses have supplied certificates in both systems. The construction cactus
adds Curve25519 and Curve448: Hex uses only certificates found by its declared
construction profile, while PrimeCert receives its committed certificates.
Missing certificates and timeouts remain unsolved, including when native
search returns exhaustion quickly. Native plots additionally contain
secp256k1 and NIST P-256, P-384, and P-521. These fixed, structured corpora do
not estimate a success rate on random primes.

The comparison rotates system and baseline/replay arm order and reports
absolute fresh replay times because the measured toolchain pins differ (Hex
used Lean 4.34.0-rc2; PrimeCert used Lean 4.33.0). All completed samples and explicit
process timeouts are retained. Source hashes, exact inputs, versions, host
context, and reproduction commands accompany the plots in the construction
report. Measurements remain shared-host information rather than a CI gate;
the earlier six-witness comparison remains in
`reports/hex-primality-performance.md`.

For kernel-only comparisons, `scripts/bench/primality_kernel_direct.py` times
`Lean.Kernel.check` after imports and elaboration. It recursively expands all
local proof dependencies, including auxiliary theorems emitted by
`decide +kernel`, and checks the complete body against its declared goal.
Imported library proofs remain dependencies. A negative control must be
rejected. The retained `hex-primality-direct-kernel-checked-issue-10268.json` uses
adjacent reversed systems and records every sample, source, and toolchain.
Its matched-input plot shows growth hidden by fresh-build overhead; cactus
rank is not a bit-length axis. Comparisons must identify the PrimeCert revision:
its fixed-window modular exponentiation changes the replay comparison materially.
The current [component attribution](../../reports/hex-primality-replay-attribution.md)
separates supplied-proof kernel replay, fresh-module elaboration, certificate
search/rendering, complete `Nat.Prime` tactics, and native construction. Match
factor subsets and witness bases before attributing an implementation difference;
common-base certificates can require fewer powers than individually selected bases.
All completed samples remain evidence, with adjacent alternating before/after
arms. Results describe the recorded shared host, not portable performance promises.

The fixed construction targets and the adjacent-arm Curve25519 phase and
replay measurements are recorded in
[the construction report](../../reports/hex-primality-construction.md).

## Reusable certificate construction

`primality?` is an explicit goal tactic using `Construction.run`, independently
of ordinary `primality` and its interactive budget. It supports the core
`Hex.Nat.Prime` predicate; the companion registers the same syntax for
`Nat.Prime` and emits its checker bridge. Closed transparent expressions such
as `2 ^ 255 - 19` remain the theorem's original subject.

The default `ConstructionBudget` has maximum input size 521 bits, recursion
depth 32, 1024 total semantic attempts across the entire construction,
1024 factor-worklist entries per node, Pollard p-minus-one bounds
`[64, 512, 4096, 32768, 262144, 524288]` at bases `[2, 3]`, two rho restarts
of 32768 steps, and no ECM bounds or curves. Witness search tries
`[2, 3, 5, 7, 11, 13, 17]` before at most 32 random candidates. It admits at
most 32 distinct factor candidates and examines at most 4096 subset masks.
`maxSieveBound = 64` permits at most 63 divisor exclusions per candidate.
The least admissible bound is computed with an integer square root during
construction and checked directly during replay.
`primality? (maxAttempts := 29)` overrides the total attempt limit; the
unadorned tactic uses 1024. The remaining allocation is passed to each factor
producer, recursive child, and witness search, so failed subset choices cannot
reset it. Inputs over the bit limit have a separate size diagnostic.
The 521-bit and 32-factor limits admit P-521 using the existing factoring
portfolio: its predecessor yields 25 candidates in 94 factor attempts, and
construction succeeds in 170 total attempts. Enumeration remains capped at
4096 subsets; when truncated, it includes the full factor mask. These limits
are a measured policy, not a completeness claim. The 522-bit boundary remains
rejected. Writing P-521 as `2 ^ 521 - 1` needs local
`maxRecDepth = 1024` and `exponentiation.threshold = 521` for Lean to normalize
the original goal; the numeral and certificate replay use default limits.
The fixed mode-3 targets `runP521Construction` and `runP521Checker`, exact
suggestion guard, per-target traces, and paired phase measurements are described
in [the standard-field report](../../reports/hex-primality-fields.md).

All limits are explicit; exhaustion reports the full profile and exact attempt
count. Table division, primality screening, and subset enumeration are bounded
work but are not semantic attempts. Every stage-one call, enabled stage-two
continuation, rho restart, and
witness candidate is counted, including work discarded by unsuccessful subset
choices. Deterministic work leaves `Rand` unchanged. Construction uses no
external factorizer and no total trial-division fallback.

The factor callback receives smooth bounds and bases through
`FactorSearchBudget`, along with worklist fuel, the nested prime allocation,
and `attemptLimit : Option Nat`. A producer that cannot honor a requested total
limit must decline without work; the registered HexIntFactor adapter does so.
Its ordinary calls have `attemptLimit = none`.
The ordinary callback and registered HexIntFactor adapter retain their
established schedules. The construction callback tries its declared smooth
ladder before rho at each composite worklist entry and retains unsplit parts
as the residual. The stage-2 contract adds an initially disabled continuation
policy and execution trace; it does not silently change these existing
defaults or their recorded attempt totals.

Construction first tries subsets of the cheap table-division factors. Only if
those certificates fail does it call the configured factor provider.
The first successful cheap certificate is used: search favors construction
latency over comparing it with certificates requiring further factoring.
The fallback receives the remaining attempt budget and advanced random state.
Previously tried subsets are skipped during that fallback. Before recursive certification, construction
validates canonical factor data and bounded products. It enumerates subsets
satisfying square-root or
cube-root arithmetic criteria and orders them by estimated recursive replay
cost. Each entry costs `(16 * childCost + 1) * (n.log2 + 1)`, and the
`m - 1` divisor exclusions each add one unit. This is a search heuristic,
not a measured cost guarantee. Table leaves cost zero construction nodes; children
whose table-factored predecessors already satisfy a criterion cost one;
remaining children receive a bit-size penalty. Estimates select search order
only. When a subset cap truncates enumeration, the full factor mask remains
among the candidates. Successful children are cached within a node's subset
loop; reusing one consumes no additional attempts or random draws. Failed
searches are not cached because their random state and remaining budget can
change. Each chosen subset is recursively certified and the exact assembled
certificate passes public `checkPrime` before emission. Invalid producer data
cannot establish a primality verdict.

The Curve25519 fixture uses three non-leaf nodes and eight factor entries,
including two cube-root nodes. Its search starts from `Rand.ofSeed n`, takes
29 semantic attempts and consumes no random draws. The Pollard boundary is
checked on `(74058212732561358302231226437062788676166966415465897661863160754340907
- 1) / (2 * 3 * 353 * 57467 * 253947789517)`: base two gives no factor at
262144 and returns 31757755568855353 at 524288.

Suggestions use Lean's core `TryThis` facility and share `reifyPrimeCert` with
ordinary proof emission. The replacement contains the complete certificate
literal and `prime_of_checkPrimeAt` (or its companion bridge), discharged by
`decide +kernel`. Applying it removes search from future builds while retaining
kernel replay. Exact `#guard_msgs` tests pin the complete Curve25519 output, a
P-521 output, a small renderer example, and construction exhaustion. Standalone literal replay
imports the checker-owning module only.

## Certificate language and extension policy

Keep `PrimeCert`, `checkPrime`, and `prime_of_checkPrimeAt` as the standalone
data boundary. The source language is Lean: closed certificate expressions,
ordinary named definitions, local `let` bindings, and explicitly invoked
producer functions or macros. `primality? using expression` evaluates such an
expression at type `PrimeCert`, validates its subject and `checkPrime`, and
renders the existing fully qualified constructor literal. It also works through
the companion's `Nat.Prime` handler. Plain `primality?` and its `maxAttempts`
form keep their construction policy and output. The `using` form does not run
that search and cannot be combined with `maxAttempts`.

This chooses an explicit producer interface over a second global method
registry. A producer can be supplied from another module without changing Hex;
Lean's existing macro registration supplies optional domain syntax. The
separate-module `CertificateProducer` conformance fixture demonstrates a
Fermat-number candidate producer and a positive-exponent syntax prototype.
Neither changes which data the checker accepts. The syntax prototype is an
example for downstream authors, not an additional supported Hex grammar.

### Comparison with PrimeCert

The language comparison is pinned to PrimeCert commit
[`0803c2f6bd289c09704c7d352bb8fcf770cbb9b2`](https://github.com/b-mehta/PrimeCert/tree/0803c2f6bd289c09704c7d352bb8fcf770cbb9b2),
on Lean 4.33.0. This comparison is distinct from the earlier algorithm survey
and performance pins above. Relevant sources are `Meta/PrimeCert.lean`,
`Meta/Pocklington.lean`, `Meta/Pocklington3.lean`, `Meta/SieveLookup.lean`,
`Pocklington.lean`, and `Pocklington3.lean`. Executable examples and the exact
comparison sources live under `scripts/bench/certificate_language/`.

`@[prime_cert key]` registers a syntax category and a metaprogram producing a
primality proof. A `PrimeDict` maps natural numbers to proof expressions, and
later steps can reuse those expressions. The final term is a composition of
method-specific theorems, not an interpreter invocation on a common data type.
Registration adds ergonomic composition **and** permits new mathematical
criteria when their proofs are supplied. The metaprogram's quoted result type
is not itself a trust guarantee: Lean's kernel must check the emitted term
against the requested theorem. A bad expression cannot prove primality, but
can fail late with a kernel application-type error. The retained malformed
Pocklington example exhibits that diagnostic.

| PrimeCert feature | Hex correspondence and limit |
|---|---|
| `small`, `sieve` | `small` uses Hex's proved table below 100000. PrimeCert's imported sieve cache reaches 1000000 and `run_sieve` can extend it. A larger sieve leaf is not the same Hex certificate; use a Pocklington subtree instead. |
| `pock` | `pock` stores each positive exponent minus one and a witness base per factor. PrimeCert's group uses one base and permits repeated factors and zero powers; Hex requires sorted, distinct subjects and positive powers. Normalize the factorization before constructing Hex data. |
| `pock3` | `pock3` and `pock3Sieve` use the same cofactor decomposition and divisor exclusions. Convert a successful nonresidue non-square witness to `w = floor(sqrt(r² - 8s))` during construction; the Hex checker checks the interval, not the square-root algorithm. |
| Divisor bounds | Hex deliberately caps `m` at 64 before its exclusion loop. PrimeCert's theorem has no corresponding cap. The prototype at 9223372036904058881 accepts `m = 65` there and rejects that data here, although `m = 4` already suffices for this number. |
| Pure power of two in the cube-root path | Hex accepts the 197 certificate with `F = 4`. The pinned PrimeCert `pock3` grammar requires a factor tail; its underlying `pocklington3_certK` accepts the same case with an empty odd-factor list. |
| Named intermediate primes | Lean definitions/lets name Hex data; PrimeCert's dictionary names facts by subject. Reification expands Hex data to a tree, while PrimeCert can reuse proof expressions. |
| New proved criterion | PrimeCert can register a theorem-producing method. Such a proof cannot be placed in the current proof-free Hex data. A new producer must translate it into existing data, or use a separately identified theorem API outside the data checker. |

These are correspondences between particular proof methods and witnesses, not
a proof that the certificate languages or their searches are complete. The
representative Curve25519 factorization translates in both directions; repeated
powers and intermediate names do not require new checker constructors. The
counterexamples above disprove a blanket claim of interchangeable syntax or
accepted witnesses. They do not show that either system cannot prove the
*primality statement* by another certificate. No existing arbitrary-method
PrimeCert proof is claimed to have a general efficient Hex translation.

Hex additionally provides inspectable, serializable proof-free data, explicit
canonical-order rejection, bounded products and divisor exclusions, per-factor
bases, native finite construction with resumable budgets, and a Mathlib-free
checker with a thin correspondence bridge. PrimeCert's registry does not by
itself supply those data contracts. Its proof-carrying `PrimePow` structure is
not a replacement for them.

### Alternatives and sharing

1. **Surface syntax over current data: selected through ordinary Lean.**
   The positive-exponent macro and named Curve25519 prototype reduce source
   repetition. `using` flattens them into portable data; no custom parser or
   elaborator becomes a replay dependency.
2. **An implicit producer registry: not selected.** It adds ordering, duplicate
   registration, import-dependent selection, ABI, and resource-accounting
   policy without adding accepted certificates. Explicit function selection
   supplies the needed extension point. Existing bounded factor callbacks and
   their versioned downstream registration keep their separate search role.
3. **A versioned step interpreter or DAG: deferred.** None of these examples
   needs a new criterion or shows unacceptable tree expansion. A DAG could
   matter for many parents sharing a large child: naming a value saves source
   but does not memoize `checkPrime`. Hex already offers `prime_of_pocklington`
   with separately proved child primes for proof-library sharing, outside the
   standalone raw-data route. A new interpreter would need checked reference
   bounds, acyclicity/order, subject consistency, and its own soundness proof.
   The current evidence does not justify that additional checker surface.
4. **Adopt PrimeCert directly: not selected.** Its theorem-producing language
   needs Mathlib/Qq and a different toolchain pin, returns proofs rather than
   standalone certificates, and moves acceptance to each method's theorem
   application. This can be useful in a Mathlib proof library, but cannot
   replace the required core data boundary. A companion-only producer remains
   possible if it emits current Hex data and its toolchain dependencies align.

### Trust, resources, and compatibility

The `using` term must elaborate at `PrimeCert` with no free variables or
unresolved metavariables. Imported compiled definitions need not expose their
bodies to the kernel: only their resulting constructor data is reified.
Compilation, evaluation, macros, producer code, and the preliminary compiled
check are all untrusted. The emitted proof applies `prime_of_checkPrimeAt` to
the *literal* and an equality slot; kernel reduction checks both the requested
subject and `checkPrime`. The companion only transports that result. It is
not possible for a registered producer to add an unchecked opcode, proof slot,
or alternative success predicate to the checker.

The existing 512-bit goal policy applies before producer evaluation. Arbitrary
user-selected computation is not covered by `ConstructionBudget`: a supplied
producer may be expensive or fail to terminate, just as other explicitly run
Lean metaprograms may. This interface guarantees validation of its result,
not bounded construction for third-party code. Checker rejection rules are
unchanged; neither malformed data nor duplicate/unsorted factors are silently
repaired. No end-to-end constant resource bound is asserted for arbitrary
certificate trees.

Current constructor names, fields, exponent encoding, acceptance, and literal
rendering are unchanged. Existing generated certificates require **no
migration**. Producer names and private macro grammars belong to their owning
modules; applying the suggestion removes those dependencies. If a future
criterion needs new data, introduce an explicitly versioned representation and
proved checker, retaining the old checker API or providing a mechanical,
acceptance-preserving conversion. Do not reinterpret old fields or accept
unknown step tags through extension registration.

The conformance suite pins exact suggestions for ordinary and supplied
Curve25519, repeated factors, the divisor sieve, and the Mathlib bridge. It
checks the renderer's output by elaborating it back to data and rendering it
again. Checker-only replay modules import neither producers nor tactic code.
Malformed subjects, composite children, duplicate factors, enormous exponents,
out-of-range sieve bounds, and open producer expressions remain rejected.
Source-size, native construction, fresh elaboration, and direct kernel replay
measurements are recorded in the
[certificate-language report](../../reports/hex-primality-language.md).

## The Mathlib layer

The Mathlib-facing layer has its own
[owned SPEC](../../HexPrimalityMathlib/SPEC/hex-primality-mathlib.md). That
document is normative for correspondence and segment transports, instance and
elaborator registration, the `Nat.Prime` tactic and `norm_num` routes, bridge
failure and resource semantics, and bridge conformance and proof-performance
evidence. It links back here for the Mathlib-free algorithms and their positive
certificate policy instead of restating them.

Any future Mathlib-side primality dependency belongs to that companion as an
accelerator over this checker. It cannot replace this Mathlib-free proof
boundary because the core consumers live below the companion.

## Milestones

0. **The hex-arith amendments.** The kernel-facing modular
   exponentiation with its exposed recursion, exported correctness
   theorem, and `@[csimp]` twin; `DecidablePred Hex.Nat.Prime`;
   `exists_prime_dvd` and `exists_prime_le_sqrt`. Everything below
   assumes these, and nothing below can be finished without them.

1. **The table and the sieve.** `sieve`, `sieve_testBit_iff` with its
   four hypotheses, the batched replay elaborator, `primeTable` with
   sortedness and both directions,
   `isTablePrime`, and `primesIn`; plus the downstream proof-carrying
   `hotPathCandidates` view and its dependency metadata. Independently useful,
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

5. **The companion.** The Mathlib-facing milestone is specified by the
   [owned companion SPEC](../../HexPrimalityMathlib/SPEC/hex-primality-mathlib.md).
   Begins after milestone 1.

6. **Shared Pollard p−1 continuation.** The saved-residue boundary, complete
   interval enumeration, 210-step layout, whole-batch recovery, proper-divisor
   and conditional success theorems, counted trace, and capped APIs above.
   Land the fixed conformance cases before adapter uptake. Default enablement
   additionally requires the arithmetic and per-consumer benchmark gates;
   this milestone is not established by existing stage-1 benchmarks.

## File organisation

```
HexPrimality/
  Sieve.lean        -- the kernel-reducible bitset sieve and its correctness
  SieveElab.lean    -- batched compiled generation and kernel replay
  Table.lean        -- primeTable, primeBits, tableSearch, isTablePrime, primesIn
  Order.lean        -- multiplicative order mod n, orderDvd, ord_dvd_pred
  MillerRabin.lean  -- millerRabin, isProbablePrime, the compositeness theorem
  PMinusOne.lean    -- shared stages 1 and 2, residue boundary, counted trace
  Cert.lean         -- PrimeCert, CheckedPrimeCert, checkPrime, soundness
  Cert3.lean        -- the cube-root variant
  Search.lean       -- p−1/rho partialFactor, primeCert?, isPrime?, nextPrime?
  Construction.lean -- opt-in finite construction and subset selection
  Elab.lean         -- primality and primality?
HexPrimality.lean
```

The companion's source, conformance, probe, and SPEC layout is owned by its
[file-organization section](../../HexPrimalityMathlib/SPEC/hex-primality-mathlib.md#file-organization).

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
  Pollard `p − 1` stage 1 has joined it here for the same two consumers
  (see "Taking up downstream factoring advances"), which sharpens the
  question rather than settling it.
