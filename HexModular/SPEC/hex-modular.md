# hex-modular (integer CRT, rational reconstruction, and the modulus supply)

Chinese remaindering over `Int`, rational reconstruction from a residue,
symmetric representatives, and the supply of moduli that the modular
algorithms elsewhere in the tree draw on. Mathlib-free. The companion
`hex-modular-mathlib` relates the executable operations to `ZMod`,
`Int.ModEq`, and `Rat`, and supplies the decidability instances that make
them usable from a Mathlib goal.

This SPEC is the first of three expanding the "Modular techniques" entry
in [future-work](../../SPEC/future-work.md). The other two are
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md), which holds the
multi-modular determinant, certified rank, and Dixon lifting, and
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md), which holds the modular gcd for
`ℤ[x]`. This library is what all three of them share.

Two claims in that entry need correcting, and both are corrected below.
The checker's obligations are **not** "primality and distinctness of the
moduli": primality is not needed at all for the determinant and the
polynomial gcd, distinctness does not imply what the argument needs, and
the property that does the work is pairwise coprimality, which is
checked. See "Primality is not what the checkers need". And the output
condition `gcd(q, m) = 1` on a reconstructed rational is a theorem rather
than a check, derivable from `gcd(p, q) = 1` and the congruence. See
"The signature is checked, so soundness is free".

## Why this library exists

**Three consumers, none of which should depend on the others.**
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) reconstructs an integer
determinant from residues and a rational solution vector from a `p`-adic
expansion. [hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md) reconstructs an integer
polynomial coefficient vector from residues.
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) does the same one arity up. A matrix library
and a polynomial library have no business depending on each other, so
what they share belongs underneath both.

**Rational reconstruction has consumers that want nothing else.**
hex-number-field's exactification turns a certified approximation into an
exact algebraic number, and the `p`-adic route to that (rather than the
continued-fraction route it uses now) is one call to `ratRecon?`.
Berlekamp-Zassenhaus's lifting phase reconstructs integer factors from
residues modulo `p^k`, which is the same operation with `P` and `Q`
chosen from the Mignotte bound rather than symmetrically. Neither
consumer wants a determinant.

**The modulus supply is one decision, made once.** Every modular
algorithm needs a stream of moduli, a way to reject one that turns out to
be unusable, and the `ZMod64.Bounds` evidence to compute in `ZMod64 p` at
all. Berlekamp-Zassenhaus already solved a small version of this problem
with `SmallPrimeCandidate` and its two fixed candidate lists. That
solution is right in shape and too small in range, and the second library
to need it should not write a third version.

## Why not inside hex-arith

An earlier draft of this SPEC gave a structural reason: the modulus
supply bundles a `ZMod64.Bounds` instance, so it sits above
hex-mod-arith, so the library cannot sit inside hex-arith. That reason
does not survive putting the supply where it belongs. `Modulus` and the
bundled `Prime` package `ZMod64` evidence and belong beside `ZMod64` in
hex-mod-arith, generalising `SmallPrimeCandidate`, and everything left
here is arithmetic on `Int` and `Nat`. This library therefore depends on
hex-arith alone.

The honest reason for a separate library is subject separation rather
than a dependency. Chinese remaindering and rational reconstruction have
their own conformance fixtures, their own oracle, their own benchmark
families, and three consumers that each want a different part; hex-arith
is a library of scalar primitives with none of that surface, and it is
complete at `done_through: 7`, so absorbing a new subject there means
reopening a finished library. Principle 1 asks for many small libraries
split along their seams, and this is one.

The alternative is defensible and this SPEC records it rather than
pretending otherwise: folding `SymMod.lean`, `Euclid.lean`, and
`Recon.lean` into hex-arith and leaving only the loop here would also
work, and would trade one library for one reopened phase.

## Scope

In scope: symmetric representatives modulo `m`; incremental Chinese
remaindering for a scalar and for a vector of residues sharing a modulus;
rational reconstruction with explicit bounds, with symmetric bounds, and
with the maximal-quotient heuristic; the vector form with a common
denominator; the modulus supply and its runtime primality test; and the
loop combinator that adds moduli until a caller-supplied check accepts.

Not in scope: `p`-adic lifting (that is Dixon's, and it lives with its
consumer in [hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md)); the
coefficient bounds that tell a consumer how large a modulus it needs
(a Hadamard bound is a matrix fact and a Mignotte bound is a polynomial
fact, so each belongs with its own type); prime *choice* heuristics,
which are per-consumer; and a first-class `Zp` type, which is its own
entry in [future-work](../../SPEC/future-work.md) and would consume this library
rather than replace it.

## Symmetric representatives

Every reconstruction in the tree ends by choosing a representative in
`(-m/2, m/2]`, and every proof that a reconstruction is correct ends by
citing uniqueness of that representative under a size bound. Both belong
here, once.

```lean
namespace Hex.Modular

/-- The representative of `a` modulo `m` in the interval `(-m/2, m/2]`. -/
def symMod (a : Int) (m : Nat) : Int

theorem symMod_emod (h : 0 < m) : (symMod a m) % (m : Int) = a % (m : Int)
theorem symMod_le (h : 0 < m) : 2 * (symMod a m).natAbs ≤ m
theorem symMod_unique (h : 2 * x.natAbs < m) (hx : x % (m : Int) = a % (m : Int)) :
    symMod a m = x
```

`symMod_unique` is the lemma the determinant, the gcd, and the linear
solve all finish with, and it is stated with a **strict** inequality on
purpose. At `2 * |x| = m` with `m` even there are two representatives,
`m/2` and `-m/2`, and the interval convention picks one; a consumer whose
bound is not strict has not proved what it thinks it has. Every caller in
this tree therefore chooses a modulus exceeding twice its bound rather
than equalling it, and the extra bit is free because it is one more
prime out of hundreds.

## Chinese remaindering

The operation is incremental, not batched. A consumer computes an image,
folds it in, tests whether the accumulated value is already the answer,
and stops. Batching the residues first would force it to decide the
number of moduli in advance, which for the determinant means always
paying the worst case and for the gcd means paying a bound that is
usually enormously pessimistic.

```lean
/-- A residue accumulated from several coprime moduli: `value` is the
symmetric representative of the common solution modulo `modulus`. -/
structure Crt where
  modulus : Nat
  value : Int
  pos : 0 < modulus
  le : 2 * value.natAbs ≤ modulus

def Crt.init : Crt := { modulus := 1, value := 0, pos := by decide, le := by decide }

/-- Fold in the residue `r` modulo `m`. Returns `none` when `m` is zero
or one, or when `m` is not coprime to the moduli already folded in. -/
def Crt.push (c : Crt) (r : Int) (m : Nat) : Option Crt

/-- The same, for `k` residues sharing one modulus. -/
def CrtVec.push (c : CrtVec k) (r : Vector Int k) (m : Nat) : Option (CrtVec k)
```

**The positivity and size fields are structure invariants, not
afterthoughts.** Without `pos`, `Crt.init.push 1 0` is accepted, because
`gcd(1, 0) = 1`: the result has `modulus = 0`, and then `push_modulus`,
`push_le`, and `push_congr_new` below are jointly unsatisfiable. Carrying
the invariants in the structure makes the bad state unconstructible
rather than merely unreachable, and `push` rejects `m ≤ 1` before doing
any arithmetic.

`push` runs `HexArith.Int.extGcd (c.modulus % m) m`, which returns
`(g, s, t)` with `s * (c.modulus % m) + t * m = g`. It returns `none`
unless `g = 1`, and otherwise `s` is the inverse of `c.modulus` modulo
`m` and the update is

```
δ        = symMod ((r - c.value) * s) m
modulus' = c.modulus * m
value'   = symMod (c.value + c.modulus * δ) modulus'
```

which is Garner's mixed-radix step. The arithmetic that grows with the
number of moduli is one multiplication and one addition on integers of
the size of the accumulated value, and everything else is word-sized.

**The reduction `c.modulus % m` before the extended gcd is what makes
that true.** `c.modulus` reaches thousands of bits, and an inverse
computed from it directly runs the Euclidean algorithm on a large
operand for a word-sized answer. Since `s` is determined modulo `m`, the
reduced operand gives the same inverse. Skipping the reduction is a
correctness-neutral performance bug, which is the kind this SPEC exists
to prevent.

**The outer `symMod` is not redundant.** With `|c.value| ≤ c.modulus/2`
and `|δ| ≤ m/2`, the sum reaches `c.modulus·(m+1)/2`, which exceeds
`modulus'/2` by up to half of `c.modulus`. Dropping the outer reduction
therefore breaks `push_le` below, and with it the size hypothesis of
`crt_unique`, which is the only thing standing between a consumer and a
wrong answer. It costs one division per modulus.

**The vector form is a separate function, not a `map` of the scalar
one.** The inverse `s` depends only on the two moduli, so `k` residues
sharing a modulus need one `extGcd` between them rather than `k`. For the
gcd, `k` is the degree of the answer; for a determinant it is `1`; for a
matrix reconstruction it is `n²`. Writing the vector form as a fold of
the scalar one would multiply the extended-gcd cost by `k` on the two
consumers that care.

```lean
theorem push_modulus : (c.push r m) = some c' → c'.modulus = c.modulus * m
theorem push_congr_new : (c.push r m) = some c' → c'.value % m = r % m
theorem push_congr_old (hd : (d : Int) ∣ c.modulus) :
    (c.push r m) = some c' → c'.value % d = c.value % d
theorem push_le : (c.push r m) = some c' → 2 * c'.value.natAbs ≤ c'.modulus

/-- The reconstruction is determined: two integers small enough and
congruent to the same residues modulo the same moduli are equal. -/
theorem crt_unique (h : 2 * x.natAbs < c.modulus) (h' : 2 * y.natAbs < c.modulus)
    (hx : x % (c.modulus : Int) = y % (c.modulus : Int)) : x = y
```

`push_congr_old` is stated for every divisor `d` of the accumulated
modulus rather than for the individual moduli, because that is what
survives the induction over the fold and it specialises to the moduli
without extra work.

`crt_unique` is `symMod_unique` restated, and it is where the whole
family of algorithms gets its answer. Nothing above it needs a theorem
about the Chinese remainder *isomorphism*: the executable statement is
that a small enough integer is determined by its residues, and the
isomorphism is the companion's business.

## Rational reconstruction

Fix `m > 0` and a residue `a`, and bounds `P, Q > 0`. The problem is to
find `p/q` with

```
q * a ≡ p (mod m),   |p| ≤ P,   0 < q ≤ Q,   gcd(p, q) = 1.
```

### The stopping rule needs a truncated Euclidean run

`Hex.Int.extGcd` returns the gcd and one Bézout pair. Rational
reconstruction needs the *intermediate* rows of the same computation: run
the extended Euclidean algorithm on `(m, a)` producing
`rⱼ = sⱼ·m + tⱼ·a`, and stop at the first `j` with `rⱼ ≤ P`. So the
primitive is new, even though the algorithm is one hex-arith already has.

```lean
/-- One row of the extended Euclidean remainder sequence on `(m, a)`:
`r = s * m + t * a`, with `s` dropped because no consumer reads it. -/
structure Row where
  r : Int
  t : Int

/-- The first row of the remainder sequence on `(m, a)` whose remainder
is at most `P`. -/
def euclidUntil (m a P : Int) : Row
```

`euclidUntil` is the only new arithmetic in this library, and it is more
than a wrapper. `HexArith.Int.extGcd` is an `@[extern]` binding that
returns the final triple, so no intermediate row is reachable through it:
`euclidUntil` needs either its own extern primitive or a refactoring of
the existing one to take a stopping predicate. Which of those is right is
an implementation question, and it is the one open question in this
library that costs real work rather than a decision.

### The signature is checked, so soundness is free

```lean
/-- Reconstruct `a mod m` as a rational with numerator at most `P` in
absolute value and denominator at most `Q`. -/
def ratRecon? (a : Int) (m : Nat) (P Q : Int) : Option Rat

/-- The symmetric case `P = Q = ⌊√((m-1)/2)⌋`, which satisfies `2PQ < m`
by construction and is what a caller with no bound of its own should
use. -/
def ratReconWide? (a : Int) (m : Nat) : Option Rat
```

The return type is `Rat`, not `Int × Int`. A `Rat` is already a coprime
pair with a positive denominator, so three of the four output conditions
are the invariants of the type, and `Rat.normalize` (or `mkRat`) is where
they are established. Not `Rat.mk'`, which is the raw structure
constructor and takes the invariants as arguments rather than
establishing them.

`ratRecon?` takes the row `euclidUntil m a P` returns, forms the
candidate from `(r, t)` with the sign normalised so the denominator is
positive, divides out `gcd(r, t)`, and then **checks** the congruence and
both bounds, returning `none` if any fails. Soundness is therefore true
by construction:

```lean
theorem ratRecon?_congr : ratRecon? a m P Q = some x →
    (x.den * a - x.num) % (m : Int) = 0
theorem ratRecon?_bounds : ratRecon? a m P Q = some x →
    x.num.natAbs ≤ P ∧ 0 < x.den ∧ (x.den : Int) ≤ Q
```

`gcd(q, m) = 1` does not appear as a check, because it follows. If
`d ∣ q` and `d ∣ m`, then from `q·a - p = k·m` we get `d ∣ p`, and
`gcd(p, q) = 1` forces `d = 1`:

```lean
theorem ratRecon?_den_coprime : ratRecon? a m P Q = some x →
    Nat.gcd x.den m = 1
```

[future-work](../../SPEC/future-work.md) lists it among the conditions the
algorithm establishes, which reads as though it were a fourth thing to
test. It is a consequence of the other three, and stating it as a theorem
rather than a check keeps one modular inverse out of the inner loop.

### Uniqueness

```lean
theorem ratRecon_unique (hm : 2 * P * Q < m)
    (h₁ : (y₁.den * a - y₁.num) % (m : Int) = 0)
    (h₂ : (y₂.den * a - y₂.num) % (m : Int) = 0)
    (b₁ : y₁.num.natAbs ≤ P ∧ (y₁.den : Int) ≤ Q)
    (b₂ : y₂.num.natAbs ≤ P ∧ (y₂.den : Int) ≤ Q) : y₁ = y₂
```

The proof is three lines of arithmetic and it is the reason the whole
technique is usable. From the two congruences,
`p₁q₂ ≡ q₁·a·q₂ ≡ p₂q₁ (mod m)`, so `m ∣ p₁q₂ - p₂q₁`. The bounds give
`|p₁q₂ - p₂q₁| ≤ 2PQ < m`, so the difference is zero and the two
rationals are equal.

Note what the argument does not use: coprimality of the numerator and
denominator plays no part, so the uniqueness statement covers unreduced
pairs as well. That is what makes the common-denominator vector form
below meaningful.

### Completeness

Soundness is by construction, so the content of the algorithm is that it
finds a solution whenever one exists.

```lean
theorem ratRecon?_complete (hm : 2 * P * Q < m)
    (hy : (y.den * a - y.num) % (m : Int) = 0)
    (hb : y.num.natAbs ≤ P ∧ (y.den : Int) ≤ Q) :
    ratRecon? a m P Q = some y
```

This is the one substantial proof in the library. It rests on the
standard property of the Euclidean remainder sequence, that
`|tⱼ| · rⱼ₋₁ ≤ m` for every `j`, which bounds the cofactor of the first
row below `P` and places the candidate inside the bounds; the target `y`
then agrees with the candidate by `ratRecon_unique`. The reference to
follow is von zur Gathen and Gerhard, *Modern Computer Algebra*, §5.10,
whose Theorem 5.16 is this statement and whose Lemma 5.15 is the cofactor
bound. Wang, Guy, and Davenport, "P-adic reconstruction of rational
numbers" (SIGSAM Bulletin 16, 1982), is the original.

Because completeness needs `2PQ < m` and `ratRecon?` does not, a caller
that supplies bounds violating it still gets a sound answer, just not a
determined one. The signature does not carry the hypothesis for that
reason, and `ratReconWide?` exists so that the common case cannot get it
wrong.

### What the caller does when it returns none

`none` means "not at this modulus", never "no such rational". Every
consumer's response is the same: fold in another modulus (or one more
`p`-adic digit) and try again. The reconstruction is therefore always
inside a loop with a growing modulus, which is why the loop combinator
below is part of this library rather than each consumer's own.

### Vectors with a common denominator

The linear solve reconstructs `n` rationals that share a denominator
dividing the determinant, and the polynomial gcd reconstructs a
coefficient vector whose entries are integers. Reconstructing each entry
separately would run `k` Euclidean sequences where one usually suffices.

```lean
/-- Reconstruct `k` residues as rationals with a common denominator.
Returns the numerators and the denominator. -/
def ratReconVec? (a : Vector Int k) (m : Nat) (P Q : Int) :
    Option (Vector Int k × Int)
```

The algorithm reconstructs the first entry, obtaining a denominator `d`,
and for each later entry first tries `symMod (d * aᵢ) m`, accepting it
when it is within `P`. That test is one multiplication. Only when it
fails does the entry get its own Euclidean run, and then `d` is replaced
by `lcm d dᵢ`, the accepted numerators are rescaled by `lcm d dᵢ / d`,
and the whole pair `(y, d)` is divided through by the gcd of all its
entries.

**The `lcm` and the reduction are both load-bearing, and an earlier draft
of this SPEC had neither.** Multiplying the denominators instead
overshoots: at `m = 101`, `P = 2`, `Q = 4`, the residues `(51, 76)` are
`(1/2, 1/4)`, and multiplying gives `d = 8` with numerators `(4, 2)`,
both outside the bounds, while `lcm` gives the correct `(2, 1)/4`. No
amount of further lifting repairs the overshoot, because the fault is in
the combination step rather than in the precision.

```lean
theorem ratReconVec?_spec : ratReconVec? a m P Q = some (y, d) →
    0 < d ∧ (d : Int) ≤ Q ∧
    ∀ i, (d * a[i] - y[i]) % (m : Int) = 0 ∧ y[i].natAbs ≤ P
```

The output is reduced as a whole (no integer divides `d` and every `yᵢ`)
but individual entries need not be in lowest terms, since `d` is the
common denominator rather than each entry's own. Under `2PQ < m` the
rational vector `y/d` is unique, by `ratRecon_unique` applied entrywise,
which is exactly the case the uniqueness proof covers without a
coprimality hypothesis.

**What `Q` has to bound.** The postcondition asserts `d ≤ Q`, and `d` is
the least common denominator of the whole vector, not of any one entry.
A caller whose bound covers each entry separately has not supplied a
usable `Q`. Dixon's caller does supply one, because Cramer's rule bounds
the common denominator by `|det A|`, and that is the sense in which the
completeness statement for the vector form is about the vector rather
than about its entries.

### Reconstruction without bounds

Some callers have no usable bound. The determinant of a random matrix is
enormously smaller than its Hadamard bound, and a caller that waits for
the bound pays for primes it did not need. The heuristic answer is
maximal-quotient rational reconstruction: run the remainder sequence,
take the row before the largest partial quotient, and hand the candidate
to the caller's own check.

```lean
/-- The maximal-quotient candidate. Heuristic: the result satisfies the
congruence, and nothing is claimed about it being the intended rational.
-/
def ratReconMaxQuot? (a : Int) (m : Nat) : Option Rat
```

The soundness theorem is the congruence and nothing else, which is
honest, and it is enough for a consumer whose check is exact (trial
division for a gcd, one matrix-vector product for a linear solve). It is
**not** enough for the multi-modular determinant, which has no cheap
check, and [hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) says so in the one
place it matters. Monagan, "Maximal quotient rational reconstruction: an
almost optimal algorithm for rational reconstruction" (ISSAC 2004), is
the reference, and the failure probability analysis there is the reason
this is offered as a candidate producer rather than as a decision.

## Moduli

### Primality is not what the checkers need

[future-work](../../SPEC/future-work.md) says the checker's obligations include
"primality and distinctness of the moduli". Neither half is right, and
getting this wrong would put a large avoidable cost inside the kernel.

**Distinctness is not the property.** Two distinct moduli need not be
coprime, and the reconstruction argument needs coprimality. For prime
moduli the two coincide, which is presumably how the sentence came
about, but the checkable statement is the coprimality one and `Crt.push`
checks it directly with one extended gcd.

**Primality is not needed for the reconstruction.** `det (A mod m) =
(det A) mod m` holds for every modulus, prime or not, because reduction
is a ring homomorphism. The same is true of every polynomial identity the
gcd certificate checks. What primality buys is that *elimination* can
divide: Gaussian elimination modulo `m` needs its pivots to be units. The
implementation gets that from the arithmetic rather than from a
hypothesis, because inverting a residue runs an extended gcd that either
returns an inverse or exhibits a nontrivial factor of `m`. A modulus
whose pivot is not invertible is discarded, and no wrong answer is
possible.

**Where primality genuinely appears** is in statements that mention
`F_p` as a field: the rank of an image, and the coprimality witness in
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md), which needs `F_p[x]` to be a domain.
Those consumers carry a `Hex.Nat.Prime p` argument, and the rest do not.

### Kernel-replayed primality is priced by the size of the prime

Where a certificate's checker names a prime, replaying that certificate
in the kernel replays the primality proof. `Hex.Nat.isPrimeTrial` is
trial division with a balanced recursion, so its cost grows like `√p`.
Measured on this tree with `decide +kernel`, against a baseline of 0.81 s
for the import alone:

| prime | bits | elaboration |
|---|---|---|
| `65521` | 16 | 0.04 s |
| `1048573` | 20 | 0.08 s |
| `16777213` | 24 | 0.42 s |
| `2147483647` | 31 | 6.2 s |

The consequence is a design rule, not a footnote: **a certificate whose
checker needs a prime should name the smallest usable one.** The
coprimality witness in [hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md) may use any
prime at which two degrees survive, so it uses a small one and the
kernel replay is free. A multi-modular determinant wants primes as large
as `ZMod64.Bounds` allows, and it can have them precisely because its
correctness argument never mentions primality.

At runtime none of this arises. `isPrimeTrial` on a 31-bit candidate is
under a millisecond of compiled code, which is negligible beside one
`O(n³)` image, so moduli are found by running it rather than by consulting
a table.

**The "Better primality" item in [future-work](../../SPEC/future-work.md) changes
both halves of this, and neither change is on this library's critical
path.** Its Miller-Rabin
compositeness test replaces trial division in `primesBelow`, turning tens
of microseconds into a few modular exponentiations. Its Pocklington
certificate replaces the kernel cost above: a checked Pocklington witness
for a 31-bit prime is a handful of modular exponentiations rather than
46341 divisions, so the "name a small prime" rule below becomes a
preference rather than a requirement. Neither is assumed here. This
library is written against `isPrimeTrial`, which exists, and the
switchover is a body change behind an unchanged signature.

### The supply, which belongs in hex-mod-arith

```lean
namespace Hex.ZMod64

/-- A usable modulus: a natural number with the small-modulus evidence
attached. -/
structure Modulus where
  m : Nat
  [bounds : Bounds m]

/-- A bundled modulus known to be prime, for the consumers whose statements
mention `F_p`. Named differently from the existing `PrimeModulus p`
typeclass. -/
structure Prime extends Modulus where
  prime : Hex.Nat.Prime m

/-- Successive primes below `2^31`, descending from `start`. Untrusted:
the primality test runs at runtime and its result is carried as evidence,
so a wrong answer here is impossible rather than merely unlikely. -/
def primesBelow (start : Nat) : Nat → Array Prime
```

These three go in **hex-mod-arith**, not here. They package
`ZMod64.Bounds` and a primality witness, they mention nothing about
Chinese remaindering, and hex-mod-arith already has the class
`ZMod64.PrimeModulus` that the structure's `prime` field produces through
`primeModulusOfPrime`. Putting them there is what lets this library
depend on hex-arith alone, and it makes
`HexBerlekampZassenhaus/PrimeSelection.lean`'s `SmallPrimeCandidate` the
special case it is rather than a parallel definition.

The naming collision with the existing class is deliberate and worth one
sentence: the class is a hypothesis about a `p` fixed by the context, the
structure is a `p` carried with its evidence. If that reads badly in
practice the structure is the one to rename, since it is new.

The `Bounds` and `Prime` fields are propositions built at runtime from a
dependent `if` on `isPrimeTrial`, so they are erased in compiled code and
cost nothing.

### The supply is bounded, and the consumers have to say so

`ZMod64.Bounds` requires `m < 2^31`, and that is not only a performance
limit. Write `L` for the least common multiple of everything below
`2^31`. Every allowed modulus divides `L`, and any product of pairwise
coprime allowed moduli divides `L` too, so the accumulated modulus can
never exceed `L`. On the `1 x 1` matrix `[L]` the determinant is `L`, the
Hadamard bound is `L`, every image is zero, and a loop that stops when
the modulus exceeds twice the bound never stops.

Nothing in this library can fix that, and it is recorded here because it
is the shared cause of three separate obligations elsewhere:
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md)'s determinant needs a
fallback that does not use moduli at all, its rank certificate needs a
lower-bound witness that is not restricted to small moduli, and
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md)'s coprimality certificate needs a
constructor that names no prime. Each of those SPECs carries the
counterexample for its own case.

`crtLoop` below therefore takes fuel and returns `Option`, and no
consumer may present a modular route as total on the strength of a bound
alone.

## The multimodular loop

All three consumers have the same outer shape, and it is worth having
once:

```lean
/-- Fold moduli in until `accept` returns a result. `image` computes the
residue vector at one modulus, `accept` attempts a reconstruction and
returns `none` to ask for another modulus. -/
def crtLoop (image : Nat → Option (Vector Int k))
    (accept : CrtVec k → Option α) (supply : Array Nat) (fuel : Nat) :
    Option α
```

The moduli are bare `Nat`s. A consumer computing in `ZMod64` passes the
`m` field of its `Modulus` values and recovers the evidence on its own
side, which is what keeps this library independent of hex-mod-arith.

`image` returns `none` for a modulus the consumer rejects (a vanishing
leading coefficient, a non-invertible pivot), and those moduli are
skipped without entering the accumulated state. `accept` is where the
consumer's own check goes: trial division for a gcd, a size bound for a
determinant, a matrix-vector product for a solve.

Three properties this shape has, each of which was a decision:

- **Rejected moduli never enter the state.** A consumer cannot poison the
  accumulated residue by folding in an image it computed under a broken
  assumption.
- **`accept` decides, and the loop proves nothing.** The loop's own
  theorem is that its result is one `accept` returned on a state whose
  modulus is the product of the moduli used, which is all a soundness
  argument needs, because the consumer's `accept` carries the rest.
- **Fuel rather than a termination proof.** Whether the loop terminates
  depends on the consumer's bound, not on the loop, so it is fuelled and
  returns `Option`. Each consumer proves its own totality statement by
  supplying the fuel its bound requires. Under design principle 8 this is
  not a total form of a partial helper at all: the `Option` is
  propagated, never defaulted.

## What this library does not decide

Prime choice heuristics belong to the consumers. Which primes are bad
(the leading coefficient vanishes), which are unlucky (the image is
correct for a different problem than the one asked), how many to try
before falling back, and what the fallback is are all questions whose
answers differ per algorithm and none of which affects soundness. This
library supplies the moduli and the arithmetic. Every consumer's SPEC
carries its own rejection rules.

## Complexity

`k` moduli of `w` bits, an accumulated modulus of `M = k·w` bits, a
vector of `n` residues.

| operation | algorithm | cost |
|---|---|---|
| `symMod` | one division | `O(M)` word ops |
| `Crt.push` | one `extGcd` on two words, one multiply-add at size `M` | `O(w²)` plus `O(M)` |
| `CrtVec.push` | one `extGcd`, `n` multiply-adds | `O(w²)` plus `O(n·M)` |
| `k` pushes, cumulative | quadratic in the number of moduli | `O(k²·w²)` word ops |
| `euclidUntil` | truncated Euclidean run at size `M` | `O(M²)` word ops |
| `ratRecon?` | `euclidUntil` plus checks | `O(M²)` |
| `ratReconVec?` | one run plus `n` multiplications, on average | `O(M²) + O(n·M)` |

The cumulative `O(k²w²)` for a full multi-modular run is the entry that
matters, and it is what a product-tree (fast) CRT would improve to
`O(M(M) log k)`. That is a later milestone: at `k = 400` and `w = 31` the
incremental cost is under a millisecond of word operations, which is far
below the `O(n³)` per-image cost that motivates the whole technique. The
crossover is a measurement, and the benchmark family below is designed to
find it rather than to assume it.

## Kernel exposure

The kernel replay closure is `symMod`, `Crt.push`, and a separate
checker

```lean
/-- Accepts `x` as the reconstruction of `a` modulo `m` within the given
bounds. The predicate `ratRecon?` tests before returning, exposed on its
own so a proof term never mentions the search. -/
def ratReconCheck (a : Int) (m : Nat) (P Q : Int) (x : Rat) : Bool
```

all of which are `@[expose]` and reduce cheaply. `ratRecon?` itself is
**not** exposed, and this is the correction to an earlier draft that
claimed the checks inside it were in the closure while `euclidUntil` was
not: an exposed `ratRecon?` unfolds to `euclidUntil`, so the Euclidean
sequence would be in the closure with it. Splitting the predicate out
keeps the closure to what a certificate actually replays, which is the
congruence and the two bounds.

The one thing that *is* expensive in the kernel is a primality proof, and
the table above prices it. A downstream module carries a `decide +kernel`
test over a fixed small certificate so that a change making `symMod` or
`Crt.push` stop reducing is caught.

## Conformance

Fixtures follow [SPEC/testing.md](../../SPEC/testing.md). A Lean driver at
`conformance/HexModular/EmitFixtures.lean` exposed as
`lean_exe hexmodular_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexModular/modular.jsonl`, and an oracle driver at
`scripts/oracle/modular_sympy.py`. One tuple appended to `ORACLES` in
`scripts/ci/run_oracles.sh`, not a new job:

```
"HexModular|hexmodular_emit_fixtures|scripts/oracle/modular_sympy.py|conformance-fixtures/HexModular/modular.jsonl"
```

Three fixture kinds: `crt` (a list of residue and modulus pairs, result
the symmetric representative and the product), `ratrecon` (residue,
modulus, bounds, result the rational or a failure marker), and `symmod`
(value, modulus, result).

**The oracle is partly a property check rather than a value check.**
SymPy's `sympy.ntheory.modular.crt` covers Chinese remaindering directly.
It has no rational reconstruction, so the oracle script carries a short
independent implementation using `fractions.Fraction` and its own
Euclidean loop, and additionally verifies the two properties that matter
by brute force on the small cases: that the returned rational satisfies
the congruence and the bounds, and that no other rational within the
bounds does. The brute-force uniqueness sweep runs only for moduli below
a few thousand, where it is exhaustive over the denominator, and it is
the part of the suite that would catch a wrong stopping rule.

Cases that must be present:

- `m = 1`, `a = 0`, and a single modulus, where the reconstruction is
  trivial and off-by-one errors live.
- The tie at `2|x| = m` for even `m`, checking the interval convention
  in both signs.
- **The outer-reduction regression**: push `1` modulo `3`, then `0`
  modulo `2`. Garner's step gives `4`, and the required symmetric
  representative modulo `6` is `-2`. Without this case, dropping the
  outer `symMod` passes the whole suite.
- `m = 0` and `m = 1` offered to `push`, both of which must be rejected.
- Non-coprime moduli, checking that `Crt.push` returns `none` rather than
  a wrong value.
- Reconstructions that must fail: a residue with no rational inside the
  bounds, where `none` is the answer and returning a candidate would be a
  soundness bug.
- Negative numerators, denominators of `1`, and the integer case, which
  is the one every consumer hits most often.
- Bounds violating `2PQ < m`, where the result is sound but not
  determined, checked against the property rather than against a value.
- A reconstruction just inside and just outside the bound, at several
  sizes, to catch a boundary error that a random sweep would miss.
- Vector reconstruction where the common denominator is found on the
  first entry, on the last entry, and where two entries force it to grow.

## Benchmarking

Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md), with drivers at
`bench/HexModular/Bench.lean`. Native and kernel: the kernel suite
measures `symMod` and `Crt.push` reduction, since those are the two
operations a downstream certificate replay pays for.

Families:

- **Incremental CRT**, `k` from 4 to 4000 moduli of 31 bits. The declared
  complexity is `k²`, and the family exists to find the point where a
  product tree would pay.
- **Vector CRT**, `k` moduli against `n` from 1 to 4096 residues,
  checking that the extended gcd is amortised across the vector rather
  than repeated.
- **Rational reconstruction**, moduli from 64 to 100000 bits, over
  reconstructions that succeed early, succeed late, and fail.
- **Failure cost**, the same sizes where no rational exists, since a
  consumer in a loop pays this on every modulus until the last.

**Comparators.** `gmpy2`'s `gcdext` and FLINT's `fmpz_mod_ctx` CRT are
`informational`: both are C implementations of the same operations and
the ratio measures the GMP binding rather than the algorithm. SymPy is
the oracle and is not a performance comparator. No comparator is
`gating`, because this library has no algorithmic choice for one to
discriminate: the algorithms here are the standard ones and the
performance question is entirely about the arithmetic underneath, which
hex-arith already measures.

## The Mathlib layer

`hex-modular-mathlib` relates the executable operations to Mathlib's:

```lean
theorem symMod_cast (h : 0 < m) : ((symMod a m : Int) : ZMod m) = (a : ZMod m)
theorem symMod_eq_intCast_iff : ...

theorem crt_push_cast (h : c.push r m = some c') :
    ((c'.value : Int) : ZMod m) = (r : ZMod m)

/-- The accumulated value is the image of the Chinese remainder
isomorphism at the given residues. -/
theorem crt_eq_chineseRemainder : ...

theorem ratRecon?_eq (h : ratRecon? a m P Q = some x) :
    ((x.num : ZMod m)) = (x.den : ZMod m) * (a : ZMod m) ∧ IsUnit ((x.den : ZMod m))
```

Mathlib has `ZMod.chineseRemainder` for coprime moduli, so the
correspondence for a two-modulus push is a transport. The `k`-modulus
statement is an induction over the fold, and the reason to state it at all
is that a Mathlib-facing consumer (the determinant correspondence in
[hex-modular-matrix-mathlib](../../SPEC/Libraries/hex-modular-matrix.md)) wants to argue in
`ZMod` and land in `ℤ`.

Rational reconstruction has no Mathlib counterpart to correspond with, so
the companion's work there is to restate the uniqueness and completeness
theorems over `ℚ` with `Rat.cast`, and to supply

```lean
instance : DecidablePred (fun x : ℚ => (x.den : ZMod m) * a = x.num ∧ |x.num| ≤ P ∧ x.den ≤ Q)
```

which is what makes `ratRecon?` usable to discharge a Mathlib goal about
a rational congruence rather than only inside a larger computation.

Following the project split, no theorem about `Crt` or `Row` belongs in
the companion beyond these and one correspondence lemma per public
operation.

## Prerequisite changes in other libraries

Three relocations, each with a reason independent of this library.

**`Modulus`, the bundled `Prime`, and `primesBelow` belong in
hex-mod-arith**, as "The supply" above sets out, and
`SmallPrimeCandidate` from `HexBerlekampZassenhaus/PrimeSelection.lean`
should become the special case of them rather than a parallel
definition. Unlike the other two relocations, this one is a
precondition: without it this library acquires a dependency on
hex-mod-arith that its subject does not justify.

**`zmod64FieldOfPrime` should move to hex-mod-arith.** The
`Lean.Grind.Field (ZMod64 p)` instance and the `ZMod64.intPow` it needs
live in `HexPolyFp/PrimeField.lean`. The instance is a statement about a
hex-mod-arith type, its proof uses `ZMod64` lemmas and
`Init.Grind.Ring.Field`, and the module's only polynomial import is
`HexPolyFp.Degree`. As it stands, any library wanting to do linear
algebra over `F_p` must depend on hex-poly-fp for one instance about a
type it already has, which is what
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) would otherwise have to do.

**`floorSqrt` and `ceilSqrt` should move to hex-arith.** They are
Newton-iteration integer square roots defined in `HexPolyZ/Mignotte.lean`
under the `Hex.ZPoly` namespace, where the Mignotte bound needed them.
`ratReconWide?` needs `⌊√((m-1)/2)⌋` and the Hadamard bound in
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) needs `ceilSqrt` per column.
An integer square root under a polynomial namespace is a naming error as
well as a placement one.

The second and third do not block starting work here, and until they
land this library can name the existing paths. The first does block, in
the weak sense that skipping it costs a dependency this SPEC's placement
argument says should not exist.

## Milestones

1. **Symmetric representatives and Chinese remaindering.** `symMod` with
   its three theorems, `Crt`, `CrtVec`, `push` with the congruence and
   bound theorems, and `crt_unique`. This milestone alone unblocks the
   determinant.

2. **Rational reconstruction.** `euclidUntil`, `ratRecon?`,
   `ratReconWide?`, soundness, `ratRecon_unique`, and
   `ratRecon?_den_coprime`. Completeness may lag by one milestone: it is
   the only hard proof here, and no consumer's soundness depends on it.

3. **The vector forms and the loop.** `ratReconVec?` with the `lcm`
   combination and the reduction, and `crtLoop`. The modulus supply lands
   in hex-mod-arith alongside. At the end of this milestone both consumer
   libraries can be written.

4. **Completeness and the heuristic.** `ratRecon?_complete` and
   `ratReconMaxQuot?`.

5. **The companion.** The `ZMod` correspondence, the `ℚ` restatements,
   and the decidability instances. Begins as soon as milestone 2 is done.

## File organisation

```
HexModular/
  SymMod.lean       -- symMod and its uniqueness lemma
  Crt.lean          -- Crt, CrtVec, push, crt_unique
  Euclid.lean       -- Row, euclidUntil
  Recon.lean        -- ratRecon?, ratReconWide?, ratReconVec?, ratReconMaxQuot?
  Loop.lean         -- crtLoop
HexModular.lean
HexModularMathlib/
  Crt.lean          -- ZMod correspondence
  Recon.lean        -- the ℚ restatements and the decidability instances
HexModularMathlib.lean
```

No file here mentions `ZMod64`. `Modulus` and `primesBelow` live in
hex-mod-arith, per "The supply", and `crtLoop` takes bare `Nat` moduli.

`libraries.yml` gains:

```yaml
  HexModular:
    deps: [HexArith]
    mathlib: false
    done_through: 1
    status: active
  HexModularMathlib:
    deps: [HexModular, HexModArithMathlib]   # ZMod correspondence only
    mathlib: true
    done_through: 0
    status: planned
```

The Mathlib-free core is active through Phase 1.  The companion remains
planned until its correspondence and decidability layer is implemented.

## Open questions

- **Whether `euclidUntil` and `extGcd` should share an implementation.**
  Both run the same division loop on the same operand sizes, one keeping
  the last row and one keeping the first row below a threshold. A single
  loop with a stopping predicate would serve both, at the cost of an
  indirection in hex-arith's hottest scalar routine. Measure before
  merging them.
- **Whether the product-tree CRT is worth having.** The complexity table
  says the incremental cost is negligible against the images at the sizes
  the consumers use. The benchmark family exists to find the size where
  that stops being true, and the answer may be that no consumer reaches
  it.
- **Whether `Modulus` should carry the Barrett context.** hex-arith has
  Barrett and Montgomery reduction, and a modulus used for `O(n³)`
  operations wants its reduction context precomputed once. Attaching it
  to `Modulus` makes that automatic and makes the structure heavier for
  the consumers that use a modulus twice. This should be settled by the
  determinant benchmark rather than in advance.
- **When to switch the modulus supply to a better primality test.** The
  switch to Miller-Rabin is a strict improvement, and it introduces a
  dependency on whichever library ends up owning the "Better primality"
  item in [future-work](../../SPEC/future-work.md). The question is only
  ordering, and the answer should be "as soon as that library has a
  compositeness test", at which point it joins the `deps` list above.
- **Whether a first-class `Zp` type subsumes the Dixon lifting loop.**
  [future-work](../../SPEC/future-work.md) proposes `Zp` and `Qp` at fixed
  precision, with Dixon named as a consumer. If that lands, the precision
  contract it specifies is the natural home for the lifting loop that
  [hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) currently writes out. The
  reconstruction and the CRT stay here either way.
