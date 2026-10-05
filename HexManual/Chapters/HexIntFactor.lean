/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexIntFactor
import HexIntFactorMathlib
import HexIntFactorMathlib.Mixed

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexIntFactor: factoring integers with certificates" =>
%%%
tag := "hex-int-factor"
%%%

# Introduction
%%%
tag := "hex-int-factor-intro"
%%%

`HexIntFactor` factors natural numbers into primes. Every factorization it
returns carries a primality certificate for each of its primes, and has been
checked, so it can be used in proofs as well as in programs. From a
factorization the library computes divisors, the divisor sums `σ_k`, Euler's
totient, the radical, the decomposition into a squarefree part times a
square, and the Carmichael function, and it certifies multiplicative orders
and primitive roots.

Fermat conjectured that every number `F_k = 2^(2^k) + 1` is prime. Euler
found in 1732 that `641` divides `F_5 = 2^32 + 1`. The function
{name}`Hex.Nat.factor?` finds this factorization:

```lean (name := fermat5)
open Hex Hex.Nat in
#eval match factor? (2 ^ 32 + 1) (Rand.ofSeed 0) with
  | .ok (F, _) => F.raw.factors.map PrimePower.prime
  | .error _ => []
```
```leanOutput fermat5
[641, 6700417]
```

Written out as data, the same factorization proves Euler's result as a
statement about Mathlib's `Nat.primeFactorsList`. Nobody writes this data by
hand: the command `#int_factor`, described in
{ref "hex-int-factor-external"}[Factors found elsewhere], prints it.

```lean
namespace HexIntFactorChapter

def eulerF5 : Hex.Nat.CheckedFactorization (2 ^ 32 + 1) :=
  ⟨⟨2 ^ 32 + 1,
    [⟨1, .small 641⟩,
     ⟨1, .pock 6700417
       [(5927076, 6, .small 2), (6592685, 0, .small 3),
        (1483445, 0, .small 17449)]⟩]⟩,
   rfl, by decide +kernel⟩

example : Nat.primeFactorsList (2 ^ 32 + 1) =
    [641, 6700417] :=
  eulerF5.primeFactorsList_eq
```

The definition of `eulerF5` lists the primes with their exponents and a
certificate for each prime, and `decide +kernel` has Lean's kernel check
them. The theorem {name}`Hex.Nat.CheckedFactorization.primeFactorsList_eq`
then identifies the checked list with Mathlib's. Nothing about how the
factors were found enters the proof. The next section explains the
certificate.

`HexIntFactor` does not depend on Mathlib. Import it to compute, and import
`HexIntFactorMathlib` for the theorems that translate its results into
statements about `Nat.factorization`, `Nat.primeFactorsList`,
`Nat.divisors`, `Nat.totient` and `orderOf` in `ZMod n`.

# Factorizations and their certificates
%%%
tag := "hex-int-factor-certificates"
%%%

A {name}`Hex.Nat.Factorization` is a number, its `subject`, and a list of
entries of type {name}`Hex.Nat.PrimePower`. An entry is an exponent and a
primality certificate from {ref "hex-primality"}[HexPrimality]; the prime of
the entry, {name}`Hex.Nat.PrimePower.prime`, is by definition the number the
certificate is about, so an entry cannot name one prime and certify another.

In `eulerF5` the entry `⟨1, .small 641⟩` is the prime `641` to the first
power. Its certificate `.small 641` says that `641` appears in HexPrimality's
table of the primes below `10^5`. The second entry is `6700417` to the first
power, with a Pocklington certificate: `6700416 = 2^7 · 3 · 17449`, and each
triple gives a witness, the exponent of a prime factor of `6700416` minus
one, and a certificate for that prime factor. The
{ref "hex-primality-certs"}[HexPrimality chapter] describes these
certificates and how they are checked.

{name}`Hex.Nat.checkFactorization` accepts a factorization when the subject
is positive, the primes are strictly increasing, every exponent is positive,
every certificate is accepted by HexPrimality's `checkPrime`, and the product
of the prime powers is the subject. It computes that product against the
subject as a bound and stops as soon as the partial product exceeds it, so a
factorization with an absurd exponent is rejected without computing an
enormous power. A value of type `CheckedFactorization n`
({name}`Hex.Nat.CheckedFactorization`) is a factorization together with
proofs that its subject is `n` and that the checker accepts it. The
arithmetic functions of this chapter take one. The number `1` has the empty
factorization. To factor an integer, factor its absolute value.

Acceptance means more than that the product is right. If a prime `q`
divides the product of the listed prime powers, it divides one of the listed
primes, so it is one of them. The listed primes are therefore all the prime
divisors of the subject, and each exponent is the exact power dividing it:

{docstring Hex.Nat.checkFactorization_primeSupport}

{docstring Hex.Nat.checkFactorization_multiplicity}

Both the product identity and the primality of each listed factor are
needed. `12 = 4 · 3` has the right product with a composite factor, and
`[3]` lists only primes but misses one.

# Finding factorizations
%%%
tag := "hex-int-factor-search"
%%%

{docstring Hex.Nat.factor?}

The search is randomized. The caller supplies the random state, a
`Hex.Rand` from {ref "hex-basic"}[HexBasic], and receives the advanced
state with the result, so a computation is reproducible from its seed. The
`fuel` argument bounds the number of cofactors the search processes and
the work it spends on each; its default, {name}`Hex.Nat.defaultFuel`, is
`4 · ⌊log₂ n⌋ + 32`. Each method also has fixed limits of its own, which
more fuel does not raise.

To display results, this chapter uses a small helper that lists the primes
of a factorization with their exponents. The numbers `2^(2^k) - 1` are
products of Fermat numbers, `2^128 - 1 = F_0 · F_1 · ⋯ · F_6`, and
`factor?` finds all nine prime factors:

```lean
open Hex Hex.Nat

def primePowers {n : Nat} (F : CheckedFactorization n) :
    List (Nat × Nat) :=
  F.raw.factors.map fun e => (e.prime, e.exponent)
```

```lean (name := fermatProduct)
#eval (factor? (2 ^ 128 - 1) (Rand.ofSeed 0)).map
  fun (F, _) => primePowers F
```
```leanOutput fermatProduct
Except.ok [(3, 1), (5, 1), (17, 1), (257, 1), (641, 1), (65537, 1), (274177, 1), (6700417, 1), (67280421310721, 1)]
```

`factor?` first removes the powers of two and divides by the primes in
HexPrimality's table, the primes below `10^5`, and recognizes perfect powers.
For each cofactor that remains, HexPrimality's certificate search tries to
prove it prime, factoring `p - 1` in turn. It may succeed, find a
Miller–Rabin witness that the cofactor is composite, or run out of budget.
If no certificate is found, the cofactor is split by Pollard's rho method
with Brent's cycle detection, then by Pollard's `p - 1` method and the
elliptic curve method (ECM), and both pieces are processed again. The search
is not trusted: the result is accepted only when the checker of the previous
section accepts it. The work is in finding a factor. Rho is expected to find
a prime factor `p` after about `√p` steps. Pollard's `p - 1` method and ECM
can find much larger factors when `p - 1`, or the order of a random elliptic
curve modulo `p`, is a product of small primes, and the default bounds on
those primes are small.

## When the search stops
%%%
tag := "hex-int-factor-partial"
%%%

The bounded search may stop before it finds a complete factorization. When `factor?` fails, its
{name}`Hex.Nat.FactorFailure` says why. The reason
{name}`Hex.Nat.FactorStop` is `zero` when asked to factor `0`, which has no
factorization, and `incomplete` when the budget ran out. A third reason,
`rejected`, means that the checker refused what the search produced; it
indicates a bug in the search, not a lack of budget. The failure also returns
the advanced random state, so a retry does not repeat the same random
choices.

{name}`Hex.Nat.factorPartial?` returns what was found so far as a
{name}`Hex.Nat.CheckedPartialFactorization`: certified prime powers and a
`residual` whose product with them is the subject. Nothing is claimed about
the residual, which may be prime, composite, or `1`, and may contain
further powers of a listed prime. Asked to factor `2^256 - 1`, which is
`2^128 - 1` times `F_7`, with a fuel of 4, the search finds eight of the nine
primes of `2^128 - 1` and leaves the residual `67280421310721 · F_7`:

```lean (name := partialSearch)
#eval (factorPartial? (2 ^ 256 - 1) (Rand.ofSeed 0)
    (fuel := 4)).map fun (F, _) =>
  (F.raw.factors.map PrimePower.prime, F.raw.residual)
```
```leanOutput partialSearch
Except.ok ([3, 5, 17, 257, 641, 65537, 274177, 6700417], 22894341011050090868949881974522315437050433829130497)
```

With the default fuel the search factors `67280421310721` as well and stops
with residual `F_7 = 2^128 + 1`. The smaller prime factor of `F_7` has
seventeen digits, so rho would need about `10^8` steps, far beyond its
default allocation, and `p - 1` is not smooth enough for the default bounds.
The search runs out; on `F_7` alone this takes about seventeen seconds
(see {ref "hex-int-factor-limits"}[Costs and limits]). The section {ref "hex-int-factor-external"}[Factors found elsewhere] completes
this factorization.

{docstring Hex.Nat.checkPartial_prod}

A partial factorization with residual `1` is a complete one, without
checking it again:

{docstring Hex.Nat.checkFactorization_of_checkPartial}

For numbers of the form `b^n ± 1`, {name}`Hex.Nat.factorPower?` first
splits the number into values of cyclotomic polynomials, using
`b^n - 1 = ∏ Φ_d(b)` over the divisors `d` of `n`, and for `b^n + 1` the
divisors of `2n` that do not divide `n`. It then factors the pieces, which
are often much smaller than the whole number, although `2^128 + 1 = Φ_256(2)`
is a single piece.

## Square forms
%%%
tag := "hex-int-factor-squfof"
%%%

Shanks's square form factorization (SQUFOF) is another way to split numbers
below `2^64`. It can be much faster than rho on a product of two primes of
similar size, where rho is slowest because the smaller factor is large, but
its bounded search can also fail. It is not used by default. The argument `squfof := .first limits` tries it before
rho, on every composite the search meets, and `squfof := .rescue limits`
tries it only after the other methods fail. The limits bound the number of
multipliers tried, the number of steps for each, and the memory used. This 56-bit number has
two factors that differ by about 19%:

```lean (name := squfofComplete)
#eval (factor? 40249308338448479
    (Rand.ofSeed 0)
    (squfof := .first
      { multipliers := 2, steps := 65536 })).map
  fun (F, _) => (primePowers F, totient F)
```
```leanOutput squfofComplete
Except.ok ([(184185251, 1), (218526229, 1)], 40249307935737000)
```

For this number and for two close 32-bit primes, the report
`reports/hex-int-factor-squfof.md` measures complete factorization about six
to nine times faster with SQUFOF first than without it. Factors just above
the range of trial division are found faster by rho.

## Proving large numbers prime
%%%
tag := "hex-int-factor-ecm"
%%%

Importing `HexIntFactor` also strengthens HexPrimality's tactics. A
Pocklington certificate for `p` needs a partial factorization of `p - 1`.
When HexPrimality's own search for one runs out, `primality` tries again
with the search of this library, and `primality?` tries again with
{name}`Hex.Nat.ecmFactorSearch`, a two-stage elliptic curve method that can
find a large prime factor of `p - 1` out of reach of rho. The
{ref "tutorial-field-primes"}[field-prime tutorial] proves the field primes
of secp256k1, P-384 and Curve448 prime this way. Writing
`primality? (factor := Hex.Nat.ecmFactorSearch)` selects the elliptic curve
search directly, with its arguments under the caller's control.

{docstring Hex.Nat.ecmFactorSearch}

The default bounds are `b₁ = 32768` for the first stage and `b₂ = 524288`
for the second, with at most 64 curves for each number to be split. With
bounds above `524288` and `4194304` respectively the elliptic curve stages
are skipped, and more than 64 curves are not used. The first stage of a
curve and its second stage each count as one attempt against the tactic's
`maxAttempts`, which is shared with the rest of the certificate search. For
example `primality? (factor := Hex.Nat.ecmFactorSearch (curves := 16))` uses
fewer curves, and `Hex.Nat.ecmFactorSearch (trace := true)` reports what
each curve found.

# Arithmetic from a factorization
%%%
tag := "hex-int-factor-arithmetic"
%%%

Once a number is factored, its arithmetic functions are given by the usual
formulas in the primes and exponents, and none of them searches. Euler
proved in 1772 that `2^31 - 1` is prime, so that `2^30 · (2^31 - 1)` is a
perfect number: the sum of its divisors, `σ_1`, is twice the number.

```lean (name := perfect)
def perfect : Nat := 2 ^ 30 * (2 ^ 31 - 1)

#eval (factor? perfect (Rand.ofSeed 0)).map fun (F, _) =>
  (primePowers F, numDivisors F,
    sigma F 1 == 2 * perfect, totient F)
```
```leanOutput perfect
Except.ok ([(2, 30), (2147483647, 1)], 62, true, 1152921503533105152)
```

{name}`Hex.Nat.numDivisors` is the number of divisors, `∏ (eᵢ + 1)`;
{name}`Hex.Nat.sigma` `F k` is the sum of the `k`th powers of the divisors;
{name}`Hex.Nat.totient` is Euler's `φ`; and {name}`Hex.Nat.radical` is the
product of the distinct primes. These are evaluated from the prime powers,
one term per prime. {name}`Hex.Nat.divisors` generates all the divisors and
sorts them into increasing order, so for `D` divisors it takes
`O(D log D)` comparisons.

{name}`Hex.Nat.squareDivisor` is the largest `d` such that `d^2` divides
`n`, and {name}`Hex.Nat.squarefreePart` is `n / d^2`; they come from halving
the exponents and from their parities. For the perfect number above they are
`2^15` and `2^31 - 1`.

{docstring Hex.Nat.squarefreePart_mul_square}

{docstring Hex.Nat.squareDivisor_spec}

# Orders and primitive roots
%%%
tag := "hex-int-factor-orders"
%%%

For `n > 1` and `a` prime to `n`, the order of `a` modulo `n` is the least
`m > 0` with `a^m ≡ 1 (mod n)`.
Knowing a candidate `m` is not enough to check it, since a proper divisor of
`m` might work too. With the factorization of `m` it suffices to check that
`a^m ≡ 1` and that `a^(m/q) ≢ 1` for each prime `q` dividing `m`. An
{name}`Hex.Nat.OrderCert` records `a`, `n`, `m` and a factorization of `m`,
and {name}`Hex.Nat.checkOrder` makes these checks.

The "minimal standard" random number generator of Park and Miller multiplies
by `16807 = 7^5` modulo the prime `2^31 - 1`. From any nonzero seed it
returns to its starting value only after `2^31 - 2` steps, because `16807` has order `2^31 - 2`, that
is, it is a primitive root. Every prime factor of
`2^31 - 2 = 2 · 3^2 · 7 · 11 · 31 · 151 · 331` is in the table, so the
certificate is short:

```lean
def minstd : OrderCert where
  base := 16807
  modulus := 2147483647
  order := 2147483646
  orderFac := ⟨2147483646,
    [⟨1, .small 2⟩, ⟨2, .small 3⟩, ⟨1, .small 7⟩,
     ⟨1, .small 11⟩, ⟨1, .small 31⟩, ⟨1, .small 151⟩,
     ⟨1, .small 331⟩]⟩

theorem minstd_valid : checkOrder minstd = true := by
  decide +kernel

example : Hex.Nat.orderOf 16807 2147483647 =
    2147483646 := by
  have h := order_eq_of_checkOrder minstd_valid
  dsimp only [minstd] at h
  exact h
```

{docstring Hex.Nat.order_eq_of_checkOrder}

For a prime `p`, {name}`Hex.Nat.isPrimitiveRoot` tests whether `g` has
order `p - 1`, given a certificate that `p` is prime and a factorization of
`p - 1`, and {name}`Hex.Nat.primitiveRoot?` tries `2, 3, 4, …` in turn and
returns the first primitive root with its order certificate. Its last
argument bounds the number of candidates, and it returns `none` when they run
out. The least primitive root modulo `2^31 - 1` is `7`:

```lean (name := leastRoot)
#eval match primeCert? 2147483647 (Rand.ofSeed 0) 64,
    factor? 2147483646 (Rand.ofSeed 0) with
  | .ok (pc, _), .ok (F, _) =>
    (primitiveRoot? pc F 100).map Prod.fst
  | _, _ => none
```
```leanOutput leastRoot
some 7
```

{name}`Hex.Nat.carmichael` computes the Carmichael function `λ(n)`, the
exponent of the group of units modulo `n`, as the least common multiple of
its values on the prime powers. Every unit raised to `λ(n)` is `1`
({name}`Hex.Nat.pow_carmichael`), and the order of every unit divides `λ(n)`
({name}`Hex.Nat.orderOf_dvd_carmichael`). For `561 = 3 · 11 · 17`,
`λ(561) = lcm(2, 10, 16) = 80`, which divides `560`. So `a^560 ≡ 1 (mod 561)`
for every `a` prime to `561`, although `561` is composite: it is the
smallest Carmichael number.

```lean (name := carmichael561)
#eval (factor? 561 (Rand.ofSeed 0)).map fun (F, _) =>
  (divisors F, carmichael F)
```
```leanOutput carmichael561
Except.ok (#[1, 3, 11, 17, 33, 51, 187, 561], 80)
```

# The Mathlib correspondence
%%%
tag := "hex-int-factor-mathlib"
%%%

`HexIntFactorMathlib` states the results of `HexIntFactor` in Mathlib's
terms. It does no searching or checking of its own: each theorem takes a
{name}`Hex.Nat.CheckedFactorization` or an accepted
{name}`Hex.Nat.OrderCert` and identifies the values computed from it with
Mathlib's definitions. With `eulerF5` from the introduction and `minstd`
from the previous section:

```lean
example : Nat.totient (2 ^ 32 + 1) = 640 * 6700416 := by
  rw [← Hex.Nat.totient_eq eulerF5]
  decide +kernel

example : orderOf (16807 : ZMod 2147483647) =
    2147483646 := by
  have h := Hex.Nat.order_eq_of_checkOrder minstd_valid
  dsimp only [minstd] at h
  have e := Hex.Nat.orderOf_natCast
    (a := 16807) (n := 2147483647) (by decide)
  rw [Nat.cast_ofNat] at e
  rw [e, h]
```

The first rewrites Mathlib's totient as the one computed from the
factorization, which the kernel evaluates. The second identifies the order of
`16807` in `ZMod 2147483647` with {name}`Hex.Nat.orderOf`, which the order
certificate determines.

The basic statement is that the exponents of a checked factorization are
Mathlib's `Nat.factorization`:

{docstring Hex.Nat.CheckedFactorization.factorization_eq}

The others have the same shape:
{name}`Hex.Nat.CheckedFactorization.primeFactorsList_eq` for
`Nat.primeFactorsList`, {name}`Hex.Nat.divisors_eq` for `Nat.divisors`,
{name}`Hex.Nat.totient_eq` for `Nat.totient`, {name}`Hex.Nat.sigma_eq` for
the sums of powers of divisors, {name}`Hex.Nat.isSquarefree_iff_squarefree`
for `Squarefree`, and {name}`Hex.Nat.orderOf_natCast` and
{name}`Hex.Nat.orderOf_eq` for `orderOf` in `ZMod n` and its group of units.

# Factors found elsewhere
%%%
tag := "hex-int-factor-external"
%%%

Finding a factor is the hard part of factoring, and checking one is easy.
So a factor found by other software, or taken from the literature, can be
supplied to {name}`Hex.Nat.importFactors`, which certifies it. Morrison and
Brillhart factored `F_7` in 1970 with the continued fraction method. The
search of {ref "hex-int-factor-partial"}[When the search stops] cannot find
their factors, but given them, `importFactors` proves both prime in about a
millisecond:

```lean (name := importF7)
open Hex Hex.Nat in
#eval match importFactors {} (2 ^ 128 + 1)
    ⟨2 ^ 128 + 1,
      [(59649589127497217, 1, none),
       (5704689200685129054721, 1, none)]⟩
    (Rand.ofSeed 0) with
  | .ok r => match r.value with
    | .complete F => some (primePowers F)
    | .partialResult _ => none
  | .error _ => none
```
```leanOutput importF7
some [(59649589127497217, 1), (5704689200685129054721, 1)]
```

```lean
end HexIntFactorChapter
```

A proposal lists candidate factors with positive exponents, and optionally
with primality certificates, in any order and with repetitions. Their
product must divide the subject, and supplied certificates must be valid;
otherwise `importFactors` returns an error. It searches for a certificate
for each factor that lacks one. Factors it cannot certify, and whatever the
proposal leaves unlisted, remain in the residual of a partial factorization;
the result is complete exactly when that residual is `1`. The first argument
bounds the work and the size of the input; by default the subject has at
most 256 bits.

The commands `#int_factor` and `#int_factor_export`, from
`HexIntFactor.Export`, turn a factorization into Lean source. They run the
program `gp` of PARI/GP to find the factors, when it is installed, and
certify them as above; without PARI/GP, or for what PARI/GP leaves
unfactored, they fall back on a short search of their own. In a module that
imports `HexIntFactor.Export`,

```
#int_factor for 2 ^ 32 + 1
```

prints a module defining the factorization of `2^32 + 1` and its checked
form, like `eulerF5` in the introduction, and

```
#int_factor_export MyFactors.F5 cert for 2 ^ 32 + 1
```

writes that module to the new file `MyFactors/F5.lean`, refusing to
overwrite an existing file. Other modules then import `MyFactors.F5` and use
`MyFactors.F5.cert_checked`. The generated module imports only
`HexIntFactor.Replay`, which contains the checker and none of the search, so
it builds without PARI/GP. The commands run only in a batch build, such as
`lake build +MyModule`, and not in the editor; remove the command once its
output has been saved. They accept subjects of at most 256 bits.

# Very large prime factors
%%%
tag := "hex-int-factor-mixed"
%%%

A Pocklington certificate for a prime `p` requires a sufficiently large
factored divisor of `p - 1`. When that is hard to find, elliptic curve
primality proofs ({ref "hex-ecpp"}[HexECPP]) offer another way. The module
`HexIntFactor.Mixed.Replay` defines factorizations,
`Hex.Nat.Mixed.Factorization`, in which each prime carries either a
HexPrimality certificate or an elliptic curve certificate, and
`HexIntFactor.Mixed.Import` imports them, trying elliptic curve certificates
for primes of up to 256 or 512 bits when asked to. The commands
`#int_factor_mixed` and `#int_factor_mixed_export` of
`HexIntFactor.Mixed.Export` produce such factorizations as source, from
supplied factors or from PARI/GP.

`HexIntFactorMathlib.Mixed` provides the same correspondence with
`Nat.factorization` for these factorizations:

{docstring Hex.Nat.Mixed.CheckedFactorization.factorization_eq}

The arithmetic functions of this chapter take the ordinary
{name}`Hex.Nat.CheckedFactorization`.
{name}`Hex.Nat.Mixed.CheckedFactorization.ofLegacy` converts an ordinary
factorization to the mixed form, and
{name}`Hex.Nat.Mixed.CheckedFactorization.toLegacy` converts back when every
prime carries a HexPrimality certificate.

# Costs and limits
%%%
tag := "hex-int-factor-limits"
%%%

Checking a factorization checks each primality certificate and rebuilds
the product with arithmetic bounded by the subject. Checking an order
certificate also computes `a^m mod n`, and `a^(m/q) mod n` for each prime
`q` dividing `m`. Both are cheap next to finding the factorization.

Splitting a number is usually the expensive part: rho is expected to find a
prime factor `p` in about `√p` steps, so the size of the second largest
prime factor matters most, since the largest is left over as the final
cofactor. Each prime found must then be certified, which needs a partial
factorization of `p - 1` and can be expensive in turn. Whether a search
succeeds therefore depends on the factors, on `p - 1` for each of them, on
the seed and on the fuel. When the search fails, supply the factors as in
{ref "hex-int-factor-external"}[Factors found elsewhere].

These times were measured on one core of a shared machine (`chungus2`) on
2026-10-05, one run each, by evaluating the functions in a compiled module:

:::table +header
* * computation
  * result
  * time
* * `factor?` on `2^32 + 1`
  * complete
  * 0.5 ms
* * `factor?` on `2^64 + 1`
  * complete
  * 3 ms
* * `factor?` on `2^128 - 1`
  * complete
  * 4.6 ms
* * `factorPartial?` on `2^128 + 1`
  * no factor
  * 17 s
* * `importFactors` on `2^128 + 1`
  * complete
  * 1.4 ms
:::

# Cross-references
%%%
tag := "hex-int-factor-cross-references"
%%%

* {ref "hex-primality"}[HexPrimality] provides the primality certificates,
  the table of small primes, Pollard's rho and `p - 1` methods, and the
  multiplicative order {name}`Hex.Nat.orderOf`.
* {ref "hex-ecpp"}[HexECPP] provides the elliptic curve primality
  certificates used by the mixed factorizations.
* {ref "hex-basic"}[HexBasic] provides the random state `Hex.Rand`.
