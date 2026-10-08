/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import VersoManual
public import HexModular
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic

import all HexModular.Crt
import all HexModular.CrtPlan
import all HexModular.Euclid
import all HexModular.Loop
import all HexModular.Recon
import all HexModular.SymMod

public meta import HexModular.CrtPlan
public meta import HexModular.Recon
public meta import HexModular.SymMod

public section

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexModular: Chinese remaindering and rational reconstruction" =>
%%%
tag := "hex-modular"
%%%

# Introduction
%%%
tag := "hex-modular-intro"
%%%

Many exact computations with integers and rationals are done fastest by not
doing them over the integers at all. The multimodular method computes the
answer modulo several primes, where every number fits in a machine word,
combines the images by the Chinese remainder theorem into the answer modulo
the product of the primes, and reads off the integer or rational answer from
that residue. `HexModular` provides the last two steps: Chinese remaindering,
incrementally or for many moduli at once, and rational reconstruction, which
recovers a fraction `p / q` from the residue of `p · q⁻¹`. It also provides the
loop that adds primes until a caller's test accepts the result.

The harmonic number `H₅₀ = 1 + 1/2 + ⋯ + 1/50` is a fraction whose numerator
has 74 bits and whose denominator has 72. Modulo a prime `p > 50` it can be
computed with arithmetic on numbers below `p`: keep `H_k` as a fraction
`a / b` of residues, and at the end multiply by `b^(p-2)`, which is the
inverse of `b` by Fermat's little theorem:

```lean
open Hex.Modular

namespace HexModularChapter

def harmonicMod (n p : Nat) : Int :=
  let (a, b) := (List.range n).foldl
    (fun (a, b) k =>
      ((a * (k + 1) + b) % p, b * (k + 1) % p))
    (0, 1)
  a * Nat.powMod b (p - 2) p % p
```

Here are the five largest primes below `2^31`. The function `recover` combines
the images of `H_n` modulo the first `j` of them with
{name}`Hex.Modular.Crt.push`, and then asks {name}`Hex.Modular.ratReconWide?`
for a fraction whose numerator, in absolute value, and denominator are both at
most `⌊√((M - 1) / 2)⌋`, where `M` is the product of the primes used:

```lean
def primes : List Nat :=
  [2147483647, 2147483629, 2147483587,
   2147483579, 2147483563]

def recover (n j : Nat) : Option Rat := do
  let c ← (primes.take j).foldlM
    (fun c p => c.push (harmonicMod n p) p) Crt.init
  ratReconWide? c.value c.modulus
```

```lean (name := harmonicFive)
#eval recover 50 5
```
```leanOutput harmonicFive
some (13943237577224054960759 / 3099044504245996706400)
```

This is `H₅₀`, as an exact computation with Lean's `Rat` confirms:

```lean
def harmonic (n : Nat) : Rat :=
  (List.range n).foldl (fun s k => s + 1 / (k + 1 : Rat)) 0

#guard recover 50 5 = some (harmonic 50)
```

With these primes, five suffice and four do not. The product of five is about
`2^155`, so the bound is about `2^77`, which exceeds both parts of `H₅₀`. With three
primes the bound is about `2^46`. `H₅₀` is not within it, and there is a
different fraction within it with the same residue, which reconstruction
duly returns. With four primes there is none:

```lean (name := harmonicFewer)
#eval (recover 50 3, recover 50 4)
```
```leanOutput harmonicFewer
(some (10596404151154 / 65912169239963), none)
```

So a multimodular computation needs a reason to stop: a bound on the size of
the answer, or a check that the answer is right. The section
{ref "hex-modular-loop"}[The multimodular loop] returns to this example with a
bound.

Import `HexModular` to use the library; the Mathlib examples near the end of
this chapter also import `Mathlib.Data.Int.ModEq` and `Mathlib.Data.ZMod.Basic`.
`HexModular` does not depend on Mathlib, and has no Mathlib companion. Its
theorems state congruences with `%` on `Int`, which is how Mathlib defines
`Int.ModEq`, so they can be used in Mathlib proofs directly; see
{ref "hex-modular-mathlib"}[Using the theorems with Mathlib]. Its only
dependency is {ref "hex-arith"}[HexArith], whose extended Euclidean algorithm
uses GMP in compiled code.

# Symmetric representatives
%%%
tag := "hex-modular-symmetric"
%%%

An integer `x` with `|x| < m / 2` is determined by its residue modulo `m`: it
is the representative of the residue in the interval `(-m/2, m/2]`. So
reconstructions in this library return that representative rather than the
usual one in `[0, m)`, and negative answers come out negative.

{docstring Hex.Modular.symMod}

```lean (name := symModEx)
#eval [symMod 17 10, symMod 15 10, symMod (-15) 10]
```
```leanOutput symModEx
[-3, 5, 5]
```

The uniqueness theorem needs the strict inequality `2 |x| < m`. When `m` is
even, `m / 2` and `-m / 2` have the same residue, and the interval keeps only
the first of them:

{docstring Hex.Modular.symMod_unique}

# Chinese remaindering
%%%
tag := "hex-modular-crt"
%%%

The *Sunzi Suanjing*, a Chinese text of the third to fifth century, asks for
a number that leaves remainder 2 when counted by threes, 3 when counted by
fives, and 2 when counted by sevens. A {name}`Hex.Modular.Crt` holds the
answer so far: its modulus, which is the product of the moduli pushed so far,
and the symmetric representative of the solution modulo it. {name}`Hex.Modular.Crt.init` is the
state modulo `1`, and each {name}`Hex.Modular.Crt.push` adds one more
condition:

```lean
def sunzi : Option Crt := do
  let c ← Crt.init.push 2 3
  let c ← c.push 3 5
  c.push 2 7
```

```lean (name := sunziEval)
#eval sunzi.map fun c => (c.value, c.modulus)
```
```leanOutput sunziEval
some (23, 105)
```

{docstring Hex.Modular.Crt}

{docstring Hex.Modular.Crt.push}

The moduli must be pairwise coprime. `push` checks this as it goes, and
returns `none` when the new modulus shares a factor with the product so far,
even when the conditions are consistent: `1 mod 4` and `3 mod 6` are both
satisfied by `9`, but `4` and `6` are not coprime.

```lean
#guard (Crt.init.push 1 4 >>= (·.push 3 6)).isNone
```

## Garner's step

Suppose the state holds `v` modulo `M`, and `r` modulo `m` is pushed, with
`M` and `m` coprime. Let `s` be the inverse of `M` modulo `m`. Then
`δ = symMod ((r - v) s) m` and the new value is `symMod (v + M δ) (M m)`.
Adding a multiple of `M` does not change the residue modulo `M`, and modulo
`m` the sum is `v + (r - v) = r`. This is Garner's mixed-radix step. The
inverse `s` comes from the extended Euclidean algorithm applied to
`M mod m` and `m`, so its operands are no larger than `m`, whatever the size
of `M`. When `m` fits in a word, the other operations (additions,
multiplications by numbers smaller than `m`, and reductions) each take time
linear in the bit length of `M`.

The final reduction is needed. Pushing `1 mod 3` and then `0 mod 2` gives
`δ = 1` and `v + M δ = 4`, which is outside `(-3, 3]`; the stored value is
`-2`:

```lean (name := garnerEval)
#eval (Crt.init.push 1 3 >>= (·.push 0 2)).map
  fun c => (c.value, c.modulus)
```
```leanOutput garnerEval
some (-2, 6)
```

Three theorems describe a successful push. The new modulus is the product,
the new value has the new residue, and it keeps the old residue modulo every
divisor of the old modulus. By induction, the value after a sequence of
pushes has every residue that was pushed.

{docstring Hex.Modular.Crt.push_modulus}

{docstring Hex.Modular.Crt.push_congr_new}

{docstring Hex.Modular.Crt.push_congr_old}

To recover an integer `x`, push residues of `x` until `2 |x|` is less than the
modulus. The value then has the same residue as `x` modulo the whole modulus,
and it is the symmetric representative of that residue, so it is `x` by
`symMod_unique`. The same argument gives the uniqueness of strictly bounded
solutions:

{docstring Hex.Modular.crt_unique}

## Vectors of residues

Recovering a polynomial or a matrix means recovering many integers modulo
the same primes. A `CrtVec k` ({name}`Hex.Modular.CrtVec`) holds `k` values
sharing one modulus. Its {name}`Hex.Modular.CrtVec.push` computes the inverse `s` once and
uses it for every coordinate, so a push costs one extended Euclidean
algorithm whatever `k` is. Here the second coordinate solves `1 mod 3`,
`0 mod 5` and `-1 mod 7`:

```lean
def lanes : Option (CrtVec 2) := do
  let c ← (CrtVec.init 2).push #v[2, 1] 3
  let c ← c.push #v[3, 0] 5
  c.push #v[2, -1] 7
```

```lean (name := lanesEval)
#eval lanes.map fun c => (c.value, c.modulus)
```
```leanOutput lanesEval
some (#v[23, -50], 105)
```

`CrtVec` has the same theorems as `Crt`, for every coordinate, together with
{name}`Hex.Modular.CrtVec.push_congr`, which combines the old and new
residues into one congruence modulo the product, and
{name}`Hex.Modular.CrtVec.eq_of_congr`, the analogue of `crt_unique`.

## Many moduli at once
%%%
tag := "hex-modular-crt-plan"
%%%

When every modulus is known before any residue, the moduli can be prepared
once and used for many reconstructions.
{name}`Hex.Modular.CrtPlan.build?` checks that the moduli are greater than
one and pairwise coprime, and arranges them as the leaves of a balanced
binary tree. Each internal node stores the inverse of the product of its left
subtree modulo the product of its right subtree.
{name}`Hex.Modular.CrtPlan.reconstruct?` then combines the residues from the
leaves up, applying Garner's step at each node with its stored inverse, so it
runs no extended Euclidean algorithm.
{name}`Hex.Modular.CrtPlan.reconstructVec?` does the same for `k` values at
once: its input is an `Array (Vector Int k)` with one vector of residues per
modulus, in the order of the moduli, and it uses each stored inverse for every
coordinate. Both return `none` if the number of residues differs from the
number of moduli, and both check the result against every residue before
returning it.

A plan for the five primes above recovers the same residue of `H₅₀` as the
incremental computation:

```lean
def plan? : Option CrtPlan := CrtPlan.build? primes.toArray

def viaPlan : Option Int := plan?.bind fun plan =>
  plan.reconstruct? (primes.toArray.map (harmonicMod 50))

def viaPush : Option Int :=
  (primes.foldlM (fun (c : Crt) p =>
    c.push (harmonicMod 50 p) p) Crt.init).map (·.value)

#guard viaPlan.isSome
#guard viaPlan = viaPush
#guard (CrtPlan.build? #[6, 10]).isNone
```

The result is the symmetric representative modulo the product of the moduli,
so it recovers every integer that small:

{docstring Hex.Modular.CrtPlan.reconstruct?_eq_candidate}

The incremental form is the one to use when the number of moduli is not known
in advance, because a computation can stop as soon as it has enough. The
section {ref "hex-modular-costs"}[Costs and limits] compares the two.

# Rational reconstruction
%%%
tag := "hex-modular-reconstruction"
%%%

A fraction `p / q` with `q` coprime to `m` has a residue modulo `m`, the
residue of `p · q⁻¹`. For example `2 / 3` is `68` modulo `101`, since
`3 · 68 = 204 = 2 · 101 + 2`. Rational reconstruction goes back: given `a`
and `m` and bounds `P` and `Q`, it looks for `p / q` with

`q a ≡ p (mod m)`, `|p| ≤ P`, `0 < q ≤ Q`.

The algorithm is Wang's. Reduce `a` modulo `m`, and run the extended Euclidean
algorithm on `m` and `a`.
Its rows are remainders `rⱼ = sⱼ m + tⱼ a`, so each satisfies
`tⱼ a ≡ rⱼ (mod m)`, and as the remainders decrease the coefficients `|tⱼ|`
increase. Stop at the first row with `rⱼ ≤ P` and take the candidate
`rⱼ / tⱼ`, which `Rat.divInt` puts in lowest terms with a positive
denominator. {name}`Hex.Modular.euclidUntil` returns that row. For `68` modulo
`101` the remainders are `101, 68, 33, 2`, and the row for `2` has `t = 3`:

```lean (name := euclidEval)
#eval euclidUntil 101 68 7
```
```leanOutput euclidEval
{ r := 2, t := 3 }
```

{docstring Hex.Modular.ratRecon?}

{docstring Hex.Modular.ratReconWide?}

```lean (name := reconEval)
#eval (ratRecon? 68 101 7 7, ratReconWide? 68 101,
  ratReconWide? 33 101)
```
```leanOutput reconEval
(some (2 / 3), some (2 / 3), some (-2 / 3))
```

Since the result is checked before it is returned, it is always a solution:
{name}`Hex.Modular.ratRecon?_congr` gives the congruence,
{name}`Hex.Modular.ratRecon?_bounds` the bounds, and
{name}`Hex.Modular.ratRecon?_den_coprime` shows that the denominator is
coprime to the modulus, so that the fraction really has a residue.

## Uniqueness and completeness

Without a condition relating the bounds to the modulus, a residue can be
the image of several fractions within them. Modulo `101`, both `2 / 3` and
`-23 / 16` reduce to `68`, and both have numerator and denominator at most
`25`:

```lean
#guard ratReconCheck 68 101 25 25 (2 / 3)
#guard ratReconCheck 68 101 25 25 (-23 / 16)
```

The condition is `2 P Q < m`. If `p₁ / q₁` and `p₂ / q₂` both satisfy the
congruence, then `m` divides `p₁ q₂ - p₂ q₁`, whose absolute value is at most
`2 P Q`. So if `2 P Q < m` it is zero and the fractions are equal.
{name}`Hex.Modular.ratReconWide?` chooses `P = Q = ⌊√((m - 1) / 2)⌋`, the
largest equal bounds satisfying the condition.

{docstring Hex.Modular.ratRecon_unique}

Under the same condition the Euclidean algorithm finds the fraction whenever
it exists. The key fact is that `|tⱼ| rⱼ₋₁ ≤ m` for every row, which places
the candidate within the bounds whenever any solution is; see von zur Gathen
and Gerhard, *Modern Computer Algebra*, and Wang, Guy and Davenport,
"P-adic reconstruction of rational numbers" (1982).

{docstring Hex.Modular.ratRecon?_complete}

So `none` from `ratRecon?` with `2 P Q < m` means that no fraction within the
bounds has the residue `a`. In a multimodular computation it usually means
that the modulus is not yet large enough.

## Common denominators

By Cramer's rule, the solution of a linear system `A x = b`, with `A` a
nonsingular square integer matrix and `b` an integer vector, is a vector of
fractions whose common denominator divides the determinant of `A`.
{name}`Hex.Modular.ratReconVec?` reconstructs such a vector, returning the
numerators and the common denominator `d`. It reconstructs the first entry
on its own. For each later entry `aᵢ` it first tries `symMod (d aᵢ) m` as the
numerator, which is one multiplication, and runs a Euclidean reconstruction
only when that numerator is too large. Then it replaces `d` by the least
common multiple of `d` and the new denominator, and scales the numerators
found so far to match. At the end it divides the numerators and `d` by their
common greatest common divisor. Modulo `101`, `51` is `1 / 2`
and `76` is `1 / 4`:

```lean
def halfQuarter : Vector Int 2 := #v[51, 76]
```

```lean (name := vecEval)
#eval ratReconVec? halfQuarter 101 2 4
```
```leanOutput vecEval
some (#v[2, 1], 4)
```

The bound `Q` now bounds the common denominator, and `P` the numerators over
that common denominator, not those of each fraction in lowest terms.
Completeness needs the numerators and the denominator together to have
greatest common divisor `1`, although a single numerator may share a factor
with `d`:

{docstring Hex.Modular.ratReconVec?_complete}

## Without bounds

Some computations have no useful bound on the answer, or only one far larger
than the answer usually is. Monagan's maximal quotient rational
reconstruction needs none. If `p / q` has residue `a` and `|p| q` is much
smaller than `m`, then the quotient in the step of the Euclidean algorithm
after the row for `p / q` is about `m / (|p| q)`, usually much larger than the
other quotients. {name}`Hex.Modular.ratReconMaxQuot?` takes its candidate
from the row just before the step with the largest quotient. Here `m = 2^40 - 87` and `a` is the residue of
`123456789 / 2`. The bound `√(m / 2)` is `741455`, so `ratReconWide?` fails,
while the maximal quotient finds the fraction:

```lean (name := maxQuotEval)
#eval (ratReconWide? 549817542239 1099511627689,
  ratReconMaxQuot? 549817542239 1099511627689)
```
```leanOutput maxQuotEval
(none, some (123456789 / 2))
```

This is a heuristic, and its theorem promises only the congruence. A
computation using it needs its own check of the answer.

{docstring Hex.Modular.ratReconMaxQuot?_congr}

# The multimodular loop
%%%
tag := "hex-modular-loop"
%%%

{name}`Hex.Modular.crtLoop` runs the multimodular method. It takes a function
computing the image of the answer modulo a given modulus, a test deciding
whether the accumulated residues determine the answer, a supply of moduli,
and fuel:

{docstring Hex.Modular.crtLoop}

The image function returns `none` for a modulus that does not work. For a
determinant computed by elimination, that is a prime modulo which no
invertible pivot can be found. The loop skips such a modulus, and also one
that `push` rejects because it is not coprime to those before it. Every
modulus inspected, used or skipped, consumes one unit of fuel. The test is
called after each successful push, and returns `none` to ask for another
modulus or `some` of the answer, which the loop returns.

For `H_n` a bound gives a test. The least common multiple `L` of
`1, …, n` is a common denominator of the terms, so the denominator of `H_n`
divides `L`, and its numerator is at most `n L` since `H_n ≤ n`. So once the
modulus exceeds `2 · n L · L`, `ratRecon?` with these bounds must find
`H_n`. The image function rejects primes `p ≤ n`, at which some term `1 / k`
has no residue:

```lean
def lcmUpTo (n : Nat) : Nat :=
  (List.range n).foldl (fun l k => Nat.lcm l (k + 1)) 1

def harmonicLoop (n : Nat) : Option Rat :=
  let Q : Int := lcmUpTo n
  let P := n * Q
  crtLoop
    (fun p => if p ≤ n then none
      else some #v[harmonicMod n p])
    (fun s => if 2 * P * Q < s.modulus then
      ratRecon? s.value[0] s.modulus P Q else none)
    primes.toArray primes.length
```

```lean (name := loopEval)
#eval harmonicLoop 50
```
```leanOutput loopEval
some (13943237577224054960759 / 3099044504245996706400)
```

The test first passes after the fifth prime. The theorem about the loop
identifies the initial segment of the supply that it used and the state on
which the test returned the result; a {name}`Hex.Modular.CrtTrace` records
how that state was reached from the images.

{docstring Hex.Modular.crtLoop_trace}

{docstring Hex.Modular.CrtTrace.congr}

The correctness of a particular use combines these with the theorems about
the test. For `harmonicLoop`, write `H_n = N / D` and suppose every image is
the residue of `H_n`. Let `M` be the product of the primes used, which are
larger than `n` and so coprime to `D`, and let `u` be an inverse of `D` modulo
`M`. Then `CrtTrace.congr`, applied to the vector `#v[N * u]`, shows that the
final value `v` is congruent to `N u` modulo `M`, so `D v ≡ N`. This is the
congruence hypothesis of `ratRecon?_complete`, which then shows that the
result is `H_n`.

# Proofs about particular values
%%%
tag := "hex-modular-kernel"
%%%

Lean's kernel can evaluate {name}`Hex.Modular.symMod` and
{name}`Hex.Modular.Crt.push`. In compiled code `push` uses GMP's extended
Euclidean algorithm, and in the kernel it uses a version written in Lean
that is proved equal to it. So `decide +kernel` proves statements about
particular Chinese remainder computations:

```lean
example : sunzi.map (·.value) = some 23 := by
  decide +kernel
```

The definition of `ratRecon?` is deliberately not exposed to the kernel,
which would otherwise have to run the Euclidean algorithm. Its check
{name}`Hex.Modular.ratReconCheck` is exposed, and together with
`ratRecon?_complete` it proves what `ratRecon?` returns without running the
Euclidean algorithm in the kernel:

```lean
example : ratRecon? 68 101 7 7 = some (2 / 3) :=
  ratRecon?_complete (by decide)
    (by decide +kernel) (by decide +kernel)
```

# Using the theorems with Mathlib
%%%
tag := "hex-modular-mathlib"
%%%

Mathlib defines `a ≡ b [ZMOD n]` to mean `a % n = b % n`, so the congruence
theorems of this library are already statements about `Int.ModEq`:

```lean
example {c c' : Crt} {r : Int} {m : Nat}
    (h : c.push r m = some c') :
    c'.value ≡ r [ZMOD m] :=
  Crt.push_congr_new h
```

The theorems about reconstruction translate to `ZMod m`. By
`ratRecon?_den_coprime`, the denominator of the fraction found by `ratRecon?`
is a unit in `ZMod m`, and the image of the fraction there is the residue it
was reconstructed from:

```lean
example {a P Q : Int} {m : Nat} {x : Rat}
    (h : ratRecon? a m P Q = some x) :
    (x.num : ZMod m) * (x.den : ZMod m)⁻¹ = a := by
  have hd : (m : Int) ∣ x.den * a - x.num :=
    Int.dvd_of_emod_eq_zero (ratRecon?_congr h)
  have key := (ZMod.intCast_eq_intCast_iff_dvd_sub
    x.num (x.den * a) m).mpr hd
  push_cast at key
  rw [key, mul_comm (x.den : ZMod m), mul_assoc,
    ZMod.coe_mul_inv_eq_one _ (ratRecon?_den_coprime h),
    mul_one]

end HexModularChapter
```

# Costs and limits
%%%
tag := "hex-modular-costs"
%%%

Write `M` for the number of bits of the accumulated modulus. A push costs one
extended Euclidean algorithm on numbers below the new modulus `m`, and
additions, multiplications and reductions on numbers of `M` bits, each linear
in `M` when `m` fits in a word. Accumulating `k` moduli of one word
each therefore costs `O(k²)` word operations. A `CrtVec` push does the
`M`-bit work once per coordinate and the extended Euclidean algorithm once.
Building a `CrtPlan` checks every pair of moduli for coprimality, which is
`k²` greatest common divisors of words.

Rational reconstruction runs the Euclidean algorithm on numbers of `M` bits
until the remainder is at most `P`, which takes `O(M²)` word operations in
the worst case. A failure may need the whole run, or may be detected when the
first candidate fails the final checks. `ratReconWide?` also computes an
integer square root, and the vector form usually runs one Euclidean algorithm
for the whole vector and a multiplication and reduction for each later
entry. The report
`reports/hex-modular-performance.md` measures these costs. On Fibonacci
inputs, which make the Euclidean algorithm as long as possible, a
reconstruction modulo a number of 262144 bits took about 3 seconds,
about 10 times as long as GMP's extended Euclidean algorithm called from
Python, which is subquadratic; at 512 bits the ratio was 2.6. Accumulating
residues was about three times as fast as the same Garner recurrence in FLINT
called from Python.

These times were measured on one core of a shared machine (`chungus2`) on
2026-10-05, one run each, by the compiled benchmarks in
`bench/HexModular/Bench.lean`. The moduli are prime powers of 23 to 48 bits,
and the plan is built in advance:

:::table +header
* * computation
  * incremental
  * with a plan
* * one value, 1024 moduli
  * 4.0 ms
  * 3.0 ms
* * one value, 4096 moduli
  * 45 ms
  * 32 ms
* * 4096 values, 16 moduli
  * 34 ms
  * 68 ms
:::

A plan saves little for one value, and for many values with few moduli the
incremental `CrtVec` was faster. The plan's advantage is that its inverses
are computed once and reused for every later reconstruction with the same
moduli.

The moduli are natural numbers of any size. Recovering an integer `x` needs
moduli with product `M > 2 |x|`, and recovering a fraction with bounds `P`
and `Q` needs `M > 2 P Q`. A finite supply may not reach the modulus a
computation needs, so `crtLoop` takes fuel and a finite supply and returns
`none` when either runs out; it is up to the caller to supply enough.

# Cross-references
%%%
tag := "hex-modular-cross-references"
%%%

* {ref "hex-arith"}[HexArith] provides the extended Euclidean algorithm used
  by every push.
* {ref "hex-mod-arith"}[HexModArith] provides arithmetic modulo word-sized
  primes, in which the images of a multimodular computation are usually
  computed.
* {ref "hex-poly-fp"}[HexPolyFp] multiplies polynomials with number theoretic
  transforms modulo several primes and combines the results with a
  {name}`Hex.Modular.CrtPlan`.
* `HexModularMatrix` computes determinants with `crtLoop` and solves linear
  systems with `ratReconVec?`.
* {ref "hex-poly-z-gcd"}[HexPolyZGcd] and {ref "hex-mv-gcd"}[HexMvGcd]
  combine the coefficients of polynomial greatest common divisors computed
  modulo several primes with `CrtVec` and `Crt`.
* {ref "hex-mv-hensel"}[HexMvHensel] uses symmetric representatives to read
  integer coefficients from coefficients modulo a prime power.
