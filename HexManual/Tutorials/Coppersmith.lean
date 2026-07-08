/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexLLL.Basic
import HexBerlekampZassenhaus

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "LLL in cryptanalysis: a toy Coppersmith attack" =>
%%%
tag := "tutorial-coppersmith"
%%%

# The story
%%%
tag := "tutorial-coppersmith-story"
%%%

A courier sends the same templated message every day: a fixed body with
one short field that changes, say a two-digit code. An eavesdropper knows
the template and knows the day's ciphertext, and wants the code.

The message is RSA-encrypted with public exponent `e = 3`. That small
exponent, with no random padding, is the weakness. Write the plaintext as
`m = a + x₀`, where `a` is the known template (as an integer) and `x₀` is
the unknown code, with `0 ≤ x₀ < X` for a small bound `X`. The ciphertext
is `c = m³ mod N`. Everything except `x₀` is public: the modulus `N`, the
exponent `3`, the ciphertext `c`, the template `a`, and the bound `X`.

Knowing that `m³` genuinely wraps around the modulus (`m³ > N`, so `c` is
not just the integer cube of `m`) rules out the trivial cube-root attack.
The unknown `x₀` is a *small root* of a polynomial modulo `N`:
`f(x) = (a + x)³ − c`, and `f(x₀) ≡ 0 (mod N)`. Coppersmith's method finds
small modular roots by lattice reduction, and that is what this page does
with the project's LLL layer. See the {ref "hex-lll"}[HexLLL chapter] for
the reducer itself.

# From a modular root to a lattice
%%%
tag := "tutorial-coppersmith-lattice"
%%%

Expanding, `f(x) = x³ + 3a·x² + 3a²·x + (a³ − c)`, a monic cubic whose
coefficients we reduce modulo `N` to small representatives. The idea due
to Howgrave-Graham turns "small root mod `N`" into "root over the
integers". If we can find another polynomial `g` that also has `x₀` as a
root modulo `N`, but whose coefficients are *small enough* that
`g(x₀)`, evaluated at the small integer `x₀`, is smaller in absolute value
than `N`, then `g(x₀) ≡ 0 (mod N)` forces `g(x₀) = 0` over the integers.
An integer root of a known polynomial is then read off by a search.

Such small-coefficient combinations are exactly the short vectors of a
lattice. Encode a polynomial by its coefficient vector, scaling the
degree-`j` coefficient by `Xʲ` so that "coefficients small after
substituting `x = X·y`" becomes "vector short". The lattice is spanned by
four rows, each a polynomial vanishing at `x₀` modulo `N`: the three
multiples `N`, `N·x`, `N·x²`, and `f` itself.

```
row N       : [ N,     0,      0,       0   ]
row N·x     : [ 0,     N·X,    0,       0   ]
row N·x²    : [ 0,     0,      N·X²,    0   ]
row f       : [ a₀,    a₁·X,   a₂·X²,   X³  ]
```

Reducing this basis with LLL produces a short vector whose polynomial `g`
is a small-coefficient integer combination of the four rows. The
short-vector guarantee is the Lean-proved
{name}`Hex.short_vector_bound_of_size_bound`. The Howgrave-Graham bound
that turns "short enough" into "root over the integers" is classical
number theory, asserted here in prose rather than formalized; this page
demonstrates the computational step, it does not prove the Coppersmith
theorem.

# The attack, end to end
%%%
tag := "tutorial-coppersmith-attack"
%%%

The instance below uses two nine-digit primes, a known template
`a = 55_555_500`, and a two-digit code `x₀ = 42`, hidden inside
`c = m³ mod N`. The attacker uses only the public data `N`, `a`, `c`, and
`X = 100` to rebuild the lattice, reduce it with the exact integer reducer
{name}`Hex.lllNative`, and recover the code.

Every basis row has its degree-`j` column divisible by `Xʲ`, so every
lattice vector does too; de-scaling a reduced row back to integer
coefficients therefore always succeeds. The recovery scans all reduced
rows, de-scales each to a candidate polynomial `g`, searches
`0 ≤ x < X` for an integer root, and accepts the first `x` that also
reproduces the ciphertext. The verification is that the recovered code is
`42`.

```lean
open Hex

namespace TutorialCoppersmith

-- Public data the attacker starts from.
private def N : Nat := 10_000_004_400_000_259
private def X : Nat := 100
private def a : Int := 55_555_500
private def c : Int := 3_100_253_145_270_284

-- Coefficients of f(x) = (a + x)^3 - c, balanced mod N.
private def a0 : Int := Int.bmod (a ^ 3 - c) N
private def a1 : Int := Int.bmod (3 * a ^ 2) N
private def a2 : Int := Int.bmod (3 * a) N

-- The Coppersmith lattice, one polynomial per row,
-- degree-j column scaled by X^j.
private def B : Matrix Int 4 4 :=
  #m[(N : Int), 0,      0,          0;
     0,   N * X,  0,          0;
     0,   0,      N * X * X,  0;
     a0,  a1 * X, a2 * X * X, X * X * X]

-- LLL-reduce at delta = 3/4.
private def reduced : Matrix Int 4 4 :=
  lllNative B (3 / 4) (by grind) (by grind) (by decide)

-- De-scale a reduced row to integer coefficients.
private def descale (r : Vector Int 4) :
    Option (Vector Int 4) :=
  if r[1] % X == 0 && r[2] % (X * X) == 0
      && r[3] % (X * X * X) == 0 then
    some #v[r[0], r[1] / X,
            r[2] / (X * X), r[3] / (X * X * X)]
  else
    none

-- Horner evaluation of a degree-3 integer polynomial.
private def evalPoly (g : Vector Int 4) (x : Int) : Int :=
  ((g[3] * x + g[2]) * x + g[1]) * x + g[0]

-- Scan reduced rows for an integer root that reproduces c.
private def recover : Option Int := Id.run do
  for row in reduced.rows.toArray do
    match descale row with
    | none => pure ()
    | some g =>
      for x in [0:100] do
        if evalPoly g x == 0 && (a + x) ^ 3 % N == c then
          return some x
  return none

-- LLL actually reduced the basis.
#guard lllReduced reduced (3 / 4) (1 / 2) == true

-- The recovered code is 42.
#guard recover == some 42

end TutorialCoppersmith
```

# Scaling up: a real modulus and a factored root
%%%
tag := "tutorial-coppersmith-factor"
%%%

The toy scanned a two-digit code. A real secret is far too large to scan
for, so the recovery has to change in two places. This page runs the same
attack against a genuine 2048-bit RSA modulus, with an unknown field of
about 400 bits, and makes both changes.

First, the lattice grows. In place of the four-row single-shift basis we
take the nine polynomials `N^(2-j)·xⁱ·f(x)ʲ` for `i, j ∈ {0, 1, 2}`: the
multiples of `N²`, of `N·f`, and of `f²`, each shifted by `1`, `x`, and
`x²`. These extra shift polynomials push the recoverable bound up from
about `N^(1/6)` toward `N^(1/3)`, comfortably covering the 400-bit secret.

Second, the root search changes. The reduced short vector is again a
polynomial `g` with `x₀` as an integer root, but `x₀` is now a 120-digit
number and `g` has degree eight; no bounded scan can find the root.
Instead we factor `g` over the integers with {name}`Hex.ZPoly.factorize`
(via the `.factors` accessor), the project's Berlekamp-Zassenhaus
factorizer, and read the secret straight off the linear factor `x - x₀`.
Factoring a degree-eight integer
polynomial, even with its very large coefficients, is instant; the lattice
reduction is the only real cost.

```lean
open Hex

namespace TutorialCoppersmithFactor

-- A 2048-bit RSA modulus N = p * q, with p and q the primes
-- just below 2^1024. Exponent e = 3, no padding.
private def p : Nat := 2 ^ 1024 - 105
private def q : Nat := 2 ^ 1024 - 179
private def N : Nat := p * q

-- The known 1202-bit template a and unknown 400-bit secret
-- x0 give c = (a + x0)^3 mod N. The attacker sees only the
-- public data N, a, c, and the bound X.
private def a  : Int := 3 ^ 758
private def x0 : Int := 2 ^ 399 + 271828182
private def X  : Nat := 2 ^ 400
private def c  : Int := (a + x0) ^ 3 % N

-- Little-endian polynomials: coefficient k is the x^k term.
private abbrev Poly := Array Int

private def mul (u v : Poly) : Poly := Id.run do
  if u.isEmpty || v.isEmpty then return #[]
  let n := u.size + v.size - 1
  let mut r : Poly := Array.replicate n 0
  for i in [0:u.size] do
    for j in [0:v.size] do
      r := r.set! (i + j)
        (r.getD (i + j) 0 + u.getD i 0 * v.getD j 0)
  return r

private def scale (s : Int) (u : Poly) : Poly :=
  u.map (· * s)
private def shift (i : Nat) (u : Poly) : Poly :=
  Array.replicate i 0 ++ u
private def pow (u : Poly) : Nat → Poly
  | 0 => #[1]
  | n + 1 => mul (pow u n) u

-- f(x) = (a + x)^3 - c, balanced mod N with `Int.bmod`.
private def f : Poly :=
  #[Int.bmod (a ^ 3 - c) N, Int.bmod (3 * a ^ 2) N,
    Int.bmod (3 * a) N, 1]

-- Nine rows N^(2-j) * x^i * f(x)^j (j, i in 0,1,2), col k
-- scaled by X^k. Each vanishes at x0 mod N^2; added shift
-- polynomials push the bound from ~N^(1/6) toward N^(1/3),
-- covering a 400-bit root.
private def rows : Array Poly := Id.run do
  let mut rs : Array Poly := #[]
  for j in [0:3] do
    let fj := pow f j
    for i in [0:3] do
      let row := scale ((N : Int) ^ (2 - j)) (shift i fj)
      rs := rs.push
        ((Array.range 9).map fun k => row.getD k 0 * X ^ k)
  return rs

private def B : Matrix Int 9 9 :=
  Matrix.ofFn fun i j => (rows.getD i.val #[]).getD j.val 0

private def reduced : Matrix Int 9 9 :=
  lllNative B (3 / 4) (by grind) (by grind) (by decide)

-- De-scale a reduced row: column k divides by X^k.
private def descale (r : Vector Int 9) : Poly :=
  (Array.range 9).map fun k => r.toArray.getD k 0 / X ^ k

-- The shortest nonzero reduced row, as polynomial g.
private def g : Poly := Id.run do
  let mut best : Poly := #[]
  let mut norm : Int := -1
  for r in reduced.rows.toArray do
    let v := r.toArray
    if v.all (· == 0) then continue
    let nrm : Int :=
      v.foldl (fun s x => s + (x.natAbs : Int)) 0
    if norm < 0 || nrm < norm then
      norm := nrm
      best := descale r
  return best

-- Factor g over Z with Berlekamp-Zassenhaus. The secret is
-- the root of its linear factor x - x0. Scanning x below
-- X ~ 2^400 is hopeless; factoring degree-8 g is instant.
private def recovered : Option Int := Id.run do
  let gz : ZPoly := DensePoly.ofCoeffs g
  for (fac, _) in gz.factors do
    -- Linear factor `p·x + q` has root `-q/p` when `p ∣ q`.
    match fac.toArray with
    | #[q, p] =>
      if p != 0 && q % p == 0 then
        let r := -q / p
        if 0 ≤ r && r < X && (a + r) ^ 3 % N == c then
          return some r
    | _ => pure ()
  return none

-- The modulus is 2048 bits; the secret is about 400 bits.
#guard N > 2 ^ 2047 && N < 2 ^ 2048
#guard x0 > 2 ^ 399

-- LLL reduces the basis; factoring g gives back x0.
#guard lllReduced reduced (3 / 4) (1 / 2) == true
#guard recovered == some x0

end TutorialCoppersmithFactor
```

# Toy versus real
%%%
tag := "tutorial-coppersmith-boundary"
%%%

This tutorial is deliberately staged. The first instance is a minimal
single-shift lattice with a tiny modulus and a bounded root scan; it
recovers roots only up to about `N^(1/6)`. The second keeps the same
skeleton but uses a real 2048-bit modulus, a nine-row lattice that reaches
about `N^(1/4)`, and Berlekamp-Zassenhaus factorization in place of the
scan. Both still assume the attacker knows a bound `X` on the secret and
work with a single polynomial in one unknown.

A production attack pushes the same idea further. It adds still more shift
polynomials `xⁱ·f(x)ʲ` to drive the recoverable bound the rest of the way
to `N^(1/3)`, and moves to multivariate lattices for settings such as
stereotyped-message recovery, partial key exposure, and the Boneh-Durfee
attack on small RSA private exponents. The computational heart, encode the
constraint as a lattice and reduce it, then read the root off the result,
is exactly what ran above.
