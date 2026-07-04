/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexLLL.Basic

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
private def N : Int := 10_000_004_400_000_259
private def X : Int := 100
private def a : Int := 55_555_500
private def c : Int := 3_100_253_145_270_284

-- Least residue of z modulo n, in (-n/2, n/2].
private def centerMod (n z : Int) : Int :=
  let r := ((z % n) + n) % n
  if 2 * r > n then r - n else r

-- Coefficients of f(x) = (a + x)^3 - c, reduced mod N.
private def a0 : Int := centerMod N (a ^ 3 - c)
private def a1 : Int := centerMod N (3 * a ^ 2)
private def a2 : Int := centerMod N (3 * a)

-- The Coppersmith lattice, one polynomial per row,
-- degree-j column scaled by X^j.
private def B : Matrix Int 4 4 :=
  #m[N,   0,      0,          0;
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
        let xi : Int := (x : Int)
        if evalPoly g xi == 0 && (a + xi) ^ 3 % N == c then
          return some xi
  return none

-- LLL actually reduced the basis.
#guard lllReducedInt reduced (3 / 4) (1 / 2) == true

-- The recovered code is 42.
#guard recover == some 42

end TutorialCoppersmith
```

# Toy versus real
%%%
tag := "tutorial-coppersmith-boundary"
%%%

This instance is deliberately small and honest about it. The modulus is
tiny, the lattice is the minimal single-shift construction, and the final
root search is a bounded scan rather than an integer factorization of `g`.
The single-shift lattice recovers roots only up to about `N^(1/6)`, well
short of the `N^(1/3)` that the full method reaches; the chosen `x₀` sits
comfortably inside that margin.

A real attack differs in degree, not in kind. It adds many shift
polynomials `xⁱ·f(x)ʲ` to enlarge the lattice and push the recoverable
bound toward `N^(1/3)`, extracts the integer root of `g` by factoring over
the integers (for which `hex-poly-z` is the project's tool) rather than
scanning, and appears in settings such as stereotyped-message recovery,
partial key exposure, and the Boneh-Durfee attack on small RSA private
exponents. The computational heart, encode the constraint as a lattice and
reduce it, is exactly what ran above.
