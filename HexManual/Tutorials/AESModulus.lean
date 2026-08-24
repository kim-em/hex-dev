/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBerlekamp
import HexGF2

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Why the AES modulus works" =>
%%%
tag := "tutorial-aes-modulus"
%%%

# The story
%%%
tag := "tutorial-aes-modulus-story"
%%%

The {ref "tutorial-aes-field"}[AES byte arithmetic tutorial] builds the
field `GF(2⁸)` as the quotient of `𝔽₂[x]` by the Rijndael modulus

```
x⁸ + x⁴ + x³ + x + 1
```

and leans on one theorem to do it: the modulus is irreducible over `𝔽₂`.
Without that fact the quotient is only a ring, some nonzero bytes have no
inverse, and the S-box construction collapses. That tutorial takes the
theorem as given. This one earns it.

The machinery is {ref "hex-berlekamp"}[`HexBerlekamp`]'s Rabin
irreducibility test: an executable criterion, a replayable certificate,
and a soundness theorem that turns a passing check into a proof. The plan
is to run the test on the modulus, run it on a plausible-looking impostor
that fails, inspect the certificate the test leaves behind, and finish
with the kernel-checked irreducibility theorem the AES construction needs.

# The modulus as a dense polynomial
%%%
tag := "tutorial-aes-modulus-poly"
%%%

`HexBerlekamp` works over {name}`Hex.FpPoly`, the dense polynomial type
with `ZMod64 p` coefficients from {ref "hex-poly-fp"}[`HexPolyFp`]. For
`p = 2` a coefficient is a bit, and the Rijndael modulus is nine of them,
listed from the constant term up.

```lean
open Hex

namespace AESModulusTutorial

/-- The Rijndael modulus `x⁸ + x⁴ + x³ + x + 1` over
`𝔽₂`, coefficients from the constant term up. -/
def m : FpPoly 2 := #p[1, 1, 0, 1, 1, 0, 0, 0, 1]

theorem m_monic : DensePoly.Monic m := by rfl

-- Reading the coefficients as bits recovers the word
-- 0x11B; its low byte 0x1B is exactly how the AES
-- tutorial passes this modulus to the packed field
-- type, with the leading x⁸ implicit.
#guard (m.toArray.toList.map ZMod64.toNat).foldr
    (fun b acc => acc * 2 + b) 0 == 0x11B

end AESModulusTutorial
```

The monicity proof is by `rfl` because the leading coefficient is
literally the bit `1`; every test and certificate below takes it as an
argument, since Rabin's criterion is stated for monic polynomials.

# What goes wrong without irreducibility
%%%
tag := "tutorial-aes-modulus-zero-divisors"
%%%

Before certifying the real modulus, it is worth seeing concretely what a
bad one does. Take `x⁸ + 1`, which differs from the Rijndael modulus in
three bits and looks just as plausible. Over `𝔽₂` it is `(x + 1)⁸`, about
as far from irreducible as a degree-eight polynomial can be.

```lean
open Hex

namespace AESModulusTutorial

/-- The impostor `x⁸ + 1`, which over `𝔽₂` is
`(x + 1)⁸`. -/
def r : FpPoly 2 := #p[1, 0, 0, 0, 0, 0, 0, 0, 1]

theorem r_monic : DensePoly.Monic r := by rfl

def sq (f : FpPoly 2) : FpPoly 2 := f * f

-- Squaring x + 1 three times really gives x⁸ + 1.
#guard sq (sq (sq #p[1, 1])) == r

/-- `(x + 1)⁴`, a nonzero residue modulo `x⁸ + 1`. -/
def u : FpPoly 2 := #p[1, 0, 0, 0, 1]

-- u has degree 4, so it is its own remainder: as a
-- residue modulo x⁸ + 1 it is not zero.
#guard FpPoly.modByMonic r u r_monic == u

-- Yet u · u reduces to zero: u is a zero divisor.
#guard (FpPoly.modByMonic r (u * u) r_monic).isZero

end AESModulusTutorial
```

A quotient with zero divisors is not a field, and the failure is not
abstract: `u` would be a byte with no multiplicative inverse, and the
S-box's inversion stage would have nothing to send it to. Irreducibility
of the modulus is exactly the condition that rules this out, for every
nonzero residue at once.

# Rabin's criterion
%%%
tag := "tutorial-aes-modulus-rabin"
%%%

The classical fact behind the test is that `X^(2^k) - X` is the product
of all monic irreducible polynomials over `𝔽₂` whose degree divides `k`.
Rabin's criterion reads that fact twice. A monic `f` of degree `n` is
irreducible over `𝔽₂` exactly when

* `f` divides `X^(2^n) - X`, so every irreducible factor of `f` has
  degree dividing `n`; and
* `gcd(f, X^(2^d) - X) = 1` for every maximal proper divisor `d` of `n`,
  so no factor has degree strictly smaller than `n`.

For `n = 8` the divisor lattice collapses pleasantly: the proper divisors
of `8` are `1`, `2`, and `4`, and every one of them divides `4`, so a
single gcd check at `d = 4` covers them all.

```lean
open Hex

namespace AESModulusTutorial

-- One maximal proper divisor, so one gcd leg.
#guard Berlekamp.maximalProperDivisors 8 == [4]

-- The Rijndael modulus passes both legs.
#guard Berlekamp.rabinTest m m_monic
#guard Berlekamp.rabinDividesTest m m_monic
#guard Berlekamp.rabinWitnesses m m_monic == [(4, true)]

-- The impostor fails both.
#guard Berlekamp.rabinTest r r_monic == false
#guard Berlekamp.rabinDividesTest r r_monic == false
#guard Berlekamp.rabinWitnesses r r_monic
    == [(4, false)]

end AESModulusTutorial
```

The impostor's failures are instructive. `X^(2⁸) - X` is square-free, so
the eightfold repeated factor `(x + 1)⁸` cannot divide it: the divides
leg fails. And `x + 1` divides both `x⁸ + 1` and `X^(2⁴) - X`, so the gcd
at `d = 4` is not a unit: the coprimality leg fails too. A polynomial
that is merely *reducible* but square-free with a low-degree factor would
pass the first leg and fail only the second; this one fails everything.

# The certificate
%%%
tag := "tutorial-aes-modulus-certificate"
%%%

Running {name}`Hex.Berlekamp.rabinTest` costs repeated Frobenius steps
and a gcd. That is cheap for a compiled program and expensive for a proof
checker, so `HexBerlekamp` splits the work: an untrusted generator runs
the test once in compiled code and writes down enough intermediate data
that *checking* becomes easy. The data is a
{name}`Hex.Berlekamp.IrreducibilityCertificate`: the chain of Frobenius
powers `X^(2^k) mod f` for `k = 0, …, n`, plus one Bezout witness per
maximal proper divisor, a pair `(left, right)` with
`left · f + right · (X^(2^d) - X mod f) = 1`. The Bezout identity is the
point: verifying that a gcd *is* `1` requires re-running the Euclidean
algorithm, but verifying a Bezout combination is two multiplications and
an addition, and it is just as conclusive.

```lean
open Hex

namespace AESModulusTutorial

/-- The Rabin certificate for the modulus, built by the
compiled generator. -/
def cert? : Option Berlekamp.IrreducibilityCertificate :=
  Berlekamp.buildIrreducibilityCertificate? m m_monic

#guard cert?.isSome

-- Nine Frobenius powers: X^(2^k) mod m for k = 0..8.
#guard (cert?.map fun c => c.powChain.size) == some 9

-- One Bezout witness, for the single divisor 4.
#guard (cert?.map fun c => c.bezout.size) == some 1

-- The checker accepts the generated certificate.
#guard (cert?.map fun c =>
  Berlekamp.checkIrreducibilityCertificate m m_monic c)
    == some true

end AESModulusTutorial
```

{name}`Hex.Berlekamp.checkIrreducibilityCertificate` recomputes each pow
chain entry by one Frobenius step from its predecessor, reads the divides
leg off the last entry (which must reduce to `X mod f`), and replays each
Bezout identity. The generator carries no soundness proof of its own and
needs none: a wrong certificate makes the checker return `false`, never a
false pass.

# From a Boolean to a theorem
%%%
tag := "tutorial-aes-modulus-theorem"
%%%

Everything so far is a `#guard`: evaluated when this manual builds, by
the same compiled code any caller would run, but checked by the
evaluator rather than the kernel. The last step promotes the passing
check to a kernel-checked theorem, using the `irreducibility` elaborator
from {ref "hex-berlekamp"}[`HexBerlekamp`].

```lean
open Hex

namespace AESModulusTutorial

/-- Kernel-checked: the Rijndael modulus is irreducible
over `𝔽₂`. -/
theorem m_irreducible : FpPoly.Irreducible m :=
  irreducibility m

-- The tactic form closes the same goal.
example : FpPoly.Irreducible m := by irreducibility

end AESModulusTutorial
```

What happens under `irreducibility m` is the certifying pattern in
miniature. At elaboration time the compiled generator produces the
certificate from the previous section; the elaborator then emits a proof
term applying the soundness theorem to the certificate *as reified
literal data*. The kernel never runs the generator, the Frobenius
exponentiation, or the extended Euclidean algorithm. What it checks is
that the certificate check reduces to `true` on the literals, and the
soundness theorem, proved once in the library as
{name}`Hex.Berlekamp.checkIrreducibilityCertificate_imp_irreducible`
(resting on {name}`Hex.Berlekamp.rabinTest_imp_irreducible`), turns that
reduction into {name}`Hex.FpPoly.Irreducible`. The trusted surface is the
small checker and its proof; the search that found the certificate is
outside it. No `native_decide` is involved anywhere.

{name}`Hex.FpPoly.Irreducible` itself says exactly what the zero-divisor
section needed: `m` is nonzero, and any factorization `a * b = m` has a
constant on one side. That is the hypothesis under which the quotient
`𝔽₂[x] / (m)` has inverses for all nonzero residues.

# Back to the AES field
%%%
tag := "tutorial-aes-modulus-aes"
%%%

The {ref "tutorial-aes-field"}[AES tutorial]'s field type is built on the
committed theorem {name}`Hex.GF2Poly.aes_modulus_irreducible`, which
lives in {ref "hex-gf2"}[`HexGF2`] and is stated for the *packed*
polynomial type `GF2Poly`, where a polynomial over `𝔽₂` is machine words
of bits rather than an array of `ZMod64 2` coefficients. That statement
is proved by exactly the pipeline this page just walked through, on the
packed representation: a committed certificate with the same shape (a
Frobenius pow chain and one Bezout witness at `d = 4`) is replayed by
{name}`Hex.GF2Poly.checkIrreducibilityCertificate` in the kernel, and
{ref "hex-gf2-irreducible"}[the packed Rabin soundness theorem] lifts the
passing check to irreducibility. Same criterion, same certificate
discipline, two representations: the dense form here is where the
general factorization machinery operates for any prime `p`, and the
packed form is what the AES field type consumes at speed.

So the debt is paid twice over. The byte arithmetic of the first
tutorial rests on an irreducibility theorem, and that theorem is not a
table lookup or a trusted comment: it is a replayed certificate, checked
by the kernel, for a criterion whose soundness is itself a Lean theorem.

# Cross-references
%%%
tag := "tutorial-aes-modulus-cross-references"
%%%

* {ref "tutorial-aes-field"}[AES byte arithmetic in GF(2⁸)] is the
  downstream consumer: the field this page's theorem legitimizes.
* {ref "hex-berlekamp"}[`HexBerlekamp`] documents the Rabin test, the
  certificate checker, and the Berlekamp factorization this page did not
  need.
* {ref "hex-poly-fp"}[`HexPolyFp`] is the dense prime-field polynomial
  layer the test runs on, including the quotient construction whose
  field laws take irreducibility as a hypothesis.
* {ref "hex-gf2-irreducible"}[Rabin irreducibility in `HexGF2`] is the
  packed counterpart, where the committed AES certificate lives.
* {ref "factor-tactics"}[The factor tactics] chapter documents the
  `factor_poly` and `irreducibility` elaborators in full, including the
  Mathlib-facing forms.
