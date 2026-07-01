/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGF2.Basic
import HexGF2.Clmul
import HexGF2.Multiply
import HexGF2.Euclid
import HexGF2.Field
import HexGF2.Irreducibility
import HexGF2.RabinSoundness
import HexGF2.CommonIrreducibility

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGF2: packed GF(2) polynomials and GF(2ⁿ) fields" =>
%%%
tag := "hex-gf2"
%%%

# Introduction
%%%
tag := "hex-gf2-intro"
%%%

`HexGF2` represents the polynomial ring `F₂[x]` as 64-bit words and
builds the finite fields `GF(2ⁿ)` on top of it. Because every
coefficient is a single bit, a polynomial over `F₂` is just a
bit-string, and a whole machine word holds 64 coefficients at once.
Addition is then a bitwise XOR, multiplication by `xᵏ` is a bit shift,
and polynomial multiplication reduces to the carry-less product of two
words (the hardware `CLMUL`/`PMULL` instruction). On top of the packed
representation, `HexGF2` adds the Euclidean algorithms, the single-word
and arbitrary-degree field wrappers, and a Lean-checked Rabin
irreducibility test.

`HexGF2` is Mathlib-free and depends only on
{ref "hex-poly"}[`HexPoly`], the generic dense-polynomial library, which
supplies the shared polynomial vocabulary the packed representation is
checked against. See {ref "hex-gf2-cross-references"}[Cross-references].

# The packed word representation
%%%
tag := "hex-gf2-words"
%%%

A `GF2Poly` is an array of 64-bit words carrying a normalization
invariant: bit `j` of word `i` is the coefficient of `x^(64·i + j)`,
and the array stores no trailing zero word, so equal polynomials have
equal word arrays.

{name}`Hex.GF2Poly`

The coefficient and degree accessors read the packed bits back out.
{name}`Hex.GF2Poly.coeff` returns the coefficient of `xⁿ` as a `Bool`,
{name}`Hex.GF2Poly.degree?` returns the degree of a nonzero polynomial,
and {name}`Hex.GF2Poly.degree` defaults the zero polynomial to `0`.

{docstring Hex.GF2Poly.coeff}

{docstring Hex.GF2Poly.degree?}

{docstring Hex.GF2Poly.degree}

The simplest builders are {name}`Hex.GF2Poly.zero`,
{name}`Hex.GF2Poly.one`, {name}`Hex.GF2Poly.ofUInt64` (a single packed
word) and {name}`Hex.GF2Poly.monomial` (the bare monomial `xⁿ`).
Addition is coefficientwise XOR, and the two shift operations multiply
or divide by a power of `x`.

{docstring Hex.GF2Poly.add}

{docstring Hex.GF2Poly.shiftLeft}

# Carry-less multiplication
%%%
tag := "hex-gf2-clmul"
%%%

Polynomial multiplication over `F₂` is *carry-less*: the coefficient of
`xⁿ` in a product is the XOR-parity of the diagonal
`Σᵢ aᵢ · b_{n-i}`, with no carry between bit positions. The library
fixes a pure-Lean reference for the 64-bit carry-less product and a
trusted runtime hook that the compiled backend implements with the
hardware intrinsic.

{docstring Hex.pureClmul}

{docstring Hex.clmul}

The extern is an optimization only: its logical semantics are pinned to
the pure reference, so every proof reasons about {name}`Hex.pureClmul`
and the compiled path merely runs faster.

{docstring Hex.clmul_eq_pureClmul}

Lifting the word-level product to packed polynomials gives
{name}`Hex.GF2Poly.mul` (the `*` of the `Mul GF2Poly` instance). Its
correctness is stated as the carry-less convolution coefficient law,
which `HexGF2Mathlib` is checked against.

{docstring Hex.GF2Poly.coeff_mul_diagonal}

# Division, gcd, and extended gcd
%%%
tag := "hex-gf2-euclid"
%%%

Long division over `F₂` needs no coefficient inversion (the leading
coefficient of any nonzero polynomial is already `1`), so the packed
representation supports a direct shift-and-XOR division.
{name}`Hex.GF2Poly.divMod` returns the quotient and remainder, with the
`Div` and `Mod` instances projecting out each component.

{docstring Hex.GF2Poly.divMod}

The Euclidean algorithm built on `divMod` gives both the plain gcd and
its extended form, which additionally returns the Bézout cofactors.

{docstring Hex.GF2Poly.gcd}

{docstring Hex.GF2Poly.xgcd}

The extended result bundles the gcd together with the two cofactors
satisfying `left · a + right · b = gcd`.

{docstring Hex.GF2Poly.XGCDResult}

# The field wrappers
%%%
tag := "hex-gf2-field"
%%%

Fixing an irreducible modulus turns the packed polynomial ring into a
field. {name}`Hex.GF2n` is the single-word wrapper for `GF(2ⁿ)` with
`n < 64`: an element is one `UInt64` of coefficients, reduced modulo a
monic degree-`n` modulus, and the type carries the irreducibility proof
of that modulus so only genuine fields can be formed.
{name}`Hex.GF2nPoly` is the arbitrary-degree counterpart, backed by a
full `GF2Poly` rather than a single word. Both expose the field
operations (addition, multiplication, inverse, division) and a
square-and-multiply exponentiation {name}`Hex.GF2n.pow`.

# Worked example
%%%
tag := "hex-gf2-worked"
%%%

The first block runs the packed operations: the bit accessors, XOR
addition, the shift, and a gcd.

```lean
open Hex Hex.GF2Poly

namespace HexGF2Chapter

-- A monomial sets exactly one coefficient bit.
#guard (GF2Poly.monomial 5).degree = 5
#guard (GF2Poly.monomial 5).coeff 5 = true
#guard (GF2Poly.monomial 5).coeff 4 = false

-- Addition is XOR, so a polynomial added to
-- itself cancels to zero.
#guard (GF2Poly.monomial 3
          + GF2Poly.monomial 3).isZero = true

-- The leading term governs the degree of a sum.
#guard (GF2Poly.monomial 3
          + GF2Poly.monomial 5).degree = 5

-- Shifting left by k multiplies by x^k.
#guard ((GF2Poly.monomial 1).shiftLeft 3).toWords
         = (GF2Poly.monomial 4).toWords

-- gcd(f, f) = f, up to the monic normalization
-- that holds automatically over F_2.
#guard (GF2Poly.gcd (GF2Poly.monomial 7)
          (GF2Poly.monomial 7)).degree = 7

end HexGF2Chapter
```

The second block works inside the AES field `GF(2⁸)`, presented by the
Rijndael modulus `x⁸ + x⁴ + x³ + x + 1` (the word `0x1B` above the
leading `x⁸`). The irreducibility of that modulus is the committed
theorem {name}`Hex.GF2Poly.aes_modulus_irreducible`, so the field type
typechecks. The byte `0x53` and its inverse `0xCA` are the standard AES
worked pair.

```lean
open Hex

namespace HexGF2Chapter

abbrev AES : Type :=
  GF2n 8 0x1B (by decide) (by decide)
    GF2Poly.aes_modulus_irreducible

def aes (w : UInt64) : AES := GF2n.reduce w

-- 0x53 and 0xCA are inverse bytes in AES's GF(2^8),
-- so their product is 1.
#guard ((aes 0x53) * (aes 0xCA)).val = 1
#guard ((aes 0x53)⁻¹).val = 0xCA

end HexGF2Chapter
```

# Rabin irreducibility
%%%
tag := "hex-gf2-irreducible"
%%%

Forming a field requires a proof that the modulus is irreducible, and
`HexGF2` produces those proofs from an executable Rabin test rather
than by trusting a table. Irreducibility is phrased directly on the
packed model.

{docstring Hex.GF2Poly.Irreducible}

{docstring Hex.GF2Poly.rabinTest}

The soundness theorem lifts a passing Boolean test to the propositional
predicate, so a `true` result is a genuine proof of irreducibility, not
a runtime assertion.

{docstring Hex.GF2Poly.rabinTest_imp_irreducible}

For moduli whose degree makes the direct test expensive, the library
also commits machine-checked certificates: a
{name}`Hex.GF2Poly.IrreducibilityCertificate` packages the
Frobenius-residue chain and Bézout witnesses, and
{name}`Hex.GF2Poly.checkIrreducibilityCertificate` verifies one with
`checkIrreducibilityCertificate_imp_irreducible` as its soundness
target. The committed cryptographic moduli (the AES modulus and its
siblings) are proved this way, none of them through `native_decide`.

{docstring Hex.GF2Poly.aes_modulus_irreducible}

# Cross-references
%%%
tag := "hex-gf2-cross-references"
%%%

Where `HexGF2` fits in the executable DAG:

* {ref "hex-poly"}[`HexPoly`] is the only dependency: it provides the
  generic dense-polynomial vocabulary against which the packed
  representation's arithmetic and Euclidean laws are stated. `HexGF2`
  specializes that theory to the single-bit-coefficient case where the
  packed word layout and carry-less multiply apply.
* `HexGF2` is consumed by the finite-field constructors that build on
  it (the packed characteristic-two entries of the `GFq` constructors),
  which reuse its `GF2n`/`GF2nPoly` wrappers and committed
  irreducibility certificates.
* `HexGF2` is Mathlib-free. The Mathlib correspondence for the `GF(2ⁿ)`
  field theory is provided by the `*Mathlib` counterparts of the
  libraries that build on it, not by this library.
