/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGF2

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "AES byte arithmetic in GF(2⁸)" =>
%%%
tag := "tutorial-aes-field"
%%%

# The story
%%%
tag := "tutorial-aes-field-story"
%%%

AES does not treat a byte as a number. It treats it as an element of the
finite field with 256 elements, and its two least obvious operations,
`MixColumns` and the S-box, are field multiplication and field inversion.
That is why AES multiplication tables look nothing like ordinary
multiplication: `0x57` times `0x83` is `0xC1`, and `0x57` plus `0x83` is
`0xD4`, which is just their exclusive-or.

This page builds that field with {ref "hex-gf2"}[`HexGF2`], runs the
worked examples from the AES specification through it, and shows that the
answers agree. Everything here is executable: each check below runs when
the manual is built, so the page cannot drift away from the library.

# Bytes as polynomials
%%%
tag := "tutorial-aes-field-bytes"
%%%

Write a byte's eight bits as the coefficients of a polynomial over `𝔽₂`,
least significant bit first. The byte `0x57` is `0b01010111`, so it is

```
x⁶ + x⁴ + x² + x + 1
```

Addition of two such polynomials adds coefficients in `𝔽₂`, where
`1 + 1 = 0`. Coefficientwise addition modulo two is exactly exclusive-or,
so field addition on bytes is the XOR the hardware already has, and every
element is its own additive inverse.

Multiplication is where it stops being free. The product of two degree-7
polynomials has degree up to 14, which no longer fits in a byte, so the
result is reduced modulo a fixed irreducible polynomial of degree 8. AES
fixes the Rijndael modulus

```
x⁸ + x⁴ + x³ + x + 1
```

which `HexGF2` commits as {name}`Hex.GF2Poly.aesModulus`. Reducing modulo
an irreducible is what makes the quotient a *field* rather than merely a
ring: it is what guarantees every nonzero byte has a multiplicative
inverse, which the S-box depends on. That irreducibility is not an
assumption here; it is the committed theorem
{name}`Hex.GF2Poly.aes_modulus_irreducible`, checked by replaying a Rabin
certificate in the kernel. See
{ref "hex-gf2-irreducible"}[Rabin irreducibility] for how that works.

# Building the field
%%%
tag := "tutorial-aes-field-building"
%%%

{name}`Hex.GF2n` is the single-word packed field: an element of `GF(2ⁿ)`
for `n < 64`, stored as one `UInt64` whose bits are the coefficients. It
is indexed by the modulus and carries the irreducibility proof, so the
type cannot be formed for a modulus that would not give a field.

The modulus is passed as its low eight coefficients, with the leading
`x⁸` implicit, so the Rijndael modulus is the word `0x1B`.

```lean
open Hex

namespace AESTutorial

/-- AES's field: `GF(2⁸)` under the Rijndael modulus. -/
abbrev AES : Type :=
  GF2n 8 0x1B (by decide) (by decide)
    GF2Poly.aes_modulus_irreducible

/-- Read a byte as a field element. -/
def byte (w : UInt64) : AES := GF2n.reduce w

end AESTutorial
```

# Addition is exclusive-or
%%%
tag := "tutorial-aes-field-add"
%%%

The AES specification gives `0x57 + 0x83 = 0xD4`. Since addition is XOR,
that is the only arithmetic in the field a reader can check by eye.

```lean
open Hex

namespace AESTutorial

#guard (byte 0x57 + byte 0x83).val = 0xD4
#guard (0x57 ^^^ 0x83 : UInt64) = 0xD4

-- Every element is its own additive inverse, so
-- doubling in this field is not multiplication by
-- two: it is zero.
#guard (byte 0x57 + byte 0x57).val = 0

end AESTutorial
```

The second line is deliberate: `^^^` is the machine XOR on the raw word,
and it agrees with field addition on the reduced representative. Field
addition on bytes really is the instruction the hardware already has.

# XTIMES: multiplication by x
%%%
tag := "tutorial-aes-field-xtimes"
%%%

The AES specification singles out multiplication by `x`, which it calls
`xtime`, because every other multiplication is built from it. Multiplying
by `x` shifts the coefficients up by one; if that pushes a term past
degree 7, the modulus is subtracted to bring it back, which over `𝔽₂`
means XOR-ing with `0x1B`.

The specification's worked chain starts at `0x57` and applies `xtime`
four times.

```lean
open Hex

namespace AESTutorial

/-- Multiplication by `x`, the AES `xtime` operation. -/
def xtime (a : AES) : AES := a * byte 0x02

#guard (xtime (byte 0x57)).val = 0xAE
#guard (xtime (byte 0xAE)).val = 0x47
#guard (xtime (byte 0x47)).val = 0x8E
#guard (xtime (byte 0x8E)).val = 0x07

end AESTutorial
```

The step from `0x8E` to `0x07` is the one that reduces: `0x8E` has its
top bit set, so shifting overflows degree 7 and the modulus comes back in.

Because multiplication distributes over addition, any product can be
assembled from `xtime` steps. The specification computes `0x57 • 0x13` by
writing `0x13` as `0x01 + 0x02 + 0x10`, so the product is `0x57` plus
`xtime 0x57` plus `xtime⁴ 0x57`.

```lean
open Hex

namespace AESTutorial

#guard (byte 0x57 * byte 0x13).val = 0xFE

-- The same answer, assembled the way the AES
-- specification assembles it.
#guard (byte 0x57
          + xtime (byte 0x57)
          + xtime (xtime (xtime (xtime (byte 0x57))))).val
    = 0xFE

end AESTutorial
```

`HexGF2` does not actually multiply this way. It uses a carry-less
multiply and then reduces, which is one hardware instruction and a few
XORs rather than a loop over bits; see
{ref "hex-gf2-clmul"}[Carry-less multiplication]. The point of the second
check is that the fast route and the specification's route agree.

# The S-box: inversion
%%%
tag := "tutorial-aes-field-sbox"
%%%

The AES S-box is a field inversion followed by an affine map over `𝔽₂`.
The affine part is bit-shuffling; the part that needs a field is the
inversion, and it exists only because the modulus is irreducible.

The specification's example is that `0x53` and `0xCA` are inverse bytes.

```lean
open Hex

namespace AESTutorial

#guard (byte 0x53 * byte 0xCA).val = 1
#guard (byte 0x53)⁻¹.val = 0xCA
#guard (byte 0xCA)⁻¹.val = 0x53

-- The S-box sends zero to zero, so inversion is
-- extended by 0⁻¹ = 0 rather than left undefined.
#guard (byte 0)⁻¹.val = 0

end AESTutorial
```

That last line is worth pausing on. `0⁻¹ = 0` is a junk value: zero has no
inverse. It is the convention `Lean.Grind.Field` uses, so that inversion is
a total function and the field laws can be stated without side conditions,
and it happens to be exactly what AES specifies for the S-box at zero.
The laws that mention inverses, such as
{name}`Hex.GF2n.mul_inv_cancel`, carry a nonzero hypothesis.

# Inversion by exponentiation
%%%
tag := "tutorial-aes-field-pow"
%%%

The nonzero elements of `GF(2⁸)` form a group of order 255 under
multiplication, so `b²⁵⁵ = 1` for every nonzero `b`, and therefore
`b²⁵⁴ = b⁻¹`. That is the other standard way to build the S-box: invert by
raising to the 254th power, which needs no extended gcd.

```lean
open Hex

namespace AESTutorial

#guard (GF2n.pow (byte 0x53) 255).val = 1
#guard (GF2n.pow (byte 0x53) 254).val = 0xCA
#guard (GF2n.pow (byte 0x03) 255).val = 1

end AESTutorial
```

{name}`Hex.GF2n.pow` is square-and-multiply, so the 254th power costs
about eight multiplications rather than 254. The project forbids the
textbook linear recursion for exactly this reason: the exponents that
arise in finite-field work are the size of the field, not the size of a
loop counter one is willing to run.

`HexGF2` inverts with the extended Euclidean algorithm rather than by
exponentiation, since the gcd route does not depend on knowing the group
order. Both give the same answer, as the checks above and in
{ref "tutorial-aes-field-sbox"}[the previous section] show.

# What was checked, and by what
%%%
tag := "tutorial-aes-field-boundary"
%%%

Every `#guard` on this page is evaluated when the manual is built, so the
byte values are computed by the same code a caller would run, not
transcribed.

What that does *not* do is prove anything about AES. It shows that this
field arithmetic reproduces the worked examples in the specification,
which is a test, not a theorem. The one genuine theorem in play is
{name}`Hex.GF2Poly.aes_modulus_irreducible`, and it earns its keep: it is
what makes `AES` above a legal type, and so what makes inversion total on
nonzero bytes.

The arithmetic is Mathlib-free. If you want to connect it to Mathlib's
finite field theory, `HexGF2Mathlib` provides the ring equivalence with
the generic quotient-field construction, along with finiteness and
cardinality for the packed representation.

# Cross-references
%%%
tag := "tutorial-aes-field-cross-references"
%%%

* {ref "hex-gf2"}[`HexGF2`] is the library this page uses: the packed
  representation, the carry-less multiply, the Euclidean algorithms, and
  the committed cryptographic moduli including {name}`Hex.GF2Poly.aesModulus`.
* {ref "hex-gf2-irreducible"}[Rabin irreducibility] covers how the
  modulus's irreducibility is certified.
* {ref "hex-gfq-field"}[`HexGFqField`] is the generic quotient field over
  any prime, which is what `GF(2⁸)` here is a packed special case of.
* {ref "hex-gfq"}[`HexGFq`] chooses moduli automatically from the Conway
  table. AES does not use the Conway polynomial for degree 8, so this page
  passes the Rijndael modulus explicitly; `GF2q 8` would give the
  canonical field, which is a different presentation of the same
  256-element field.
