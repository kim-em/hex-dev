/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGF2
import HexGFq

/-!
# Finite fields: `GF(2^8)` two ways, and the canonical `GFq` constructors

`hex-gf2` and `hex-gfq` had no `Examples/` coverage at all. This exercises the
two representations of `GF(2^8)` a caller actually picks between, and the
canonical constructors, on concrete values.

The AES field appears twice here under *different* moduli, and that is the
point rather than an oversight. `Hex.GF2n 8 0x1B` is Rijndael's
`x^8 + x^4 + x^3 + x + 1`, which is what AES specifies. `Hex.GF2q 8` is the
Conway polynomial for `(2, 8)`, whose lower word is `0x1D`. Both present a
field of 256 elements; they are isomorphic but not equal, so a value's
coordinates differ between them. Reach for the AES modulus when interoperating
with AES, and for the Conway one when you need the field to be canonical.
-/

namespace Examples.FiniteFields

open Hex

/-! ## The AES field, packed in one word -/

/-- `GF(2^8)` under the Rijndael modulus, the field AES specifies. -/
abbrev AES : Type :=
  GF2n 8 0x1B (by decide) (by decide) GF2Poly.aes_modulus_irreducible

/-- Reduce a byte into the AES field. -/
def aes (w : UInt64) : AES := GF2n.reduce w

-- `0x53` and `0xCA` are the standard AES inverse pair.
#guard ((aes 0x53) * (aes 0xCA)).val = 1
#guard ((aes 0x53)⁻¹).val = 0xCA

-- `xtimes` is multiplication by `x`. Below degree 8 it is a plain shift; at or
-- above, the modulus folds the overflow back in. These are the FIPS-197
-- worked values.
#guard ((aes 0x57) * (aes 0x02)).val = 0xAE
#guard ((aes 0xAE) * (aes 0x02)).val = 0x47

-- Every nonzero element satisfies `a^255 = 1`, so `a^256 = a`.
#guard ((aes 0x53) ^ (256 : Nat)).val = 0x53

/-! ## The same field, canonically

`GF2q 8` is the packed Conway presentation. Its modulus differs from AES's, so
the same `UInt64` names a different element. -/

-- The Conway modulus for `(2, 8)` has lower word `0x1D`, not AES's `0x1B`.
#guard GF2q.lower (n := 8) = 0x1D

-- Inverse cancellation holds here too, on whatever the coordinates happen to
-- be; that is a field law, not a fact about the modulus.
#guard GF2q.repr ((GF2q.ofWord (n := 8) 0x53) * (GF2q.ofWord (n := 8) 0x53)⁻¹) = 1

/-! ## The generic constructor, over an odd prime

`GFqC p n` resolves its committed Conway entry by instance synthesis, so a
caller names the field rather than the table entry. -/

/-- `GF(13^6)`, the largest committed entry. -/
abbrev GF13_6 : Type := GFqC 13 6

/-- The generator, as the residue of `x`. -/
def gen : GF13_6 := GFqC.ofPoly FpPoly.X

-- Reduction is the identity on an already-reduced representative.
#guard GFqC.repr (GFqC.ofPoly (p := 13) (n := 6) (GFqC.repr gen)) = GFqC.repr gen

end Examples.FiniteFields
