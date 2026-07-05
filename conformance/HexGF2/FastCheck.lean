/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGF2.CommonIrreducibility
public import HexGF2.Field
-- `#guard` checks below evaluate at elaboration time, so the field
-- instances and `ofUInt64Monic` must be available as `meta` imports.
public meta import HexGF2.Field
public meta import HexGF2.Euclid

public section

/-!
Executable `#guard` checks for the single-word `GF2n` wrapper path.

These checks use the AES modulus `x^8 + x^4 + x^3 + x + 1`; the
irreducibility witness comes from `HexGF2.CommonIrreducibility` so the
module can focus on ordinary evaluation through proof-carrying wrapper
constructors.
-/
namespace Hex

private theorem aesIrreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 8) :=
  GF2Poly.aes_modulus_irreducible

namespace GF2n

private abbrev AESField : Type :=
  GF2n 8 0x1B (by decide) (by decide) aesIrreducible

private def aes (w : UInt64) : AESField :=
  reduce w

#guard ((aes 0x53)⁻¹).val = 0xCA
#guard ((aes 1) / (aes 0x53)).val = 0xCA
#guard ((aes 0x53) * (aes 0xCA)).val = 1

end GF2n

namespace GF2nPoly

private abbrev AESPolyField : Type :=
  GF2nPoly (GF2Poly.ofUInt64Monic 0x1B 8) aesIrreducible

private def aesPoly (w : UInt64) : AESPolyField :=
  reducePoly (GF2Poly.ofUInt64 w)

#guard (((aesPoly 0x53)⁻¹).val.toWords) = #[0xCA]
#guard (((aesPoly 1) / (aesPoly 0x53)).val.toWords) = #[0xCA]
#guard (((aesPoly 0x53) * (aesPoly 0xCA)).val.toWords) = #[1]

end GF2nPoly
end Hex
