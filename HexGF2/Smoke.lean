import HexGF2.Field

/-!
Executable smoke tests for the single-word `GF2n` wrapper path.

These checks use the AES modulus `x^8 + x^4 + x^3 + x + 1`; the
irreducibility proof is a placeholder fixture so the module can focus on
ordinary evaluation through proof-carrying wrapper constructors.  The
checks use `#guard` rather than `#eval` because the irreducibility
fixture is currently a `theorem ... := by sorry` (`#eval` refuses to run
through `sorry`-tainted closures, while `#guard`'s `decide` path
reduces); see `HexGF2/Conformance.lean` for the parallel pattern.
-/
namespace Hex

/-- Irreducibility of the AES Rijndael modulus `x^8 + x^4 + x^3 + x + 1`
over `GF(2)` is currently stubbed via `theorem ... := by sorry`,
matching the established project pattern for irreducibility fixtures
(see `HexGF2/Bench.lean`, `HexGF2/Conformance.lean`, and
`HexGF2/EmitFixtures.lean`).  The full proof is pending the executable
`rabinTest`-to-`GF2Poly.Irreducible` soundness bridge tracked under the
GF2 Rabin's-theorem follow-up; once that lands, every committed AES-
style fixture can be discharged uniformly via `rabinTest` plus
`decide`. -/
private theorem aesIrreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 8) := by
  sorry

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
