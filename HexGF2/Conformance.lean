import HexGF2.CommonIrreducibility
import HexGF2.Field

/-!
Core conformance checks for `HexGF2`.

Oracle:
- none for this `core` profile; checks are deterministic Lean-side fixtures.

Mode:
- always.

Covered operations:
- `GF2Poly.ofWords`, `GF2Poly.ofUInt64`, `GF2Poly.monomial`, `GF2Poly.toWords`.
- `GF2Poly.coeff`, `GF2Poly.degree?`, `GF2Poly.degree`.
- `GF2Poly.add`, `GF2Poly.mulXk`, `GF2Poly.divXk`, `GF2Poly.mul`.
- `GF2Poly.divMod`, `GF2Poly.div`, `GF2Poly.mod`, `GF2Poly.gcd`, `GF2Poly.xgcd`.
- `pureClmul` and trusted-runtime `clmul`.
- small `GF2n` addition, multiplication, inversion, division, and powers.

Covered properties:
- trailing-zero normalization preserves low coefficients and storage is normalized.
- addition is coefficientwise XOR and self-cancels.
- shifts move coefficients by the requested power of `x`.
- multiplication is commutative on committed inputs and agrees with monomial shifts.
- division reconstructs the dividend and division by zero returns `(0, p)`.
- `gcd` divides through the computed quotients on committed inputs.
- `xgcd` satisfies its Bezout identity on committed inputs.
- `clmul` agrees with `pureClmul` on committed inputs.
- small `GF2n` operations obey characteristic-two cancellation and AES inverse fixtures.

Covered edge cases:
- zero and empty packed inputs.
- trailing-zero word normalization.
- bit positions around 63/64 and cross-word shifts.
- products with high carry-less bits.
- division by zero.
- nontrivial Euclidean examples.
- zero inverse and reduction in the small `GF2n` wrapper.
-/

namespace Hex
namespace GF2Poly

private def w (p : GF2Poly) : Array UInt64 :=
  p.toWords

private def pA : GF2Poly :=
  ofUInt64 0b1011

private def pB : GF2Poly :=
  ofUInt64 0b110

private def pCross : GF2Poly :=
  ofWords #[0, 1]

private def pHigh : GF2Poly :=
  monomial 63 + monomial 64 + monomial 70

private def pDivisor : GF2Poly :=
  ofUInt64 0b1011

private def pDividend : GF2Poly :=
  pDivisor * ofUInt64 0b111 + ofUInt64 0b10

#guard w (ofWords #[]) = #[]
#guard w (ofWords #[0, 0, 0]) = #[]
#guard w (ofWords #[0x15, 0, 0]) = #[0x15]
#guard w (ofWords #[0, 1, 0]) = #[0, 1]

#guard w (ofUInt64 0) = #[]
#guard w (ofUInt64 0xA5) = #[0xA5]
#guard w (ofUInt64 ((1 : UInt64) <<< 63)) = #[((1 : UInt64) <<< 63)]

#guard (ofUInt64 0xA5).coeff 0 = true
#guard (ofUInt64 0xA5).coeff 1 = false
#guard (ofUInt64 0xA5).coeff 2 = true
#guard (ofWords #[0, 1]).coeff 63 = false
#guard (ofWords #[0, 1]).coeff 64 = true
#guard (ofWords #[0, 1]).coeff 65 = false

#guard w (monomial 0) = #[1]
#guard w (monomial 63) = #[((1 : UInt64) <<< 63)]
#guard w (monomial 64) = #[0, 1]
#guard (monomial 70).coeff 70 = true
#guard (monomial 70).coeff 69 = false

#guard (0 : GF2Poly).degree? = none
#guard (0 : GF2Poly).degree = 0
#guard (ofUInt64 0x80).degree? = some 7
#guard (ofUInt64 0x80).degree = 7
#guard pCross.degree? = some 64
#guard pCross.degree = 64

#guard w (pA + pB) = #[0b1101]
#guard ((pA + pB).coeff 1) = ((pA.coeff 1) != (pB.coeff 1))
#guard ((pA + pB).coeff 3) = ((pA.coeff 3) != (pB.coeff 3))
#guard w (pHigh + pHigh) = #[]
#guard w (pCross + monomial 64) = #[]

#guard w (pA.mulXk 0) = w pA
#guard w (pA.mulXk 3) = #[0b1011000]
#guard w ((ofUInt64 1).mulXk 64) = #[0, 1]
#guard (pA.mulXk 3).coeff 4 = pA.coeff 1
#guard (pCross.mulXk 6).coeff 70 = true

#guard w (pA.divXk 0) = w pA
#guard w ((ofUInt64 0b1011000).divXk 3) = #[0b1011]
#guard w ((monomial 70).divXk 6) = #[0, 1]
#guard ((pA.mulXk 5).divXk 5).coeff 3 = pA.coeff 3

#guard w (pA * pB) = #[0b111010]
#guard w (pA * 0) = #[]
#guard w ((monomial 63) * (monomial 1)) = #[0, 1]
#guard w ((monomial 70) * pA) = w (pA.mulXk 70)
#guard w (pA * pB) = w (pB * pA)
#guard w (pHigh * pA) = w (pA * pHigh)

#guard w ((divMod pDividend pDivisor).1) = #[0b111]
#guard w ((divMod pDividend pDivisor).2) = #[0b10]
#guard w (((divMod pDividend pDivisor).1 * pDivisor) + (divMod pDividend pDivisor).2) =
  w pDividend
#guard w (pDividend / pDivisor) = #[0b111]
#guard w (pDividend % pDivisor) = #[0b10]
#guard w (pDividend / 0) = #[]
#guard w (pDividend % 0) = w pDividend

#guard w (gcd pA pB) = #[1]
#guard w (gcd (pA * pB) pA) = w pA
#guard w (gcd 0 pB) = w pB
#guard w (((pA * pB) / gcd (pA * pB) pA) * gcd (pA * pB) pA) = w (pA * pB)
#guard w ((pA / gcd pA pB) * gcd pA pB) = w pA

#guard w ((xgcd pA pB).gcd) = #[1]
#guard w ((xgcd pA pB).left * pA + (xgcd pA pB).right * pB) =
  w ((xgcd pA pB).gcd)
#guard w ((xgcd (pA * pB) pA).left * (pA * pB) +
    (xgcd (pA * pB) pA).right * pA) =
  w ((xgcd (pA * pB) pA).gcd)
#guard w ((xgcd 0 pB).left * 0 + (xgcd 0 pB).right * pB) =
  w ((xgcd 0 pB).gcd)

example (p : GF2Poly) : p + p = 0 := by simp

example (p q : GF2Poly) : p + (p + q) = q := by simp

example (p q : GF2Poly) : (p + q) + q = p := by simp

end GF2Poly

#guard pureClmul 0 0 = (0, 0)
#guard pureClmul 0x53 0xCA = (0, 0x3F7E)
#guard pureClmul ((1 : UInt64) <<< 63) 2 = (1, 0)
#guard pureClmul 0xFFFF 0xFFFF = (0, 0x55555555)

#guard clmul 0 0 = pureClmul 0 0
#guard clmul 0x53 0xCA = pureClmul 0x53 0xCA
#guard clmul ((1 : UInt64) <<< 63) 2 = pureClmul ((1 : UInt64) <<< 63) 2

example (x : UInt64) : clmul 0 x = (0, 0) := by simp

example (x : UInt64) : clmul x 0 = (0, 0) := by simp

example (x y z : UInt64) :
    clmul (x ^^^ y) z =
      ((clmul x z).1 ^^^ (clmul y z).1, (clmul x z).2 ^^^ (clmul y z).2) := by
  grind

example (x y z : UInt64) :
    clmul x (y ^^^ z) =
      ((clmul x y).1 ^^^ (clmul x z).1, (clmul x y).2 ^^^ (clmul x z).2) := by
  grind

private theorem aesIrreducible :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 8) :=
  GF2Poly.aes_modulus_irreducible

namespace GF2n

private abbrev AESField : Type :=
  GF2n 8 0x1B (by decide) (by decide) aesIrreducible

private def aes (word : UInt64) : AESField :=
  reduce word

-- Plain `#eval` is blocked by the proof-only `aesIrreducible` fixture.
#guard ((aes 0)⁻¹).val = 0
#guard ((aes 1)⁻¹).val = 1
#guard ((aes 0xCA)⁻¹).val = 0x53
#guard ((aes 0) + (aes 0xCA)).val = 0xCA
#guard ((aes 0x53) + (aes 0x53)).val = 0
#guard ((aes 0x53) + (aes 0xCA)).val = 0x99
#guard ((aes 0) * (aes 0xCA)).val = 0
#guard ((aes 0x53) * (aes 1)).val = 0x53
#guard ((aes 0x53) * (aes 0xCA)).val = 1
#guard ((aes 0x57) * (aes 0x83)).val = 0xC1
#guard ((aes 0x53)⁻¹).val = 0xCA
#guard ((aes 0) / (aes 0x53)).val = 0
#guard ((aes 0x53) / (aes 1)).val = 0x53
#guard ((aes 1) / (aes 0x53)).val = 0xCA
#guard ((aes 0x02) ^ 8).val = 0x1B
#guard ((aes 0x53) ^ 0).val = 1
#guard ((aes 0x53) ^ 1).val = 0x53

example : ((0 : AESField)⁻¹ = 0) := by
  simp

example (a b : AESField) : a / b = a * b⁻¹ := by
  grind

example (a : AESField) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  grind

end GF2n

namespace GF2nPoly

private abbrev AESPolyField : Type :=
  GF2nPoly (GF2Poly.ofUInt64Monic 0x1B 8) aesIrreducible

private def aesPoly (word : UInt64) : AESPolyField :=
  reducePoly (GF2Poly.ofUInt64 word)

#guard (aesPoly 0).val = 0
#guard (aesPoly 1).val = 1
#guard ((aesPoly 0x53) * (aesPoly 0xCA)).val = 1

example (p : GF2Poly) :
    (reducePoly (f := GF2Poly.ofUInt64Monic 0x1B 8) (hirr := aesIrreducible) p).val =
      p % GF2Poly.ofUInt64Monic 0x1B 8 := by
  simp

example (a b : AESPolyField) :
    (a + b).val = (a.val + b.val) % GF2Poly.ofUInt64Monic 0x1B 8 := by
  simp

example (a b : AESPolyField) :
    (a * b).val = (a.val * b.val) % GF2Poly.ofUInt64Monic 0x1B 8 := by
  simp

example :
    (0 : AESPolyField).val = (0 : GF2Poly) := by
  simp

example :
    (1 : AESPolyField).val = (1 : GF2Poly) % GF2Poly.ofUInt64Monic 0x1B 8 := by
  simp

example :
    ((0 : AESPolyField)⁻¹ = 0) := by
  simp

example (a : AESPolyField) : a + a = 0 := by
  simp

example (a : AESPolyField) : a * 0 = 0 := by
  simp

example (a : AESPolyField) : 0 * a = 0 := by
  simp

example (a b : AESPolyField) : a / b = a * b⁻¹ := by
  grind

example (a : AESPolyField) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  grind

example (a b : AESPolyField) (k : Nat) :
    frobeniusIter (a + b) k = frobeniusIter a k + frobeniusIter b k := by
  grind

example (a b : AESPolyField) (k : Nat) :
    frobeniusIter (a * b) k = frobeniusIter a k * frobeniusIter b k := by
  grind

example {a b : AESPolyField} {k : Nat}
    (ha : frobeniusIter a k = a) (hb : frobeniusIter b k = b) :
    frobeniusIter (a + b) k = a + b := by
  grind

example {a b : AESPolyField} {k : Nat}
    (ha : frobeniusIter a k = a) (hb : frobeniusIter b k = b) :
    frobeniusIter (a * b) k = a * b := by
  grind

end GF2nPoly
end Hex
