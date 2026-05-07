import HexGfq.Basic

/-!
Core conformance checks for the canonical finite-field constructors in
`HexGfq`.

Oracle: none
Mode: always
Covered operations:
- `Conway.packedGF2FpPoly`
- `Conway.PackedGF2Entry`
- `GFq.modulus`, `GFq.ofPoly`, and `GFq.repr`
- `GF2q.supportedEntry`, `GF2q.lower`, `GF2q.modulus`,
  `GF2q.ofWord`, and `GF2q.repr`
Covered properties:
- the committed packed binary entry is backed by `supportedEntry_2_1`
- the generic and packed modulus views agree on the committed `C(2, 1)`
  entry
- generic `GFq 2 1` representatives reduce modulo the Conway polynomial
- packed `GF2q 1` representatives reduce words modulo the packed Conway
  polynomial
Covered edge cases:
- the committed binary linear entry `(p, n) = (2, 1)`
- zero, already-reduced, modulus, and high-degree generic inputs
- zero, one, modulus-word, and high-bit packed inputs
- unsupported Conway lookup boundaries outside the committed table
-/

namespace Hex
namespace GfqConformance

private def coeffNats {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def wordArray (f : GF2Poly) : Array UInt64 :=
  f.toWords

private def polyTwo (coeffs : Array Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))

private abbrev Entry21 : Conway.SupportedEntry 2 1 :=
  Conway.supportedEntry_2_1

private abbrev Generic21 : Type :=
  GFq 2 1 Entry21

private def generic (coeffs : Array Nat) : Generic21 :=
  GFq.ofPoly Entry21 (polyTwo coeffs)

private def genericReprNats (x : Generic21) : List Nat :=
  coeffNats (GFq.repr x)

private abbrev Packed21 : Type :=
  GF2q 1

private def packed (w : UInt64) : Packed21 :=
  GF2q.ofWord (n := 1) w

private def packedAsGenericCoeffNats (w : UInt64) : List Nat :=
  if GF2q.repr (packed w) = 0 then
    []
  else
    [(GF2q.repr (packed w)).toNat]

#guard coeffNats (Conway.packedGF2FpPoly 1 1) = [1, 1]
-- `PackedGF2Entry` excludes degree zero; this checks only the raw helper's
-- leading-coefficient convention at the lower boundary.
#guard coeffNats (Conway.packedGF2FpPoly 0 0) = [1]
#guard coeffNats (Conway.packedGF2FpPoly 0b101 3) = [1, 0, 1, 1]
#guard coeffNats (Conway.packedGF2FpPoly ((1 : UInt64) <<< 63) 1) = [0, 1]

#guard coeffNats (inferInstance : Conway.PackedGF2Entry 1).entry.poly = [1, 1]
#guard Conway.luebeckConwayPolynomial? 2 1 =
  some (inferInstance : Conway.PackedGF2Entry 1).entry.poly
#guard (inferInstance : Conway.PackedGF2Entry 1).lower = 1
example : 0 < 1 :=
  (inferInstance : Conway.PackedGF2Entry 1).degree_pos

example : 1 < 64 :=
  (inferInstance : Conway.PackedGF2Entry 1).degree_lt_word
#guard coeffNats (Conway.conwayPoly 2 1 (inferInstance : Conway.PackedGF2Entry 1).entry) =
  coeffNats (Conway.packedGF2FpPoly (inferInstance : Conway.PackedGF2Entry 1).lower 1)

#guard coeffNats (GFq.modulus Entry21) = [1, 1]
#guard GFq.modulus Entry21 = Conway.conwayPoly 2 1 Conway.supportedEntry_2_1
#guard 0 < FpPoly.degree (GFq.modulus Entry21)
#guard Conway.luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2))
#guard Conway.luebeckConwayPolynomial? 2 7 = (none : Option (FpPoly 2))
#guard Conway.luebeckConwayPolynomial? 17 1 = (none : Option (FpPoly 17))

#guard genericReprNats (generic #[]) = []
#guard genericReprNats (generic #[1]) = [1]
#guard genericReprNats (generic #[0, 1]) = [1]
#guard genericReprNats (generic #[1, 1]) = []
#guard genericReprNats (generic #[0, 0, 0, 1]) = [1]
#guard GFq.repr (generic #[0, 1]) =
  GFqRing.reduceMod (GFq.modulus Entry21) (polyTwo #[0, 1])
#guard GFq.repr (generic #[1, 1]) =
  GFqRing.reduceMod (GFq.modulus Entry21) (polyTwo #[1, 1])

#guard coeffNats (GF2q.supportedEntry (n := 1)).poly = [1, 1]
#guard Conway.luebeckConwayPolynomial? 2 1 =
  some (GF2q.supportedEntry (n := 1)).poly
#guard GF2q.lower (n := 1) = 1
#guard wordArray (GF2q.modulus (n := 1)) = #[3]
#guard coeffNats (GFq.modulus Entry21) =
  coeffNats (Conway.packedGF2FpPoly (GF2q.lower (n := 1)) 1)
#guard wordArray (GF2q.modulus (n := 1)) =
  wordArray (GF2Poly.ofUInt64Monic (GF2q.lower (n := 1)) 1)

#guard GF2q.repr (packed 0) = 0
#guard GF2q.repr (packed 1) = 1
#guard GF2q.repr (packed 2) = 1
#guard GF2q.repr (packed 3) = 0
#guard GF2q.repr (packed ((1 : UInt64) <<< 63)) = 1
#guard GF2q.repr (packed ((0 : UInt64) - 1)) = 0
#guard genericReprNats (generic #[0, 1]) = packedAsGenericCoeffNats 2
#guard genericReprNats (generic #[1, 1]) = packedAsGenericCoeffNats 3
#guard GF2q.repr (GF2q.ofWord (n := 1) 2) =
  (GF2n.reduce
    (n := 1) (irr := GF2q.lower (n := 1))
    (hn := Conway.PackedGF2Entry.degree_pos)
    (hn64 := Conway.PackedGF2Entry.degree_lt_word)
    (hirr := Conway.PackedGF2Entry.packed_irreducible) 2).val

end GfqConformance
end Hex
