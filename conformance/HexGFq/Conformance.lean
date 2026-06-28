import HexGFq.Basic

/-!
Core conformance checks for the canonical finite-field constructors in
`HexGFq`.

Oracle: none
Mode: always
Covered operations:
- `Conway.packedGF2FpPoly`
- `Conway.PackedGF2Entry`
- `GFq.modulus`, `GFq.ofPoly`, and `GFq.repr`
- `GFqC.modulus`, `GFqC.ofPoly`, `GFqC.repr`, and `GFqC.frob`
- `GF2q.supportedEntry`, `GF2q.lower`, `GF2q.modulus`,
  `GF2q.ofWord`, and `GF2q.repr`
Covered properties:
- the committed packed binary entries are backed by `supportedEntry_2_1`
  through `supportedEntry_2_6`
- the ergonomic generic `GFqC 2 1` surface selects `supportedEntry_2_1`
  through instance synthesis
- the generic and packed modulus views agree on the committed `C(2, 1)`
  entry
- generic `GFqC 2 1` representatives reduce modulo the Conway polynomial
- packed `GF2q 1` representatives reduce words modulo the packed Conway
  polynomial
Covered edge cases:
- the committed binary linear entry `(p, n) = (2, 1)`
- the nontrivial committed packed binary entry `(p, n) = (2, 4)`
- zero, already-reduced, modulus, and high-degree generic inputs
- zero, one, modulus-word, and high-bit packed inputs
- the unsupported `(p, n) = (2, 0)` Conway lookup boundary
-/

namespace Hex
namespace GfqConformance

private def coeffNats {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def wordArray (f : GF2Poly) : Array UInt64 :=
  f.toWords

private def polyTwo (coeffs : Array Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))

private abbrev Generic21 : Type :=
  GFqC 2 1

private def generic (coeffs : Array Nat) : Generic21 :=
  GFqC.ofPoly (p := 2) (n := 1) (polyTwo coeffs)

private def genericReprNats (x : Generic21) : List Nat :=
  coeffNats (GFqC.repr x)

private abbrev Packed21 : Type :=
  GF2q 1

private def packed (w : UInt64) : Packed21 :=
  GF2q.ofWord (n := 1) w

private abbrev Packed24 : Type :=
  GF2q 4

private def packed4 (w : UInt64) : Packed24 :=
  GF2q.ofWord (n := 4) w

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

#guard coeffNats (inferInstance : Conway.PackedGF2Entry 2).entry.poly = [1, 1, 1]
#guard coeffNats (inferInstance : Conway.PackedGF2Entry 3).entry.poly = [1, 1, 0, 1]
#guard coeffNats (inferInstance : Conway.PackedGF2Entry 4).entry.poly = [1, 1, 0, 0, 1]
#guard coeffNats (inferInstance : Conway.PackedGF2Entry 5).entry.poly = [1, 0, 1, 0, 0, 1]
#guard coeffNats (inferInstance : Conway.PackedGF2Entry 6).entry.poly = [1, 1, 0, 1, 1, 0, 1]
#guard (inferInstance : Conway.PackedGF2Entry 2).lower = 0x3
#guard (inferInstance : Conway.PackedGF2Entry 3).lower = 0x3
#guard (inferInstance : Conway.PackedGF2Entry 4).lower = 0x3
#guard (inferInstance : Conway.PackedGF2Entry 5).lower = 0x5
#guard (inferInstance : Conway.PackedGF2Entry 6).lower = 0x1B

example :
    (Conway.CommittedEntry.entry (p := 2) (n := 1)) = Conway.supportedEntry_2_1 :=
  rfl
#guard coeffNats (GFqC.modulus (p := 2) (n := 1)) = [1, 1]
#guard GFqC.modulus (p := 2) (n := 1) =
  GFq.modulus Conway.supportedEntry_2_1
#guard GFqC.modulus (p := 2) (n := 1) =
  Conway.conwayPoly 2 1 Conway.supportedEntry_2_1
#guard 0 < FpPoly.degree (GFqC.modulus (p := 2) (n := 1))
example : 0 < FpPoly.degree (GFqC.modulus (p := 2) (n := 1)) := by
  simp

example : 0 < (1 : Nat) ∧ 1 < 64 := by
  simp

example : FpPoly.Irreducible (GFqC.modulus (p := 2) (n := 1)) := by
  grind

example (h : Conway.SupportedEntry 2 1) : Hex.Nat.Prime 2 := by
  have := GFq.modulus_prime h
  grind

example : GF2Poly.Irreducible (GF2q.modulus (n := 1)) := by
  grind

#guard Conway.luebeckConwayPolynomial? 2 0 = (none : Option (FpPoly 2))
-- `(2, 2)` and `(3, 1)` were previously unsupported boundaries; PR #2365
-- extended the committed Lübeck table to cover them, so their positive
-- lookups are now exercised in `HexConway/Conformance.lean`.

#guard genericReprNats (generic #[]) = []
#guard genericReprNats (generic #[1]) = [1]
#guard genericReprNats (generic #[0, 1]) = [1]
#guard genericReprNats (generic #[1, 1]) = []
#guard genericReprNats (generic #[0, 0, 0, 1]) = [1]
#guard GFqC.repr (generic #[0, 1]) =
  GFqRing.reduceMod (GFqC.modulus (p := 2) (n := 1)) (polyTwo #[0, 1])
#guard GFqC.repr (generic #[1, 1]) =
  GFqRing.reduceMod (GFqC.modulus (p := 2) (n := 1)) (polyTwo #[1, 1])
#guard GFqC.repr (GFqC.ofPoly (p := 2) (n := 1) (polyTwo #[0, 1])) =
  GFq.repr (GFq.ofPoly Conway.supportedEntry_2_1 (polyTwo #[0, 1]))

example (x y z : Generic21) :
    GFqC.repr ((x + y) * z) =
      GFqRing.reduceMod (GFqC.modulus (p := 2) (n := 1))
        (GFqRing.reduceMod (GFqC.modulus (p := 2) (n := 1))
          (GFqC.repr x + GFqC.repr y) * GFqC.repr z) := by
  simp

-- The Frobenius wrapper matches the inherited `p`-th power on the
-- committed `GFqC 2 1` entry and produces the expected representative.
#guard genericReprNats (GFqC.frob (generic #[1])) = [1]
#guard genericReprNats (GFqC.frob (generic #[0, 1])) = [1]
#guard GFqC.frob (generic #[0, 1]) = GFq.frob (generic #[0, 1])
#guard GFqC.frob (generic #[0, 1]) = (generic #[0, 1]) ^ (2 : Nat)

#guard coeffNats (GF2q.supportedEntry (n := 1)).poly = [1, 1]
#guard Conway.luebeckConwayPolynomial? 2 1 =
  some (GF2q.supportedEntry (n := 1)).poly
#guard GF2q.lower (n := 1) = 1
#guard wordArray (GF2q.modulus (n := 1)) = #[3]
#guard coeffNats (GFqC.modulus (p := 2) (n := 1)) =
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

#guard wordArray (GF2q.modulus (n := 4)) = #[0x13]
#guard GF2q.lower (n := 4) = 0x3
#guard GF2q.repr (packed4 0x10) = 0x3
#guard coeffNats (GF2q.reprFpPoly (packed4 0x10)) = [1, 1]
#guard coeffNats (GFq.repr (GF2q.toGFq (packed4 0x10))) = [1, 1]
#guard GF2q.toGFq (packed4 0x10) =
  GFq.ofPoly (GF2q.supportedEntry (n := 4)) (GF2q.reprFpPoly (packed4 0x10))

end GfqConformance
end Hex
