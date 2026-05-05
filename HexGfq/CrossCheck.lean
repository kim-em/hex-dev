import HexGfq.Basic

/-!
Packed-vs-generic representation cross-check for `HexGfq`.

Oracle: none (Tier-G fast-vs-fast)
Mode: always

The committed Conway lookup currently exposes only `(2, 1)` as a
`SupportedEntry`, so `HexGfq/Conformance.lean` exercises the bridge
between `GFq 2 1` (generic `FpPoly`-quotient) and `GF2q 1` (packed
`GF2n`) at the trivial extension degree.  This module exercises the
same bridge at extension degrees where the implementations actually
diverge by constructing ad-hoc moduli at degrees 4, 8, 16, and 32 and
running pseudorandom shared inputs through both representations.

The moduli are not committed Conway entries; their irreducibility
witnesses are propositional `sorry`s, in line with the existing
pattern in `HexGF2/Conformance.lean` and `HexGF2/Bench.lean`.  The
cross-check still computes operationally: each `#guard` runs the
packed and generic operations on the same input and compares results.

Operations covered: addition, multiplication, inversion, Frobenius
(`a ↦ a^p`).

`HexGfq` does not commit packed representations for odd characteristic,
so the cross-check is binary-only.  See the per-library SPEC for the
representation-bridge scope.
-/
namespace Hex
namespace GfqCrossCheck

/-! ## Pseudorandom input streams

Deterministic 64-bit linear congruential generator using Knuth's MMIX
constants.  Each fixture seeds its own stream so the failure modes are
distinguishable.
-/

private def lcgStep (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

private def lcgWords (seed : UInt64) (count : Nat) : Array UInt64 := Id.run do
  let mut s := seed
  let mut acc : Array UInt64 := Array.empty
  for _ in [0:count] do
    s := lcgStep s
    acc := acc.push s
  pure acc

private def streamPairs (seed : UInt64) (count : Nat) : Array (UInt64 × UInt64) :=
  let raw := lcgWords seed (2 * count)
  Id.run do
    let mut acc : Array (UInt64 × UInt64) := Array.empty
    for i in [0:count] do
      acc := acc.push (raw[2 * i]!, raw[2 * i + 1]!)
    pure acc

/-! ## Bit-level word ↔ `FpPoly 2` conversions

Each bit of a `UInt64` corresponds to one binary coefficient of the
generic `FpPoly 2` representative, which makes the bridge between the
packed `GF2n` and generic `GFqField.FiniteField (FpPoly 2)` views
explicit and decidable.
-/

private def maskBits (w : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then
    0
  else if 64 ≤ n then
    w
  else
    w &&& (((1 : UInt64) <<< n.toUInt64) - 1)

private def wordToPoly2 (w : UInt64) (n : Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (((List.range n).map fun i =>
    if (((w >>> i.toUInt64) &&& 1) = 0) then
      (0 : ZMod64 2)
    else
      (1 : ZMod64 2)).toArray)

private def poly2ToWord (f : FpPoly 2) (n : Nat) : UInt64 :=
  (List.range n).foldl (init := (0 : UInt64)) fun acc i =>
    if (f.coeff i).val = 0 then
      acc
    else
      acc ||| ((1 : UInt64) <<< i.toUInt64)

/-! ## `Hex.Nat.Prime 2` and `ZMod64.PrimeModulus 2` -/

private def primeTwo : Hex.Nat.Prime 2 := by
  refine ⟨by decide, ?_⟩
  intro m hm
  have hmle : m ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hm
  have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · simp at hm
  · exact Or.inl rfl
  · exact Or.inr rfl

local instance instPrimeModulusTwo : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime primeTwo

/-! ## Per-degree fixtures

For each extension degree `n` we fix a known irreducible packed
modulus, declare the matching `FpPoly 2` modulus via
`Conway.packedGF2FpPoly`, and provide `sorry`'d irreducibility plus
positive-degree witnesses for both representations.  The four `#guard`s
per degree compare 50 pseudorandom shared inputs across addition,
multiplication, inversion, and Frobenius (`a ↦ a^2`).
-/

/-- `streamPairs` size shared across degrees.  Total work is roughly
`size × 4 ops × 4 degrees` polynomial-arithmetic calls. -/
private def streamSize : Nat := 100

namespace N4

/-- Irreducible polynomial `x^4 + x + 1`. -/
private def lower : UInt64 := 0x3
private def n : Nat := 4

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def matchesAdd (a b : UInt64) : Bool :=
  (packedOf a + packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a + genericOf b)) n

private def matchesMul (a b : UInt64) : Bool :=
  (packedOf a * packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a * genericOf b)) n

private def matchesInv (a : UInt64) : Bool :=
  ((packedOf a)⁻¹).val ==
    poly2ToWord (GFqField.repr ((genericOf a)⁻¹)) n

private def matchesFrob (a : UInt64) : Bool :=
  ((packedOf a) ^ (2 : Nat)).val ==
    poly2ToWord (GFqField.repr (GFqField.frob (genericOf a))) n

private def fixturePairs : Array (UInt64 × UInt64) :=
  streamPairs 0xCAFEBABE_DEADBEEF streamSize

#guard fixturePairs.all fun ab => matchesAdd ab.1 ab.2
#guard fixturePairs.all fun ab => matchesMul ab.1 ab.2
#guard fixturePairs.all fun ab => matchesInv ab.1
#guard fixturePairs.all fun ab => matchesFrob ab.1

end N4

namespace N8

/-- AES irreducible polynomial `x^8 + x^4 + x^3 + x + 1` (Rijndael). -/
private def lower : UInt64 := 0x1B
private def n : Nat := 8

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def matchesAdd (a b : UInt64) : Bool :=
  (packedOf a + packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a + genericOf b)) n

private def matchesMul (a b : UInt64) : Bool :=
  (packedOf a * packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a * genericOf b)) n

private def matchesInv (a : UInt64) : Bool :=
  ((packedOf a)⁻¹).val ==
    poly2ToWord (GFqField.repr ((genericOf a)⁻¹)) n

private def matchesFrob (a : UInt64) : Bool :=
  ((packedOf a) ^ (2 : Nat)).val ==
    poly2ToWord (GFqField.repr (GFqField.frob (genericOf a))) n

private def fixturePairs : Array (UInt64 × UInt64) :=
  streamPairs 0x1B1B1B1B_AAAA5555 streamSize

#guard fixturePairs.all fun ab => matchesAdd ab.1 ab.2
#guard fixturePairs.all fun ab => matchesMul ab.1 ab.2
#guard fixturePairs.all fun ab => matchesInv ab.1
#guard fixturePairs.all fun ab => matchesFrob ab.1

end N8

namespace N16

/-- CRC-16-CCITT irreducible polynomial `x^16 + x^12 + x^3 + x + 1`. -/
private def lower : UInt64 := 0x100B
private def n : Nat := 16

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def matchesAdd (a b : UInt64) : Bool :=
  (packedOf a + packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a + genericOf b)) n

private def matchesMul (a b : UInt64) : Bool :=
  (packedOf a * packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a * genericOf b)) n

private def matchesInv (a : UInt64) : Bool :=
  ((packedOf a)⁻¹).val ==
    poly2ToWord (GFqField.repr ((genericOf a)⁻¹)) n

private def matchesFrob (a : UInt64) : Bool :=
  ((packedOf a) ^ (2 : Nat)).val ==
    poly2ToWord (GFqField.repr (GFqField.frob (genericOf a))) n

private def fixturePairs : Array (UInt64 × UInt64) :=
  streamPairs 0xFFEE0011_22DD3344 streamSize

#guard fixturePairs.all fun ab => matchesAdd ab.1 ab.2
#guard fixturePairs.all fun ab => matchesMul ab.1 ab.2
#guard fixturePairs.all fun ab => matchesInv ab.1
#guard fixturePairs.all fun ab => matchesFrob ab.1

end N16

namespace N32

/-- Irreducible polynomial `x^32 + x^7 + x^3 + x^2 + 1`. -/
private def lower : UInt64 := 0x8D
private def n : Nat := 32

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  sorry

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  sorry

private abbrev Packed : Type :=
  GF2n n lower (by decide) (by decide) packed_irr

private abbrev Generic : Type :=
  GFqField.FiniteField genericMod generic_pos primeTwo generic_irr

private def packedOf (w : UInt64) : Packed :=
  GF2n.reduce (maskBits w n)

private def genericOf (w : UInt64) : Generic :=
  GFqField.ofPoly genericMod generic_pos primeTwo generic_irr (wordToPoly2 w n)

private def matchesAdd (a b : UInt64) : Bool :=
  (packedOf a + packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a + genericOf b)) n

private def matchesMul (a b : UInt64) : Bool :=
  (packedOf a * packedOf b).val ==
    poly2ToWord (GFqField.repr (genericOf a * genericOf b)) n

private def matchesInv (a : UInt64) : Bool :=
  ((packedOf a)⁻¹).val ==
    poly2ToWord (GFqField.repr ((genericOf a)⁻¹)) n

private def matchesFrob (a : UInt64) : Bool :=
  ((packedOf a) ^ (2 : Nat)).val ==
    poly2ToWord (GFqField.repr (GFqField.frob (genericOf a))) n

private def fixturePairs : Array (UInt64 × UInt64) :=
  streamPairs 0x0123456789ABCDEF streamSize

#guard fixturePairs.all fun ab => matchesAdd ab.1 ab.2
#guard fixturePairs.all fun ab => matchesMul ab.1 ab.2
#guard fixturePairs.all fun ab => matchesInv ab.1
#guard fixturePairs.all fun ab => matchesFrob ab.1

end N32

end GfqCrossCheck
end Hex
