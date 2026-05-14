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
witnesses are local certificates or remaining propositional proof
obligations.  The cross-check still computes operationally: each
`#guard` runs the packed and generic operations on the same input and
compares results.

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
  Berlekamp.gf2WordPoly w n

private theorem wordToPoly2_size_le (w : UInt64) (n : Nat) :
    (wordToPoly2 w n).size ≤ n :=
  Berlekamp.gf2WordPoly_size_le w n

private theorem wordToPoly2_coeff (w : UInt64) (n i : Nat) :
    (wordToPoly2 w n).coeff i =
      if i < n then Berlekamp.gf2BitCoeff w i else 0 :=
  Berlekamp.gf2WordPoly_coeff w n i

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

private def polyP2 (coeffs : Array Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))

private theorem maxProperDiv_4 : Berlekamp.maximalProperDivisors 4 = [2] := by decide
private theorem maxProperDiv_8 : Berlekamp.maximalProperDivisors 8 = [4] := by decide

private def genericN4Cert : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 4
  powChain :=
    #[polyP2 #[0, 1], polyP2 #[0, 0, 1], polyP2 #[1, 1],
      polyP2 #[1, 0, 1], polyP2 #[0, 1]]
  bezout := #[{ left := polyP2 #[], right := polyP2 #[1] }]

set_option maxRecDepth 4096 in
private theorem genericN4Cert_check :
    Berlekamp.checkIrreducibilityCertificateLinear
        (Conway.packedGF2FpPoly 0x3 4)
        (by unfold Conway.packedGF2FpPoly; rfl)
        genericN4Cert = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinear,
    genericN4Cert,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinear, Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_4, Conway.packedGF2FpPoly, polyP2]
  constructor
  · constructor
    · constructor
      · rfl
      · intro x hx
        have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem genericN4_irr :
    FpPoly.Irreducible (Conway.packedGF2FpPoly 0x3 4) :=
  Berlekamp.rabinTest_imp_irreducible (Conway.packedGF2FpPoly 0x3 4)
    (by unfold Conway.packedGF2FpPoly; rfl)
    (Berlekamp.checkIrreducibilityCertificateLinear_rabinTest
      (Conway.packedGF2FpPoly 0x3 4)
      (by unfold Conway.packedGF2FpPoly; rfl)
      genericN4Cert
      genericN4Cert_check)

private def genericN8Cert : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 8
  powChain :=
    #[polyP2 #[0, 1], polyP2 #[0, 0, 1], polyP2 #[0, 0, 0, 0, 1],
      polyP2 #[1, 1, 0, 1, 1], polyP2 #[0, 1, 1, 1, 1, 0, 1],
      polyP2 #[0, 0, 1, 0, 0, 1, 1, 1], polyP2 #[1, 0, 1, 1, 0, 0, 1],
      polyP2 #[0, 1, 0, 1, 1, 1, 1, 1], polyP2 #[0, 1]]
  bezout :=
    #[{ left := polyP2 #[1, 1, 0, 0, 1],
        right := polyP2 #[1, 0, 0, 0, 1, 0, 1] }]

set_option maxRecDepth 4096 in
private theorem genericN8Cert_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        (Conway.packedGF2FpPoly 0x1B 8)
        (by unfold Conway.packedGF2FpPoly; rfl)
        genericN8Cert = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    genericN8Cert,
    Berlekamp.IrreducibilityCertificate.toAmbient?,
    Berlekamp.checkPowChainLinearIncremental,
    Berlekamp.checkPowChainLinearIncrementalStep,
    Berlekamp.checkRabinBezoutWitnesses,
    Berlekamp.checkRabinBezoutWitness, Berlekamp.certifiedFrobeniusDiffMod,
    maxProperDiv_8, Conway.packedGF2FpPoly, polyP2]
  constructor
  · constructor
    · constructor
      · rfl
      · constructor
        · rfl
        · intro x hx
          have hcases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨
              x = 6 ∨ x = 7 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rfl
  · rfl

private theorem genericN8_irr :
    FpPoly.Irreducible (Conway.packedGF2FpPoly 0x1B 8) :=
  Berlekamp.rabinTest_imp_irreducible (Conway.packedGF2FpPoly 0x1B 8)
    (by unfold Conway.packedGF2FpPoly; rfl)
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      (Conway.packedGF2FpPoly 0x1B 8)
      (by unfold Conway.packedGF2FpPoly; rfl)
      genericN8Cert
      genericN8Cert_check)

/-! ## Per-degree fixtures

For each extension degree `n` we fix a known irreducible packed
modulus, declare the matching `FpPoly 2` modulus via
`Conway.packedGF2FpPoly`, and provide irreducibility plus positive-degree
witnesses for both representations.  The four `#guard`s
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
  exact GF2Poly.gf16_modulus_irreducible

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  exact genericN4_irr

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
  exact GF2Poly.aes_modulus_irreducible

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  exact genericN8_irr

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
  change GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x100B 16)
  exact GF2Poly.gf65k_modulus_irreducible

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

private def packedModulus : GF2Poly :=
  GF2Poly.ofUInt64Monic lower n

private def packedCert : GF2Poly.IrreducibilityCertificate :=
  { n := n
    powChain := Array.ofFn fun k : Fin (n + 1) =>
      GF2Poly.xpow2kMod packedModulus k.val
    bezout :=
      let diff := GF2Poly.frobeniusDiffMod packedModulus 16
      let xg := GF2Poly.xgcd packedModulus diff
      #[{ left := xg.left, right := xg.right }] }

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8192 in
private theorem packedCert_check :
    GF2Poly.checkIrreducibilityCertificate packedModulus packedCert = true := by
  decide

private theorem packed_irr :
    GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n) := by
  exact GF2Poly.checkIrreducibilityCertificate_imp_irreducible
    packedModulus packedCert packedCert_check

private def genericMod : FpPoly 2 :=
  Conway.packedGF2FpPoly lower n

private theorem genericMod_monic : DensePoly.Monic genericMod := by
  unfold genericMod Conway.packedGF2FpPoly
  rfl

private def genericN32PowChain : Array (FpPoly 2) :=
  #[
    polyP2 #[0, 1],
    polyP2 #[0, 0, 1],
    polyP2 #[0, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 0, 1, 1, 0, 0, 0, 1],
    polyP2 #[1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1],
    polyP2 #[1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1],
    polyP2 #[1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1],
    polyP2 #[0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1],
    polyP2 #[1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1],
    polyP2 #[1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    polyP2 #[0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1],
    polyP2 #[1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    polyP2 #[0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1],
    polyP2 #[0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1],
    polyP2 #[0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1],
    polyP2 #[0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1],
    polyP2 #[0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1],
    polyP2 #[0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1],
    polyP2 #[0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1],
    polyP2 #[1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1],
    polyP2 #[1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1],
    polyP2 #[1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1],
    polyP2 #[1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1],
    polyP2 #[1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1],
    polyP2 #[1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1],
    polyP2 #[1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1],
    polyP2 #[0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1],
    polyP2 #[0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    polyP2 #[0, 1]
  ]

private def genericN32SamePrimeCert :
    Berlekamp.SamePrimeIrreducibilityCertificate 2 where
  n := 32
  powChain := genericN32PowChain
  bezout :=
    #[{ left := polyP2 #[1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1],
        right := polyP2 #[0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1] }]

private def genericN32Quotients : Array (FpPoly 2) :=
  #[
    polyP2 #[],
    polyP2 #[],
    polyP2 #[],
    polyP2 #[],
    polyP2 #[1],
    polyP2 #[],
    polyP2 #[],
    polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    polyP2 #[1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    polyP2 #[1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    polyP2 #[0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1],
    polyP2 #[1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    polyP2 #[0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1],
    polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    polyP2 #[0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1],
    polyP2 #[0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1],
    polyP2 #[0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    polyP2 #[0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    polyP2 #[0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1],
    polyP2 #[0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]
  ]

private def genericN32Cert : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 32
  powChain := genericN32PowChain
  bezout := genericN32SamePrimeCert.bezout

#guard
  Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses
    genericMod genericMod_monic genericN32SamePrimeCert
    genericN32Quotients = true

private theorem genericN32_step0_prev_reduced :
    (polyP2 #[0, 1]).degree?.getD 0 < genericMod.degree?.getD 0 := by
  have hdegree : genericMod.degree?.getD 0 = 32 := by
    unfold genericMod Conway.packedGF2FpPoly DensePoly.degree? DensePoly.size
    rfl
  apply Berlekamp.degree?_getD_lt_of_size_le
  · decide
  · rw [hdegree]
    unfold polyP2 FpPoly.ofCoeffs
    exact Nat.le_trans (DensePoly.size_ofCoeffs_le _)
      (by simp)

private theorem genericN32_step0_curr_reduced :
    (polyP2 #[0, 0, 1]).degree?.getD 0 < genericMod.degree?.getD 0 := by
  have hdegree : genericMod.degree?.getD 0 = 32 := by
    unfold genericMod Conway.packedGF2FpPoly DensePoly.degree? DensePoly.size
    rfl
  apply Berlekamp.degree?_getD_lt_of_size_le
  · decide
  · rw [hdegree]
    unfold polyP2 FpPoly.ofCoeffs
    exact Nat.le_trans (DensePoly.size_ofCoeffs_le _)
      (by simp)

private theorem genericN32_step0_reduced_bools :
    decide ((polyP2 #[0, 1]).degree?.getD 0 < genericMod.degree?.getD 0) = true ∧
      decide ((polyP2 #[0, 0, 1]).degree?.getD 0 < genericMod.degree?.getD 0) = true := by
  exact ⟨decide_eq_true genericN32_step0_prev_reduced,
    decide_eq_true genericN32_step0_curr_reduced⟩

#guard
  Berlekamp.checkRabinBezoutWitnesses
    genericMod genericMod_monic genericN32SamePrimeCert = true

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
