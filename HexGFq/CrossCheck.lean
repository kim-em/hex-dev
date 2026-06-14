import HexGFq.Basic

/-!
Packed-vs-generic representation cross-check for `HexGFq`.

Oracle: none (Tier-G fast-vs-fast)
Mode: always

The committed Conway lookup currently exposes only `(2, 1)` as a
`SupportedEntry`, so `HexGFq/Conformance.lean` exercises the correspondence
between `GFq 2 1` (generic `FpPoly`-quotient) and `GF2q 1` (packed
`GF2n`) at the trivial extension degree.  This module exercises the
same correspondence at extension degrees where the implementations actually
diverge by constructing ad-hoc moduli at degrees 4, 8, 16, and 32 and
running pseudorandom shared inputs through both representations.

The moduli are not committed Conway entries; their irreducibility
witnesses are local certificates or remaining propositional proof
obligations.  The cross-check still computes operationally: each
`#guard` runs the packed and generic operations on the same input and
compares results.

Operations covered: addition, multiplication, inversion, Frobenius
(`a ↦ a^p`).

`HexGFq` does not commit packed representations for odd characteristic,
so the cross-check is binary-only.  See the per-library SPEC for the
representation-correspondence scope.
-/
namespace Hex
namespace GfqCrossCheck

/-! ## Pseudorandom input streams

Deterministic 64-bit linear congruential generator using Knuth's MMIX
constants.  Each fixture seeds its own stream so the failure modes are
distinguishable.
-/

/-- `lcgStep s` advances the 64-bit LCG state one step using Knuth's MMIX
multiplier and increment. -/
private def lcgStep (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1442695040888963407

/-- `lcgWords seed count` runs the LCG from `seed` and returns its first
`count` output words. -/
private def lcgWords (seed : UInt64) (count : Nat) : Array UInt64 := Id.run do
  let mut s := seed
  let mut acc : Array UInt64 := Array.empty
  for _ in [0:count] do
    s := lcgStep s
    acc := acc.push s
  pure acc

/-- `streamPairs seed count` draws `2 * count` LCG words and pairs them into
`count` input pairs fed through both representations. -/
private def streamPairs (seed : UInt64) (count : Nat) : Array (UInt64 × UInt64) :=
  let raw := lcgWords seed (2 * count)
  Id.run do
    let mut acc : Array (UInt64 × UInt64) := Array.empty
    for i in [0:count] do
      acc := acc.push (raw[2 * i]!, raw[2 * i + 1]!)
    pure acc

/-! ## Bit-level word ↔ `FpPoly 2` conversions

Each bit of a `UInt64` corresponds to one binary coefficient of the
generic `FpPoly 2` representative, which makes the correspondence between
the packed `GF2n` and generic `GFqField.FiniteField (FpPoly 2)` views
explicit and decidable.
-/

/-- `maskBits w n` keeps the low `n` bits of `w` and clears the rest. -/
private def maskBits (w : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then
    0
  else if 64 ≤ n then
    w
  else
    w &&& (((1 : UInt64) <<< n.toUInt64) - 1)

/-- `wordToPoly2 w n` reads the low `n` bits of `w` as the binary coefficients
of an `FpPoly 2` representative. -/
private def wordToPoly2 (w : UInt64) (n : Nat) : FpPoly 2 :=
  Berlekamp.gf2WordPoly w n

/-- `wordToPoly2_size_le` bounds the converted polynomial's coefficient array
by the requested bit width `n`. -/
private theorem wordToPoly2_size_le (w : UInt64) (n : Nat) :
    (wordToPoly2 w n).size ≤ n :=
  Berlekamp.gf2WordPoly_size_le w n

/-- `wordToPoly2_coeff` gives the `i`-th coefficient of the converted
polynomial: bit `i` of `w` when `i < n`, else zero. -/
private theorem wordToPoly2_coeff (w : UInt64) (n i : Nat) :
    (wordToPoly2 w n).coeff i =
      if i < n then Berlekamp.gf2BitCoeff w i else 0 :=
  Berlekamp.gf2WordPoly_coeff w n i

/-- `poly2ToWord f n` packs the low `n` coefficients of `f` back into a
`UInt64`, setting bit `i` when coefficient `i` is nonzero. -/
private def poly2ToWord (f : FpPoly 2) (n : Nat) : UInt64 :=
  (List.range n).foldl (init := (0 : UInt64)) fun acc i =>
    if (f.coeff i).val = 0 then
      acc
    else
      acc ||| ((1 : UInt64) <<< i.toUInt64)

/-! ## `Hex.Nat.Prime 2` and `ZMod64.PrimeModulus 2` -/

/-- `primeTwo` is the primality witness for 2, used to build the prime-modulus
instance for the binary base field. -/
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

/-- `polyP2 coeffs` builds an `FpPoly 2` from a coefficient array of naturals
reduced mod 2. -/
private def polyP2 (coeffs : Array Nat) : FpPoly 2 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 2 n))

private theorem maxProperDiv_4 : Berlekamp.maximalProperDivisors 4 = [2] := by decide
private theorem maxProperDiv_8 : Berlekamp.maximalProperDivisors 8 = [4] := by decide
private theorem maxProperDiv_16 : Berlekamp.maximalProperDivisors 16 = [8] := by decide
private theorem maxProperDiv_32 : Berlekamp.maximalProperDivisors 32 = [16] := by decide

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

private def genericN16Cert : Berlekamp.IrreducibilityCertificate where
  p := 2
  n := 16
  powChain :=
    #[polyP2 #[0, 1], polyP2 #[0, 0, 1], polyP2 #[0, 0, 0, 0, 1],
      polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 1],
      polyP2 #[1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      polyP2 #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1],
      polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1],
      polyP2 #[1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1],
      polyP2 #[1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1],
      polyP2 #[0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1],
      polyP2 #[0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1],
      polyP2 #[0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1],
      polyP2 #[1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1],
      polyP2 #[1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1],
      polyP2 #[1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1],
      polyP2 #[0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1],
      polyP2 #[0, 1]]
  bezout :=
    #[{ left := polyP2 #[0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1],
        right := polyP2 #[1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1] }]

private def genericN16Mod : FpPoly 2 :=
  Conway.packedGF2FpPoly 0x100B 16

private theorem genericN16Mod_monic : DensePoly.Monic genericN16Mod := by
  unfold genericN16Mod Conway.packedGF2FpPoly
  rfl

private theorem genericN16Mod_degree_eq : genericN16Mod.degree?.getD 0 = 16 := by
  unfold genericN16Mod Conway.packedGF2FpPoly DensePoly.degree? DensePoly.size
  rfl

private theorem genericN16Mod_degree_pos : 0 < genericN16Mod.degree?.getD 0 := by
  rw [genericN16Mod_degree_eq]
  decide

private theorem polyP2_size_le_16 {arr : Array Nat} (h : arr.size ≤ 16) :
    (polyP2 arr).size ≤ genericN16Mod.degree?.getD 0 := by
  rw [genericN16Mod_degree_eq]
  unfold polyP2 FpPoly.ofCoeffs
  exact Nat.le_trans (DensePoly.size_ofCoeffs_le _) (by simpa using h)

private def genericN16SamePrimeCert :
    Berlekamp.SamePrimeIrreducibilityCertificate 2 where
  n := genericN16Cert.n
  powChain := genericN16Cert.powChain
  bezout := genericN16Cert.bezout

private def genericN16Quotients : Array (FpPoly 2) :=
  #[
    polyP2 #[],
    polyP2 #[],
    polyP2 #[],
    polyP2 #[1],
    polyP2 #[1, 0, 0, 0, 1, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 0, 1, 0, 1, 0, 1],
    polyP2 #[1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1],
    polyP2 #[1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 0, 0, 0, 1],
    polyP2 #[1, 0, 1, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 0, 0, 0, 1, 0, 1, 0, 1],
    polyP2 #[0, 0, 1, 0, 1, 0, 1],
    polyP2 #[1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    polyP2 #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]
  ]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step0_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 0 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1])
    (curr := polyP2 #[0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step1_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 1 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step2_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 2 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step3_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 3 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 1])
    (curr := polyP2 #[1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    (quot := polyP2 #[1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step4_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 4 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    (curr := polyP2 #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1])
    (quot := polyP2 #[1, 0, 0, 0, 1, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step5_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 5 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1])
    (curr := polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1])
    (quot := polyP2 #[0, 0, 0, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step6_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 6 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1])
    (curr := polyP2 #[1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1])
    (quot := polyP2 #[1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step7_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 7 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1])
    (curr := polyP2 #[1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1])
    (quot := polyP2 #[0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step8_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 8 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1])
    (curr := polyP2 #[0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1])
    (quot := polyP2 #[1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step9_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 9 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1])
    (curr := polyP2 #[0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1])
    (quot := polyP2 #[0, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step10_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 10 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1])
    (quot := polyP2 #[0, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step11_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 11 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1])
    (curr := polyP2 #[1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1])
    (quot := polyP2 #[1, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step12_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 12 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1])
    (curr := polyP2 #[1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1])
    (quot := polyP2 #[0, 0, 0, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step13_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 13 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1])
    (curr := polyP2 #[1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1])
    (quot := polyP2 #[0, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step14_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 14 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1])
    (curr := polyP2 #[0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1])
    (quot := polyP2 #[1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_step15_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericN16Mod genericN16SamePrimeCert genericN16Quotients 15 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1])
    (curr := polyP2 #[0, 1])
    (quot := polyP2 #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericN16Mod_degree_pos
  · exact polyP2_size_le_16 (by decide)
  · exact polyP2_size_le_16 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericN16Mod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16QuotientWitnesses_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses
      genericN16Mod genericN16Mod_monic genericN16SamePrimeCert
      genericN16Quotients = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses_of_steps
  · decide
  · decide
  · apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses_first_of_coeffs
      (first := polyP2 #[0, 1])
    · rfl
    · simp [genericN16Mod, Conway.packedGF2FpPoly, polyP2, FpPoly.X,
        DensePoly.monomial, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
      decide
  · intro k hk
    match k, hk with
    | 0, _ => exact genericN16_step0_check
    | 1, _ => exact genericN16_step1_check
    | 2, _ => exact genericN16_step2_check
    | 3, _ => exact genericN16_step3_check
    | 4, _ => exact genericN16_step4_check
    | 5, _ => exact genericN16_step5_check
    | 6, _ => exact genericN16_step6_check
    | 7, _ => exact genericN16_step7_check
    | 8, _ => exact genericN16_step8_check
    | 9, _ => exact genericN16_step9_check
    | 10, _ => exact genericN16_step10_check
    | 11, _ => exact genericN16_step11_check
    | 12, _ => exact genericN16_step12_check
    | 13, _ => exact genericN16_step13_check
    | 14, _ => exact genericN16_step14_check
    | 15, _ => exact genericN16_step15_check
    | k + 16, h => exact absurd (show k + 16 < 16 from h) (by omega)

private theorem genericN16PowChain_check :
    Berlekamp.checkPowChainLinearIncremental
      genericN16Mod genericN16Mod_monic genericN16SamePrimeCert = true :=
  Berlekamp.checkPowChainLinearIncremental_of_quotientWitnesses
    genericN16Mod genericN16Mod_monic genericN16SamePrimeCert
    genericN16Quotients genericN16QuotientWitnesses_check

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16_bezout :
    Berlekamp.checkRabinBezoutWitnesses
      genericN16Mod genericN16Mod_monic genericN16SamePrimeCert = true := by
  unfold Berlekamp.checkRabinBezoutWitnesses Berlekamp.checkRabinBezoutWitness
    Berlekamp.certifiedFrobeniusDiffMod
  simp [genericN16SamePrimeCert, genericN16Cert, maxProperDiv_16,
    genericN16Mod, Conway.packedGF2FpPoly, polyP2]
  decide

private theorem genericN16_basisSize :
    genericN16SamePrimeCert.n = Berlekamp.basisSize genericN16Mod := by
  decide

private theorem genericN16_nPos : 0 < genericN16SamePrimeCert.n := by
  decide

private theorem genericN16Mod_modByMonic_X :
    FpPoly.modByMonic genericN16Mod FpPoly.X genericN16Mod_monic = FpPoly.X := by
  rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  apply DensePoly.mod_eq_self_of_degree_lt
  rw [genericN16Mod_degree_eq]
  decide

private theorem polyP2_zero_one_eq_X : (polyP2 #[0, 1] : FpPoly 2) = FpPoly.X := by
  simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, FpPoly.X, DensePoly.monomial,
        DensePoly.trimTrailingZeros, DensePoly.trimTrailingZerosList]
  decide

private theorem genericN16_finalEntry :
    (polyP2 #[0, 1] : FpPoly 2) =
      FpPoly.modByMonic genericN16Mod FpPoly.X genericN16Mod_monic := by
  rw [genericN16Mod_modByMonic_X, polyP2_zero_one_eq_X]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN16Cert_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
        (Conway.packedGF2FpPoly 0x100B 16)
        (by unfold Conway.packedGF2FpPoly; rfl)
        genericN16Cert = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    genericN16Cert, Berlekamp.IrreducibilityCertificate.toAmbient?]
  exact ⟨⟨⟨genericN16_basisSize,
    by simpa [genericN16SamePrimeCert] using genericN16PowChain_check⟩,
    by simpa using genericN16_finalEntry⟩,
    by simpa [genericN16SamePrimeCert] using genericN16_bezout⟩

theorem genericN16_irr :
    FpPoly.Irreducible (Conway.packedGF2FpPoly 0x100B 16) :=
  Berlekamp.rabinTest_imp_irreducible (Conway.packedGF2FpPoly 0x100B 16)
    (by unfold Conway.packedGF2FpPoly; rfl)
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      (Conway.packedGF2FpPoly 0x100B 16)
      (by unfold Conway.packedGF2FpPoly; rfl)
      genericN16Cert
      genericN16Cert_check)

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
  exact genericN16_irr

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

private theorem genericMod_degree_eq : genericMod.degree?.getD 0 = 32 := by
  unfold genericMod Conway.packedGF2FpPoly DensePoly.degree? DensePoly.size
  rfl

private theorem genericMod_degree_pos : 0 < genericMod.degree?.getD 0 := by
  rw [genericMod_degree_eq]; decide

private theorem polyP2_size_le_32 {arr : Array Nat} (h : arr.size ≤ 32) :
    (polyP2 arr).size ≤ genericMod.degree?.getD 0 := by
  rw [genericMod_degree_eq]
  unfold polyP2 FpPoly.ofCoeffs
  exact Nat.le_trans (DensePoly.size_ofCoeffs_le _) (by simpa using h)

#guard
  Berlekamp.quotientStepCoeffCheck 65
    (polyP2 #[0, 1]) (polyP2 #[0, 0, 1]) (polyP2 #[]) genericMod = true

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step0_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 0 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1])
    (curr := polyP2 #[0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step1_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 1 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step2_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 2 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step3_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 3 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step4_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 4 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    (curr := polyP2 #[1, 0, 1, 1, 0, 0, 0, 1])
    (quot := polyP2 #[1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step5_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 5 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 1, 1, 0, 0, 0, 1])
    (curr := polyP2 #[1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step6_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 6 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])
    (curr := polyP2 #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    (quot := polyP2 #[])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step7_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 7 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
    (curr := polyP2 #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1])
    (quot := polyP2 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step8_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 8 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1])
    (curr := polyP2 #[1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1])
    (quot := polyP2 #[0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step9_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 9 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1])
    (curr := polyP2 #[1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1])
    (quot := polyP2 #[0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step10_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 10 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1])
    (curr := polyP2 #[0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1])
    (quot := polyP2 #[1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step11_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 11 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1])
    (curr := polyP2 #[1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1])
    (quot := polyP2 #[1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step12_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 12 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1])
    (curr := polyP2 #[1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1])
    (quot := polyP2 #[0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step13_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 13 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1])
    (curr := polyP2 #[0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1])
    (quot := polyP2 #[1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step14_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 14 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1])
    (curr := polyP2 #[1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1])
    (quot := polyP2 #[1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step15_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 15 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1])
    (curr := polyP2 #[0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1])
    (quot := polyP2 #[1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step16_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 16 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1])
    (curr := polyP2 #[0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1])
    (quot := polyP2 #[0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step17_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 17 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1])
    (curr := polyP2 #[0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1])
    (quot := polyP2 #[0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step18_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 18 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1])
    (curr := polyP2 #[0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1])
    (quot := polyP2 #[0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step19_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 19 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1])
    (curr := polyP2 #[0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1])
    (quot := polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step20_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 20 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1])
    (curr := polyP2 #[0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1])
    (quot := polyP2 #[0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step21_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 21 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1])
    (curr := polyP2 #[0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1])
    (quot := polyP2 #[0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step22_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 22 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1])
    (curr := polyP2 #[1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1])
    (quot := polyP2 #[1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step23_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 23 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1])
    (curr := polyP2 #[1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1])
    (quot := polyP2 #[0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step24_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 24 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1])
    (curr := polyP2 #[1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1])
    (quot := polyP2 #[0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step25_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 25 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1])
    (curr := polyP2 #[1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1])
    (quot := polyP2 #[0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step26_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 26 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1])
    (curr := polyP2 #[1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1])
    (quot := polyP2 #[0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step27_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 27 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1])
    (curr := polyP2 #[1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1])
    (quot := polyP2 #[0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step28_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 28 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1])
    (curr := polyP2 #[1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1])
    (quot := polyP2 #[0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step29_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 29 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1])
    (curr := polyP2 #[0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1])
    (quot := polyP2 #[1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step30_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 30 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1])
    (curr := polyP2 #[0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1])
    (quot := polyP2 #[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
private theorem genericN32_step31_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep
      genericMod genericN32SamePrimeCert genericN32Quotients 31 = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnessStep_of_entry_size_bounds
    (prev := polyP2 #[0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1])
    (curr := polyP2 #[0, 1])
    (quot := polyP2 #[0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1])
  · rfl
  · rfl
  · rfl
  · exact genericMod_degree_pos
  · exact polyP2_size_le_32 (by decide)
  · exact polyP2_size_le_32 (by decide)
  · simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, genericMod,
      Conway.packedGF2FpPoly]
    decide

private theorem genericMod_modByMonic_X :
    FpPoly.modByMonic genericMod FpPoly.X genericMod_monic = FpPoly.X := by
  rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  apply DensePoly.mod_eq_self_of_degree_lt
  rw [genericMod_degree_eq]
  decide

private theorem polyP2_zero_one_eq_X : (polyP2 #[0, 1] : FpPoly 2) = FpPoly.X := by
  simp [polyP2, FpPoly.ofCoeffs, DensePoly.ofCoeffs, FpPoly.X, DensePoly.monomial,
        DensePoly.trimTrailingZeros, DensePoly.trimTrailingZerosList]
  decide

private theorem genericN32QuotientWitnesses_check :
    Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses
      genericMod genericMod_monic genericN32SamePrimeCert
      genericN32Quotients = true := by
  apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses_of_steps
  · decide
  · decide
  · apply Berlekamp.checkPowChainLinearIncrementalQuotientWitnesses_first_of_coeffs
      (first := polyP2 #[0, 1])
    · rfl
    · rw [genericMod_modByMonic_X, polyP2_zero_one_eq_X]
  · intro k hk
    match k, hk with
    | 0, _ => exact genericN32_step0_check
    | 1, _ => exact genericN32_step1_check
    | 2, _ => exact genericN32_step2_check
    | 3, _ => exact genericN32_step3_check
    | 4, _ => exact genericN32_step4_check
    | 5, _ => exact genericN32_step5_check
    | 6, _ => exact genericN32_step6_check
    | 7, _ => exact genericN32_step7_check
    | 8, _ => exact genericN32_step8_check
    | 9, _ => exact genericN32_step9_check
    | 10, _ => exact genericN32_step10_check
    | 11, _ => exact genericN32_step11_check
    | 12, _ => exact genericN32_step12_check
    | 13, _ => exact genericN32_step13_check
    | 14, _ => exact genericN32_step14_check
    | 15, _ => exact genericN32_step15_check
    | 16, _ => exact genericN32_step16_check
    | 17, _ => exact genericN32_step17_check
    | 18, _ => exact genericN32_step18_check
    | 19, _ => exact genericN32_step19_check
    | 20, _ => exact genericN32_step20_check
    | 21, _ => exact genericN32_step21_check
    | 22, _ => exact genericN32_step22_check
    | 23, _ => exact genericN32_step23_check
    | 24, _ => exact genericN32_step24_check
    | 25, _ => exact genericN32_step25_check
    | 26, _ => exact genericN32_step26_check
    | 27, _ => exact genericN32_step27_check
    | 28, _ => exact genericN32_step28_check
    | 29, _ => exact genericN32_step29_check
    | 30, _ => exact genericN32_step30_check
    | 31, _ => exact genericN32_step31_check
    | k + 32, h => exact absurd (show k + 32 < 32 from h) (by omega)

private theorem genericN32PowChain_check :
    Berlekamp.checkPowChainLinearIncremental
      genericMod genericMod_monic genericN32SamePrimeCert = true :=
  Berlekamp.checkPowChainLinearIncremental_of_quotientWitnesses
    genericMod genericMod_monic genericN32SamePrimeCert
    genericN32Quotients genericN32QuotientWitnesses_check

#guard
  Berlekamp.checkRabinBezoutWitnesses
    genericMod genericMod_monic genericN32SamePrimeCert = true

set_option maxRecDepth 65536 in
private theorem genericN32_bezout :
  Berlekamp.checkRabinBezoutWitnesses
    genericMod genericMod_monic genericN32SamePrimeCert = true := by
  unfold Berlekamp.checkRabinBezoutWitnesses Berlekamp.checkRabinBezoutWitness
    Berlekamp.certifiedFrobeniusDiffMod
  rw [genericMod_modByMonic_X]
  simp [genericN32SamePrimeCert, genericN32PowChain, maxProperDiv_32,
    genericMod, Conway.packedGF2FpPoly, lower, n, polyP2]
  decide

private theorem genericN32_basisSize :
    genericN32SamePrimeCert.n = Berlekamp.basisSize genericMod := by
  decide

private theorem genericN32_nPos : 0 < genericN32SamePrimeCert.n := by
  decide

private theorem genericN32_finalEntry :
    genericN32SamePrimeCert.powChain[genericN32SamePrimeCert.n]? =
      some (FpPoly.modByMonic genericMod FpPoly.X genericMod_monic) := by
  rw [genericMod_modByMonic_X]
  rw [← polyP2_zero_one_eq_X]
  rfl

private theorem genericN32Cert_check :
    Berlekamp.checkIrreducibilityCertificateLinearIncremental
      genericMod genericMod_monic genericN32Cert = true := by
  simp [Berlekamp.checkIrreducibilityCertificateLinearIncremental,
    genericN32Cert, Berlekamp.IrreducibilityCertificate.toAmbient?]
  exact ⟨⟨⟨genericN32_basisSize,
    by simpa [genericN32SamePrimeCert] using genericN32PowChain_check⟩,
    by simpa [genericN32SamePrimeCert] using genericN32_finalEntry⟩,
    by simpa [genericN32SamePrimeCert] using genericN32_bezout⟩

private theorem generic_pos : 0 < FpPoly.degree genericMod := by
  decide

private theorem generic_irr : FpPoly.Irreducible genericMod := by
  exact Berlekamp.rabinTest_imp_irreducible genericMod genericMod_monic
    (Berlekamp.checkIrreducibilityCertificateLinearIncremental_rabinTest
      genericMod genericMod_monic genericN32Cert genericN32Cert_check)

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
