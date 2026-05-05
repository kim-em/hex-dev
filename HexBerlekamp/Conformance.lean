import HexBerlekamp.DistinctDegree

/-!
Core conformance checks for the `HexBerlekamp` Berlekamp, Rabin
irreducibility, certificate-checker, split-step, and distinct-degree surface.

Oracle: FLINT or Sage for external factorisation profiles; core uses Lean-only
property checks.
Mode: if_available
Covered operations:
- `basisSize`, `coeffVector`, `berlekampColumn`, `berlekampMatrix`, and
  `fixedSpaceMatrix`
- `properDivisors`, `maximalProperDivisors`, `frobeniusDiffMod`,
  `rabinDividesTest`, `rabinCoprimeTest`, `rabinWitnesses`, and `rabinTest`
- `checkPowChain`, `checkRabinBezoutWitness`,
  `checkRabinBezoutWitnesses`, and `checkIrreducibilityCertificate`
- `splitFactorAt` and `kernelWitnessSplit?`
- `distinctDegreeCandidate`, `distinctDegreeStep`, and `distinctDegreeFactor`
Covered properties:
- Berlekamp fixed-space matrices subtract the identity from the Frobenius matrix
- Rabin witnesses agree with the per-divisor coprimality checks
- accepted irreducibility certificates have matching pow chains and Bezout
  witnesses, while malformed certificates are rejected
- successful split witnesses multiply back to the split input
- distinct-degree factorization products reconstruct the committed input
Covered edge cases:
- constant, linear, irreducible quadratic, and reducible quadratic inputs over
  `F_5`
- composite degree divisor lists and prime degree divisor lists
- missing pow-chain and wrong-prime certificate data
- split searches with no nontrivial factor, a linear edge input, and a
  reducible quadratic adversarial input
- distinct-degree runs with a unit residual and a degree-8 product of linear,
  quadratic, and quintic irreducibles (Artin-Schreier `x^5 - x - 1` over `F_5`)
-/

namespace Hex
namespace BerlekampConformance

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def vectorNats {n : Nat} (v : Vector (ZMod64 5) n) : List Nat :=
  v.toArray.toList.map ZMod64.toNat

private def matrixNats {n m : Nat} (M : Matrix (ZMod64 5) n m) : List (List Nat) :=
  M.toArray.toList.map vectorNats

private def splitSummary (result : Option (Berlekamp.SplitResult 5)) :
    Option (Nat × List Nat × List Nat) :=
  result.map fun split =>
    (split.splitConstant.toNat, coeffNats split.factor, coeffNats split.cofactor)

private def bucketSummary (buckets : List (Berlekamp.DegreeBucket 5)) :
    List (Nat × List Nat) :=
  buckets.map fun bucket => (bucket.degree, coeffNats bucket.factor)

private def ddfSummary (result : Berlekamp.DistinctDegreeFactorization 5) :
    List (Nat × List Nat) × List Nat :=
  (bucketSummary result.buckets, coeffNats result.residual)

private def unitPoly : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5)]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem unitPoly_monic : DensePoly.Monic unitPoly := by
  rfl

private def linearPoly : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5), 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem linearPoly_monic : DensePoly.Monic linearPoly := by
  rfl

private def irreducibleQuad : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem irreducibleQuad_monic : DensePoly.Monic irreducibleQuad := by
  rfl

private def reducibleQuad : FpPoly 5 :=
  { coeffs := #[(4 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem reducibleQuad_monic : DensePoly.Monic reducibleQuad := by
  rfl

/--
`x^5 - x - 1 = 4 + 4x + x^5` over `F_5`.  Irreducible by Artin-Schreier:
`x^p - x - a` is irreducible over `F_p` whenever `a ≠ 0`.
-/
private def irreducibleQuint : FpPoly 5 :=
  { coeffs := #[(4 : ZMod64 5), 4, 0, 0, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem irreducibleQuint_monic : DensePoly.Monic irreducibleQuint := by
  rfl

/--
Degree-8 product `(1 + x) * (2 + x^2) * (x^5 - x - 1)` over `F_5`, expanded
to `3 + x + 2x² + 3x³ + 4x⁴ + 2x⁵ + 2x⁶ + x⁷ + x⁸`.  The three factors are
irreducible of distinct degrees `1`, `2`, `5`, so the distinct-degree
factorization separates them into one bucket each with unit residual.

Stored in expanded form (rather than as the symbolic product) so the monic
proof reduces by `rfl` without unfolding the schoolbook multiplication.
-/
private def bigPoly : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 1, 2, 3, 4, 2, 2, 1, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem bigPoly_monic : DensePoly.Monic bigPoly := by
  rfl

set_option maxRecDepth 2048 in
#guard bigPoly == linearPoly * irreducibleQuad * irreducibleQuint

#guard Berlekamp.basisSize irreducibleQuad = 2
#guard Berlekamp.basisSize linearPoly = 1
#guard Berlekamp.basisSize (0 : FpPoly 5) = 0

#guard vectorNats (Berlekamp.coeffVector irreducibleQuad (polyFive #[4, 3, 1])) = [4, 3]
#guard vectorNats (Berlekamp.coeffVector linearPoly (polyFive #[2, 1])) = [2]
#guard vectorNats (Berlekamp.coeffVector unitPoly (polyFive #[2, 0, 3])) = []

#guard vectorNats
    (Berlekamp.berlekampColumn irreducibleQuad irreducibleQuad_monic ⟨0, by decide⟩) =
  [1, 0]
#guard vectorNats
    (Berlekamp.berlekampColumn irreducibleQuad irreducibleQuad_monic ⟨1, by decide⟩) =
  [0, 4]
#guard vectorNats
    (Berlekamp.berlekampColumn linearPoly linearPoly_monic ⟨0, by decide⟩) =
  [1]

#guard matrixNats (Berlekamp.berlekampMatrix irreducibleQuad irreducibleQuad_monic) =
  [[1, 0], [0, 4]]
#guard matrixNats (Berlekamp.fixedSpaceMatrix irreducibleQuad irreducibleQuad_monic) =
  [[0, 0], [0, 3]]
#guard
  let Q := Berlekamp.berlekampMatrix reducibleQuad reducibleQuad_monic
  let F := Berlekamp.fixedSpaceMatrix reducibleQuad reducibleQuad_monic
  (List.finRange (Berlekamp.basisSize reducibleQuad)).all fun i =>
    (List.finRange (Berlekamp.basisSize reducibleQuad)).all fun j =>
      F[i][j] == Q[i][j] - if i = j then 1 else 0

#guard Berlekamp.properDivisors 6 = [1, 2, 3]
#guard Berlekamp.maximalProperDivisors 6 = [2, 3]
#guard Berlekamp.maximalProperDivisors 5 = [1]

#guard coeffNats (Berlekamp.frobeniusDiffMod irreducibleQuad irreducibleQuad_monic 0) = []
#guard coeffNats (Berlekamp.frobeniusDiffMod irreducibleQuad irreducibleQuad_monic 1) = [0, 3]
#guard coeffNats (Berlekamp.frobeniusDiffMod reducibleQuad reducibleQuad_monic 1) = []

#guard Berlekamp.rabinDividesTest irreducibleQuad irreducibleQuad_monic
#guard Berlekamp.rabinDividesTest linearPoly linearPoly_monic
#guard Berlekamp.rabinDividesTest reducibleQuad reducibleQuad_monic

#guard Berlekamp.rabinCoprimeTest irreducibleQuad irreducibleQuad_monic 1
#guard !Berlekamp.rabinCoprimeTest reducibleQuad reducibleQuad_monic 1
#guard Berlekamp.rabinWitnesses irreducibleQuad irreducibleQuad_monic = [(1, true)]
#guard Berlekamp.rabinWitnesses reducibleQuad reducibleQuad_monic = [(1, false)]
#guard
  (Berlekamp.rabinWitnesses irreducibleQuad irreducibleQuad_monic).all Prod.snd =
    (Berlekamp.maximalProperDivisors (Berlekamp.basisSize irreducibleQuad)).all
      (Berlekamp.rabinCoprimeTest irreducibleQuad irreducibleQuad_monic)

private def validQuadCert : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4], polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

private def shortPowCert : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

private def wrongPrimeCert : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(ZMod64.ofNat 7 0), ZMod64.ofNat 7 1]]
  bezout := #[]

private def samePrimeValidCert : Berlekamp.SamePrimeIrreducibilityCertificate 5 where
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4], polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

#guard Berlekamp.checkPowChain irreducibleQuad irreducibleQuad_monic samePrimeValidCert
#guard
  Berlekamp.checkRabinBezoutWitness irreducibleQuad irreducibleQuad_monic
    samePrimeValidCert 0 1
#guard
  Berlekamp.checkRabinBezoutWitnesses irreducibleQuad irreducibleQuad_monic
    samePrimeValidCert
#guard Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic validQuadCert
#guard !Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic shortPowCert
#guard !Berlekamp.checkIrreducibilityCertificate irreducibleQuad irreducibleQuad_monic wrongPrimeCert

#guard coeffNats (Berlekamp.splitFactorAt reducibleQuad FpPoly.X (ZMod64.ofNat 5 1)) =
  [4, 1]
#guard coeffNats (Berlekamp.splitFactorAt linearPoly FpPoly.X (ZMod64.ofNat 5 1)) =
  [2]
#guard coeffNats (Berlekamp.splitFactorAt irreducibleQuad FpPoly.X (ZMod64.ofNat 5 1)) =
  [3]

#guard splitSummary (Berlekamp.kernelWitnessSplit? reducibleQuad FpPoly.X) =
  some (1, [4, 1], [1, 1])
#guard splitSummary (Berlekamp.kernelWitnessSplit? linearPoly FpPoly.X) = none
#guard splitSummary (Berlekamp.kernelWitnessSplit? irreducibleQuad FpPoly.X) = none
#guard
  match Berlekamp.kernelWitnessSplit? reducibleQuad FpPoly.X with
  | some split => split.factor * split.cofactor == reducibleQuad
  | none => false

#guard Berlekamp.basisSize bigPoly = 8
#guard vectorNats (Berlekamp.coeffVector bigPoly bigPoly) = [3, 1, 2, 3, 4, 2, 2, 1]

#guard
  let Q := Berlekamp.berlekampMatrix bigPoly bigPoly_monic
  let F := Berlekamp.fixedSpaceMatrix bigPoly bigPoly_monic
  (List.finRange (Berlekamp.basisSize bigPoly)).all fun i =>
    (List.finRange (Berlekamp.basisSize bigPoly)).all fun j =>
      F[i][j] == Q[i][j] - if i = j then 1 else 0

-- `X^5 - X` has degree `5 < 8 = deg bigPoly`, so the reduction is the identity
-- and the result is just `-X + X^5 = 4X + X^5` over `F_5`.
#guard coeffNats (Berlekamp.frobeniusDiffMod bigPoly bigPoly_monic 1) =
  [0, 4, 0, 0, 0, 1]

-- `bigPoly(4) = 0` because `linearPoly = 1 + x` vanishes at `x = -1 ≡ 4`.
-- `gcd(bigPoly, X - 4) = X + 1 = [1, 1]`.
#guard coeffNats (Berlekamp.splitFactorAt bigPoly FpPoly.X (ZMod64.ofNat 5 4)) =
  [1, 1]

#guard
  match Berlekamp.kernelWitnessSplit? bigPoly FpPoly.X with
  | some split => split.factor * split.cofactor == bigPoly
  | none => false

-- DDF on `bigPoly` recovers the three irreducible factors.  The EEA-based
-- `DensePoly.gcd` returns each gcd up to a unit scalar, so we phrase the
-- bucket test as a degree match plus a structural product reconstruction
-- rather than pinning literal coefficients.
#guard
  let result := Berlekamp.distinctDegreeFactor bigPoly bigPoly_monic
  result.buckets.map Berlekamp.DegreeBucket.degree = [1, 2, 5]
#guard
  let result := Berlekamp.distinctDegreeFactor bigPoly bigPoly_monic
  result.product == bigPoly
#guard
  let result := Berlekamp.distinctDegreeFactor bigPoly bigPoly_monic
  Berlekamp.isUnitPolynomial result.residual
#guard ddfSummary (Berlekamp.distinctDegreeFactor irreducibleQuad irreducibleQuad_monic) =
  ([(2, [2, 0, 1])], [1])
#guard ddfSummary (Berlekamp.distinctDegreeFactor unitPoly unitPoly_monic) =
  ([], [1])

end BerlekampConformance
end Hex
