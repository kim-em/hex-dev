import HexBerlekampZassenhaus.Basic

/-!
Core conformance checks for the `HexBerlekampZassenhaus` integer
Berlekamp-Zassenhaus pipeline.

Oracle: python-flint for the external JSONL factorization profile; core uses
Lean-only property and committed-fixture checks.
Mode: if_available
Covered operations:
- `isGoodPrime`, `choosePrime`, and `choosePrimeData`
- `normalizeForFactor`, `normalizationPrefixFactors`, and
  `reassembleNormalizedFactors`
- `henselLiftData`
- `recombineLLL?`, `recombinationSearch`, and `recombine`
- `factorWithBound` and `factor`
- `PrimeFactorData.degreeSum`, `PrimeFactorData.factorProduct`,
  `PrimeFactorData.containsDegree`, `PrimeFactorData.hasSubsetDegree`,
  `PrimeFactorData.checkFactorCerts`, `PrimeFactorData.checkForPolynomial`,
  and `checkIrreducibleCert`
Covered properties:
- selected good primes satisfy the executable admissibility predicate
- normalization prefix factors and square-free core multiply back to the input
- recombination outputs multiply back to the target on committed lifted factors
- bounded and default factor entry points multiply their returned factors back
  to the input on committed small cases
- default factorization returns promptly and preserves product on small linear
  and cyclotomic products, with factor recovery checked where the current
  executable recombination surface exposes it
- nested prime-factor data aligns degrees, modular factors, and Rabin
  certificates, while the integer checker accepts the constant edge case and
  rejects malformed composite/degree-obstruction data
Covered edge cases:
- zero, constant, monomial, repeated-root, leading-coefficient-divisible, and
  square-free integer polynomials
- empty and singleton lifted-factor recombination inputs
- exhaustive fallback and LLL production recombination branch inputs
- valid, wrong-prime, missing-obstruction, malformed-degree, and composite
  integer irreducibility certificates
-/

namespace Hex
namespace BZConformance

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
private instance boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private def zpoly (coeffs : Array Int) : ZPoly :=
  DensePoly.ofCoeffs coeffs

private def linear (r : Int) : ZPoly :=
  zpoly #[-r, 1]

private def fromRoots (roots : List Int) : ZPoly :=
  Array.polyProduct (roots.map linear).toArray

private def coeffs (f : ZPoly) : List Int :=
  f.toArray.toList

private def factorCoeffSummary (factors : Array ZPoly) : List (List Int) :=
  factors.toList.map coeffs

private def sameFactorCoeffSet (actual expected : List (List Int)) : Bool :=
  actual.length == expected.length &&
    expected.all (fun target => actual.any (fun got => got == target)) &&
    actual.all (fun got => expected.any (fun target => got == target))

private def sortedLinearRoots (factors : Array ZPoly) : Array Int :=
  (factors.map fun f => -(f.coeff 0)).qsort (· ≤ ·)

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def unitPolyFive : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5)]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem unitPolyFive_monic : DensePoly.Monic unitPolyFive := by
  rfl

private def irreducibleQuadFive : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem irreducibleQuadFive_monic : DensePoly.Monic irreducibleQuadFive := by
  rfl

private def validQuadCert : Berlekamp.IrreducibilityCertificate where
  p := 5
  n := 2
  powChain := #[polyFive #[0, 1], polyFive #[0, 4], polyFive #[0, 1]]
  bezout :=
    #[{ left := polyFive #[3],
        right := polyFive #[0, 4] }]

private def wrongPrimeQuadCert : Berlekamp.IrreducibilityCertificate where
  p := 7
  n := 2
  powChain := #[FpPoly.ofCoeffs #[(ZMod64.ofNat 7 0), ZMod64.ofNat 7 1]]
  bezout := #[]

private def squareFreeTypical : ZPoly :=
  linear 1

private def repeatedRootPoly : ZPoly :=
  zpoly #[1, -2, 1]

private def monomialWithContent : ZPoly :=
  zpoly #[0, 0, 6]

private def leadingCoeffDivisibleByFive : ZPoly :=
  zpoly #[1, 1, 5]

private def recombineFactors3 : Array ZPoly :=
  #[linear (-1), linear 2, linear 4]

private def recombineTarget3 : ZPoly :=
  Array.polyProduct recombineFactors3

private def recombineLift3 : LiftData :=
  { p := 2
    k := 8
    liftedFactors := recombineFactors3 }

private def recombineFactors5 : Array ZPoly :=
  #[linear 1, linear 2, linear 3, linear 4, linear 5]

private def recombineTarget5 : ZPoly :=
  Array.polyProduct recombineFactors5

private def recombineLift5 : LiftData :=
  { p := 2
    k := 8
    liftedFactors := recombineFactors5 }

private def emptyLift : LiftData :=
  { p := 2
    k := 4
    liftedFactors := #[] }

private def primeDataValidQuad : PrimeFactorData :=
  { p := 5
    factorDegrees := #[2]
    factorPolys := #[irreducibleQuadFive]
    factorCerts := #[validQuadCert] }

private def certValidQuad : ZPolyIrreducibilityCertificate :=
  { perPrime := #[primeDataValidQuad]
    degreeObstructions := #[{ targetDegree := 1, primeIndex := 0 }] }

private def primeDataWrongPrimeCert : PrimeFactorData :=
  { p := 5
    factorDegrees := #[2]
    factorPolys := #[irreducibleQuadFive]
    factorCerts := #[wrongPrimeQuadCert] }

private def certWrongPrime : ZPolyIrreducibilityCertificate :=
  { perPrime := #[primeDataWrongPrimeCert]
    degreeObstructions := #[{ targetDegree := 1, primeIndex := 0 }] }

private def primeDataMalformedDegree : PrimeFactorData :=
  { p := 5
    factorDegrees := #[1]
    factorPolys := #[irreducibleQuadFive]
    factorCerts := #[validQuadCert] }

private def certMalformedDegree : ZPolyIrreducibilityCertificate :=
  { perPrime := #[primeDataMalformedDegree]
    degreeObstructions := #[{ targetDegree := 1, primeIndex := 0 }] }

private def certMissingObstruction : ZPolyIrreducibilityCertificate :=
  { perPrime := #[primeDataValidQuad]
    degreeObstructions := #[] }

private def constantCert : ZPolyIrreducibilityCertificate :=
  { perPrime := #[]
    degreeObstructions := #[] }

private def cubicLinear123 : ZPoly :=
  fromRoots [1, 2, 3]

private def phi11 : ZPoly :=
  zpoly #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

private def phi22 : ZPoly :=
  zpoly #[1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1]

private def cyclo11Times22 : ZPoly :=
  phi11 * phi22

#guard !isGoodPrime repeatedRootPoly 5
#guard !isGoodPrime leadingCoeffDivisibleByFive 5
#guard !isGoodPrime (0 : ZPoly) 5

#guard choosePrime squareFreeTypical = 2
#guard isGoodPrime squareFreeTypical 2
#guard choosePrime leadingCoeffDivisibleByFive = 2

#guard
  let data := choosePrimeData squareFreeTypical
  letI := data.bounds
  data.p = choosePrime squareFreeTypical &&
    data.fModP == ZPoly.modP data.p squareFreeTypical &&
    !data.factorsModP.isEmpty

#guard
  let data := choosePrimeData repeatedRootPoly
  letI := data.bounds
  data.p = choosePrime repeatedRootPoly &&
    data.fModP == ZPoly.modP data.p repeatedRootPoly &&
    data.p = 2 &&
    data.factorsModP.size = 1

#guard
  let data := normalizeForFactor monomialWithContent
  data.content = 6 &&
    data.xPower = 2 &&
    data.squareFreeCore = 1 &&
    Array.polyProduct (normalizationPrefixFactors data ++ #[data.squareFreeCore]) =
      monomialWithContent

#guard
  let data := normalizeForFactor repeatedRootPoly
  data.content = 1 &&
    data.xPower = 0 &&
    data.squareFreeCore = linear 1 &&
    data.repeatedPart = linear 1 &&
    Array.polyProduct (normalizationPrefixFactors data ++ #[data.squareFreeCore]) =
      repeatedRootPoly

#guard
  let data := normalizeForFactor squareFreeTypical
  data.content = 1 &&
    data.xPower = 0 &&
    data.repeatedPart = 1 &&
    Array.polyProduct (reassembleNormalizedFactors data #[data.squareFreeCore]) =
      squareFreeTypical

#guard
  let primeData := choosePrimeData squareFreeTypical
  let liftData := henselLiftData squareFreeTypical 4 primeData
  liftData.p = primeData.p &&
    liftData.k = 4 &&
    liftData.liftedFactors.size = primeData.factorsModP.size

#guard recombinationSearch recombineTarget3 recombineFactors3.toList |>.isSome
#guard
  match recombinationSearch recombineTarget3 recombineFactors3.toList with
  | some factors => Array.polyProduct factors.toArray = recombineTarget3
  | none => false
#guard recombinationSearch recombineTarget3 [] = none

#guard recombineLLL? recombineTarget5 recombineLift5 |>.isSome
#guard
  match recombineLLL? recombineTarget5 recombineLift5 with
  | some factors =>
      sortedLinearRoots factors = sortedLinearRoots recombineFactors5 &&
        Array.polyProduct factors = recombineTarget5
  | none => false
#guard recombineLLL? recombineTarget3 emptyLift = none

#guard factorCoeffSummary (recombine recombineTarget3 recombineLift3) =
  factorCoeffSummary recombineFactors3
#guard
  Array.polyProduct (recombine recombineTarget5 recombineLift5) =
    recombineTarget5

#guard
  let factors := factorWithBound (linear 3) 4
  Array.polyProduct factors = linear 3
#guard
  let factors := factorWithBound repeatedRootPoly 4
  Array.polyProduct factors = repeatedRootPoly
#guard
  let factors := factor monomialWithContent
  Array.polyProduct factors = monomialWithContent
#guard
  let factors := factor cubicLinear123
  Array.polyProduct factors = cubicLinear123
#guard
  let factors := factor cyclo11Times22
  Array.polyProduct factors = cyclo11Times22 &&
    sameFactorCoeffSet (factorCoeffSummary factors)
      (factorCoeffSummary #[phi11, phi22])

#guard PrimeFactorData.degreeSum primeDataValidQuad = 2
#guard coeffNats (PrimeFactorData.factorProduct primeDataValidQuad) = [2, 0, 1]
#guard PrimeFactorData.containsDegree primeDataValidQuad 2
#guard !PrimeFactorData.containsDegree primeDataValidQuad 1
#guard !PrimeFactorData.hasSubsetDegree primeDataValidQuad 1
#guard PrimeFactorData.hasSubsetDegree primeDataValidQuad 2
#guard PrimeFactorData.checkFactorCerts primeDataValidQuad
#guard !PrimeFactorData.checkForPolynomial (zpoly #[2, 0, 1]) primeDataValidQuad
#guard checkIrreducibleCert 1 constantCert

#guard !PrimeFactorData.checkFactorCerts primeDataWrongPrimeCert
#guard !checkIrreducibleCert (zpoly #[2, 0, 1]) certWrongPrime
#guard !PrimeFactorData.checkFactorCerts primeDataMalformedDegree
#guard !checkIrreducibleCert (zpoly #[2, 0, 1]) certMalformedDegree
#guard !checkIrreducibleCert (zpoly #[2, 0, 1]) certMissingObstruction
#guard !checkIrreducibleCert (zpoly #[1, -3, 2]) certValidQuad

end BZConformance
end Hex
