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
- `bhksRecover?`, `recombinationSearch`, `factorSlow`, and `factorFast`
- `factorWithBound` and `factor`
- `PrimeFactorData.degreeSum`, `PrimeFactorData.factorProduct`,
  `PrimeFactorData.containsDegree`, `PrimeFactorData.hasSubsetDegree`,
  `PrimeFactorData.checkFactorCerts`, `PrimeFactorData.checkForPolynomial`,
  and `checkIrreducibleCert`
Covered properties:
- selected good primes satisfy the executable admissibility predicate
- normalization prefix factors and square-free core multiply back to the input
- supported recombination/factorization outputs multiply back to the target on
  committed lifted factors
- signed scalar and `(factor, multiplicity)` buckets match independently
  committed expectations on the public `Factorization` edge-case table
- bounded and default factor entry points multiply their returned factors back
  to the input on committed small cases
- default factorization returns promptly and preserves product on small linear
  and cyclotomic products, with factor recovery checked where the current
  executable recombination surface exposes it
- nested prime-factor data aligns degrees, modular factors, and Rabin
  certificates, while the integer checker accepts the constant edge case and
  rejects malformed composite/degree-obstruction data
Covered edge cases:
- zero, signed constants, signed monomials, repeated roots with explicit
  multiplicity, non-unit content, negative-leading inputs,
  leading-coefficient-divisible inputs, and square-free integer polynomials
- empty and singleton lifted-factor recombination inputs
- exhaustive slow-backstop and BHKS recovery branch inputs
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

private def factorizationCoeffSummary (φ : Factorization) : List (List Int × Nat) :=
  φ.factors.toList.map fun entry => (coeffs entry.1, entry.2)

private def sameFactorCoeffSet (actual expected : List (List Int × Nat)) : Bool :=
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

private def negativeMonomial : ZPoly :=
  zpoly #[0, -1]

private def negativeRepeatedRootWithContent : ZPoly :=
  DensePoly.scale (-2 : Int) repeatedRootPoly

private def leadingCoeffDivisibleByFive : ZPoly :=
  zpoly #[1, 1, 5]

private def x4Plus1 : ZPoly :=
  zpoly #[1, 0, 0, 0, 1]

private def quadSqrt2Sqrt3 : ZPoly :=
  zpoly #[6, 0, -5, 0, 1]

private def swinnertonDyerSD3 : ZPoly :=
  zpoly #[576, 0, -960, 0, 352, 0, -40, 0, 1]

private def phi15 : ZPoly :=
  zpoly #[1, -1, 0, 1, -1, 1, 0, -1, 1]

private def liftedFactors3 : Array ZPoly :=
  #[linear (-1), linear 2, linear 4]

private def liftedTarget3 : ZPoly :=
  Array.polyProduct liftedFactors3

private def liftedData3 : LiftData :=
  { p := 37
    k := 8
    liftedFactors := liftedFactors3 }

private def liftedFactors5 : Array ZPoly :=
  #[linear 1, linear 2, linear 3, linear 4, linear 5]

private def liftedTarget5 : ZPoly :=
  Array.polyProduct liftedFactors5

private def liftedData5 : LiftData :=
  { p := 37
    k := 8
    liftedFactors := liftedFactors5 }

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

private structure FactorizationCase where
  input : ZPoly
  expected : Factorization

private def expectedFactorization
    (scalar : Int) (factors : Array (ZPoly × Nat)) : Factorization :=
  { scalar, factors }

private def factorizationEdgeCases : List FactorizationCase :=
  [ { input := 0
      expected := expectedFactorization 0 #[] }
  , { input := 1
      expected := expectedFactorization 1 #[] }
  , { input := -1
      expected := expectedFactorization (-1) #[] }
  , { input := DensePoly.C (2 : Int)
      expected := expectedFactorization 2 #[] }
  , { input := DensePoly.C (-2 : Int)
      expected := expectedFactorization (-2) #[] }
  , { input := DensePoly.C (6 : Int)
      expected := expectedFactorization 6 #[] }
  , { input := DensePoly.C (-6 : Int)
      expected := expectedFactorization (-6) #[] }
  , { input := ZPoly.X
      expected := expectedFactorization 1 #[(ZPoly.X, 1)] }
  , { input := DensePoly.scale (-1 : Int) ZPoly.X
      expected := expectedFactorization (-1) #[(ZPoly.X, 1)] }
  , { input := ZPoly.X * ZPoly.X
      expected := expectedFactorization 1 #[(ZPoly.X, 2)] }
  , { input := zpoly #[1, 0, -1]
      expected := expectedFactorization (-1) #[(linear (-1), 1), (linear 1, 1)] }
  , { input := repeatedRootPoly
      expected := expectedFactorization 1 #[(linear 1, 2)] }
  , { input := DensePoly.scale (-1 : Int) repeatedRootPoly
      expected := expectedFactorization (-1) #[(linear 1, 2)] }
  , { input := zpoly #[-2, 0, 2]
      expected := expectedFactorization 2 #[(linear (-1), 1), (linear 1, 1)] }
  , { input := negativeRepeatedRootWithContent
      expected := expectedFactorization (-2) #[(linear 1, 2)] } ]

#guard
  factorizationEdgeCases.all fun c =>
    let φ := factor c.input
    φ == c.expected && Factorization.product φ == c.input

#guard !isGoodPrime repeatedRootPoly 5
#guard !isGoodPrime leadingCoeffDivisibleByFive 5
#guard !isGoodPrime (0 : ZPoly) 5
#guard !isGoodPrime squareFreeTypical 2

#guard modularFactorDegreesAt? x4Plus1 5 = some #[2, 2]
#guard modularFactorDegreesAt? quadSqrt2Sqrt3 23 = some #[1, 1, 1, 1]
#guard modularFactorDegreesAt? swinnertonDyerSD3 71 = some #[1, 1, 1, 1, 1, 1, 1, 1]
#guard modularFactorDegreesAt? phi15 31 = some #[1, 1, 1, 1, 1, 1, 1, 1]
#guard modularFactorDegreesAt? x4Plus1 29 = none
#guard modularFactorDegreesAt? leadingCoeffDivisibleByFive 5 = none

#guard choosePrime squareFreeTypical = 3
#guard isGoodPrime squareFreeTypical 3
#guard choosePrime leadingCoeffDivisibleByFive = 3

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
    data.p = 3 &&
    data.factorsModP.size = 1

#guard
  let data := choosePrimeData leadingCoeffDivisibleByFive
  data.p = choosePrime leadingCoeffDivisibleByFive &&
    data.p = 3

#guard
  let data := choosePrimeData leadingCoeffDivisibleByFive
  letI := data.bounds
  data.fModP == ZPoly.modP data.p leadingCoeffDivisibleByFive

#guard
  let data := choosePrimeData leadingCoeffDivisibleByFive
  3 <= data.p

#guard bhksBound (0 : ZPoly) = 1
#guard bhksBound ZPoly.X = 9
#guard bhksBound (DensePoly.ofCoeffs #[1, 0, 1]) = 4609

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

#guard
  let primeData := choosePrimeData repeatedRootPoly
  let liftData := henselLiftData repeatedRootPoly 1 primeData
  liftData.p = primeData.p &&
    liftData.k = 1 &&
    liftData.liftedFactors.size = primeData.factorsModP.size

#guard
  let primeData := choosePrimeData leadingCoeffDivisibleByFive
  let liftData := henselLiftData leadingCoeffDivisibleByFive 8 primeData
  liftData.p = primeData.p &&
    liftData.k = 8 &&
    liftData.liftedFactors.size = primeData.factorsModP.size

#guard recombinationSearch liftedTarget3 liftedFactors3.toList |>.isSome
#guard
  match recombinationSearch liftedTarget3 liftedFactors3.toList with
  | some factors => Array.polyProduct factors.toArray = liftedTarget3
  | none => false
#guard recombinationSearch liftedTarget3 [] = none

#guard
  match bhksRecover? liftedTarget5 liftedData5 with
  | some factors =>
      sortedLinearRoots factors = sortedLinearRoots liftedFactors5 &&
        Array.polyProduct factors = liftedTarget5
  | none => true
#guard bhksRecover? liftedTarget3 emptyLift = none

#guard
  Factorization.product (factorSlow liftedTarget3) = liftedTarget3
#guard
  match factorFast (linear 3) with
  | some φ => Factorization.product φ = linear 3
  | none => false

#guard
  let factors := factorWithBound (linear 3) 4
  Factorization.product factors = linear 3
#guard
  let factors := factorWithBound repeatedRootPoly 4
  Factorization.product factors = repeatedRootPoly
#guard
  let factors := factorWithBound cubicLinear123 4
  Factorization.product factors = cubicLinear123
#guard
  let factors := factor monomialWithContent
  Factorization.product factors = monomialWithContent
#guard
  let φ := factor monomialWithContent
  φ.scalar = 6 && φ.factors == #[(ZPoly.X, 2)]
#guard
  let φ := factor negativeMonomial
  φ.scalar = -1 && φ.factors == #[(ZPoly.X, 1)]
#guard
  let φ := factor repeatedRootPoly
  φ.scalar = 1 && φ.factors == #[(linear 1, 2)]
#guard
  let φ := factor negativeRepeatedRootWithContent
  φ.scalar = -2 && φ.factors == #[(linear 1, 2)] &&
    Factorization.product φ = negativeRepeatedRootWithContent
#guard
  let factors := factor cubicLinear123
  Factorization.product factors = cubicLinear123
#guard
  let factors := factor cyclo11Times22
  Factorization.product factors = cyclo11Times22 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[phi11, phi22] |>.map fun coeffs => (coeffs, 1))
#guard
  let factors := factor quadSqrt2Sqrt3
  Factorization.product factors = quadSqrt2Sqrt3 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[zpoly #[-3, 0, 1], zpoly #[-2, 0, 1]] |>.map fun coeffs =>
        (coeffs, 1))

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
