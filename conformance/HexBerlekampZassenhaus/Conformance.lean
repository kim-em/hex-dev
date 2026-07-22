/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus

/-!
Core conformance checks for the `HexBerlekampZassenhaus` integer
Berlekamp-Zassenhaus pipeline.

Oracle: python-flint for the external JSONL factorization profile; core uses
Lean-only property and committed-fixture checks.
Mode: if_available
Covered operations:
- `isGoodPrime`, `choosePrime`, and `choosePrimeData?`
- `normalizeForFactor`, `normalizationPrefixFactors`, and
  `reassembleNormalizedFactors`
- `henselLiftData`
- `bhksRecover?`, `recombinationSearch`, `factorTrial`,
  and `factorClassicalNoDecline`
- `factor`
- `PrimeFactorData.degreeSum`, `PrimeFactorData.factorProduct`,
  `PrimeFactorData.containsDegree`, `PrimeFactorData.hasSubsetDegree`,
  `PrimeFactorData.checkFactorCerts`, `PrimeFactorData.checkForPolynomial`,
  and `checkIrreducibleCert`
Covered properties:
- selected good primes satisfy the executable admissibility predicate
- normalization prefix factors and square-free core multiply back to the input
- supported recombination/factorization outputs multiply back to the target on
  committed lifted factors
- adversarial modular split cases exercise non-trivial subset-product
  recombination buckets
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
- four-way modular split inputs whose integer factors are quadratic subset
  products
- eight-way modular split inputs (`swinnertonDyerSD3`, `phi15`) that are
  irreducible over `ℤ`, where every `2^8` subset product is rejected and the
  modular backstop and public `factor` fall back to the single input
- valid, wrong-prime, missing-obstruction, malformed-degree, and composite
  integer irreducibility certificates
-/

namespace Hex
namespace BZConformance

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsTwo : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
private instance boundsThree : ZMod64.Bounds 3 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩
private instance boundsTwentyThree : ZMod64.Bounds 23 := ⟨by decide, by decide⟩

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

/-- Order-insensitive comparison for factor coefficient lists with multiplicities.
The public contract treats factor order as operational, not mathematical, so
conformance guards compare the coefficient/multiplicity buckets as a multiset. -/
private def sameFactorCoeffSet (actual expected : List (List Int × Nat)) : Bool :=
  actual.length == expected.length &&
    expected.all (fun target => actual.any (fun got => got == target)) &&
    actual.all (fun got => expected.any (fun target => got == target))

/-- Product preservation guard for the public default `factor` entry point. -/
private def factorPreservesProduct (f : ZPoly) : Bool :=
  Factorization.product (ZPoly.factorize f) = f

private def sameCoeffSet (actual expected : List (List Int)) : Bool :=
  actual.length == expected.length &&
    expected.all (fun target => actual.any (fun got => got == target)) &&
    actual.all (fun got => expected.any (fun target => got == target))

private def sortedLinearRoots (factors : Array ZPoly) : Array Int :=
  (factors.map fun f => -(f.coeff 0)).qsort (· ≤ ·)

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def polyTwentyThree (coeffs : Array Nat) : FpPoly 23 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 23 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def unitPolyFive : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5)]
    normalized := by
      right
      decide }

private theorem unitPolyFive_monic : DensePoly.Monic unitPolyFive := by
  rfl

private def irreducibleQuadFive : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      decide }

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

/-! ## Adversarial modular split cases (HO-2, #2565)

These named polynomials exercise the SPEC-required shapes from
`SPEC/Libraries/hex-berlekamp-zassenhaus.md` §"Conformance fixtures":
at least one input where the integer factors require a non-trivial subset
product of lifted mod-p factors, and at least one input that splits heavily
(≥ 4 distinct mod-p factors) over a small admissible prime.

The Lean-only guards below check the local modular split facts and, where
the executable BHKS recovery surface exposes it, the recombined integer
factor buckets.  The companion `EmitFixtures.lean` driver emits the same
four polynomials as `adv/quad_sqrt2_sqrt3`, `adv/x4_plus_1`,
`adv/swinnerton_dyer_sd3`, and `adv/phi15` with pinned
`modFactorPrime` / `modFactorDegrees` so `scripts/oracle/bz_flint.py`
independently verifies the named modular split via `nmod_poly.factor`. -/

private def x4Plus1 : ZPoly :=
  zpoly #[1, 0, 0, 0, 1]

private def quadSqrt2Sqrt3 : ZPoly :=
  zpoly #[6, 0, -5, 0, 1]

private def quadSqrt2Sqrt3PrimeData23 : PrimeChoiceData :=
  { p := 23
    fModP := ZPoly.modP 23 quadSqrt2Sqrt3
    factorsModP :=
      #[ polyTwentyThree #[18, 1]
       , polyTwentyThree #[5, 1]
       , polyTwentyThree #[16, 1]
       , polyTwentyThree #[7, 1] ] }

private def quadSqrt2Sqrt3LiftData23 : LiftData :=
  henselLiftData quadSqrt2Sqrt3 4 quadSqrt2Sqrt3PrimeData23

private def quadSqrt2Sqrt3ExpectedFactors : Array ZPoly :=
  #[zpoly #[-2, 0, 1], zpoly #[-3, 0, 1]]

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
    p_pos := by decide
    k := 8
    liftedFactors := liftedFactors3 }

private def liftedFactors5 : Array ZPoly :=
  #[linear 1, linear 2, linear 3, linear 4, linear 5]

private def liftedTarget5 : ZPoly :=
  Array.polyProduct liftedFactors5

private def liftedData5 : LiftData :=
  { p := 37
    p_pos := by decide
    k := 8
    liftedFactors := liftedFactors5 }

private def emptyLift : LiftData :=
  { p := 2
    p_pos := by decide
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

/-- Edge-case table guard: expected signed scalar/multiplicity buckets and
exact product preservation must both hold for the public `factor` output. -/
private def factorizationCaseMatches (c : FactorizationCase) : Bool :=
  let φ := ZPoly.factorize c.input
  φ == c.expected && Factorization.product φ == c.input

#guard
  factorizationEdgeCases.all factorizationCaseMatches

#guard !isGoodPrime repeatedRootPoly 5
#guard !isGoodPrime leadingCoeffDivisibleByFive 5
#guard !isGoodPrime (0 : ZPoly) 5
#guard !isGoodPrime squareFreeTypical 2

#guard modularFactorDegreesAt? x4Plus1 5 = some #[2, 2]
#guard modularFactorDegreesAt? quadSqrt2Sqrt3 23 = some #[1, 1, 1, 1]
#guard modularFactorDegreesAt? swinnertonDyerSD3 71 = some #[1, 1, 1, 1, 1, 1, 1, 1]
#guard modularFactorDegreesAt? phi15 31 = some #[1, 1, 1, 1, 1, 1, 1, 1]
#guard modularFactorDegreesAt? x4Plus1 29 = some #[2, 2]
#guard modularFactorDegreesAt? leadingCoeffDivisibleByFive 5 = none

#guard choosePrime squareFreeTypical = 3
#guard isGoodPrime squareFreeTypical 3
#guard choosePrime leadingCoeffDivisibleByFive = 3

#guard
  match choosePrimeData? squareFreeTypical with
  | none => false
  | some data =>
    letI := data.bounds
    data.p = choosePrime squareFreeTypical &&
      data.fModP == ZPoly.modP data.p squareFreeTypical &&
      !data.factorsModP.isEmpty

-- `repeatedRootPoly = (x - 1)²` has no admissible prime: its modular image
-- stays a perfect square mod every candidate, so `isGoodPrime` rejects each
-- one. Confirm the partial API surfaces this as `none`.
#guard
  match choosePrimeData? repeatedRootPoly with
  | none => true
  | some _ => false

#guard
  match choosePrimeData? leadingCoeffDivisibleByFive with
  | none => false
  | some data =>
    data.p = choosePrime leadingCoeffDivisibleByFive &&
      data.p = 3

#guard
  match choosePrimeData? leadingCoeffDivisibleByFive with
  | none => false
  | some data =>
    letI := data.bounds
    data.fModP == ZPoly.modP data.p leadingCoeffDivisibleByFive

#guard
  match choosePrimeData? leadingCoeffDivisibleByFive with
  | none => false
  | some data => 3 <= data.p

/-! ### Extended-search cascade (HO-5d-3, #5819)

The `(x-1)(x-2)…(x-n)` cascade exhausts the historical fixed prefix once
`n ≥ 72`, because then every old prefix prime had a colliding residue pair
somewhere in `{1, ..., n}` and the modular image failed the square-free
predicate. Materializing the degree-72 input via `fromRoots` in kernel
reduction time is prohibitively slow (~10 minutes of `#guard` cost), so the
fixture instead uses the engineered degree-2 cascade
`(x - 1)(x - (1 + D))` with `D = product p` over the old fixed-list primes
`p ∈ {3, 5, 7, 11, 13, 17, 19, 23, 31, 71}`. The expanded SPEC prefix now
includes `29`, and `D mod 29 ≠ 0`, so `choosePrimeData?` reaches the new
candidate instead of falling through to the post-prefix range.
-/

/-- Product of the fixed-list primes, used to engineer the extended-
search cascade fixture. -/
private def fixedPrimeProduct : Int :=
  3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 31 * 71

private def extendedCascade2 : ZPoly :=
  fromRoots [1, 1 + fixedPrimeProduct]

#guard
  match choosePrimeData? extendedCascade2 with
  | none => false
  | some data => data.p == 29

#guard
  match choosePrimeData? extendedCascade2 with
  | none => false
  | some data => 29 ≤ data.p

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
  match choosePrimeData? squareFreeTypical with
  | none => false
  | some primeData =>
    let liftData := henselLiftData squareFreeTypical 4 primeData
    liftData.p = primeData.p &&
      liftData.k = 4 &&
      liftData.liftedFactors.size = primeData.factorsModP.size

#guard
  match choosePrimeData? leadingCoeffDivisibleByFive with
  | none => false
  | some primeData =>
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

/-
Non-monic recovered-candidate guard for `core = 2X² + 3X + 1` at `p = 3`,
`k = 2` (`p ^ k = 9`).  This exercises the corrected recovered-candidate model
(`liftedRecoveryCandidate` / `RecoveredAtLift` on the Mathlib side, mirrored by
the per-step candidate of `scaledRecombinationSearchModAux` here): the centred
lifted product is dilated by the integer leading coefficient before the
primitive part is taken, so the model recovers genuine integer factors of a
non-monic core rather than monic-coordinate witnesses.

The monic transform `toMonic core = X² + 3X + 2` splits as `(X+1)(X+2)`; lifting
each centred factor and dilating by `coreLc = 2` recovers the true integer
factors `2X+1` and `X+1`, whose product is `core`.  An obvious non-factor
(`2X+3`) is rejected by the exact-division check, distinguishing it from the
recovered true factor.
-/
#guard
  let core := zpoly #[1, 3, 2]          -- 2X² + 3X + 1
  let coreLc := (2 : Int)
  let modulus := 9                      -- p ^ k = 3 ^ 2
  let liftedFactors := [zpoly #[1, 1], zpoly #[2, 1]]   -- X+1, X+2
  let recovered := normalizeFactorSign <| ZPoly.primitivePart <|
    ZPoly.dilate coreLc <| centeredLiftPoly (zpoly #[1, 1]) modulus
  recovered = zpoly #[1, 2]                            -- 2X + 1, a true factor
    && (exactQuotient? core recovered).isSome          -- ... which divides core
    && (exactQuotient? core (zpoly #[3, 2])).isNone    -- 2X + 3 is not a factor
    && (match scaledRecombinationSearchMod coreLc core modulus liftedFactors with
        | some factors => Array.polyProduct factors.toArray = core
        | none => false)

#guard
  match bhksRecover? liftedTarget5 liftedData5 with
  | some factors =>
      sortedLinearRoots factors = sortedLinearRoots liftedFactors5 &&
        Array.polyProduct factors = liftedTarget5
  | none => true
#guard bhksRecover? liftedTarget3 emptyLift = none
#guard quadSqrt2Sqrt3LiftData23.liftedFactors.size = 4
#guard
  match bhksRecover? quadSqrt2Sqrt3 quadSqrt2Sqrt3LiftData23 with
  | some factors =>
      factors.size = 2 &&
        Array.polyProduct factors = quadSqrt2Sqrt3 &&
        sameCoeffSet (factorCoeffSummary factors)
          (factorCoeffSummary quadSqrt2Sqrt3ExpectedFactors)
  | none => false

#guard
  Factorization.product (factorTrial liftedTarget3) = liftedTarget3
#guard
  let φ := factorTrial quadSqrt2Sqrt3
  Factorization.product φ = quadSqrt2Sqrt3 &&
    sameFactorCoeffSet (factorizationCoeffSummary φ)
      (factorCoeffSummary quadSqrt2Sqrt3ExpectedFactors |>.map fun coeffs =>
        (coeffs, 1))
-- Size-ordered full classical recombination (the complete subset-product search,
-- with the level-aware early decline disabled) recovers the same quadratic
-- buckets `X^2 - 2`, `X^2 - 3` on the adversarial subset-product case.
#guard
  match factorClassicalNoDecline quadSqrt2Sqrt3 with
  | some φ =>
      Factorization.product φ = quadSqrt2Sqrt3 &&
        sameFactorCoeffSet (factorizationCoeffSummary φ)
          (factorCoeffSummary quadSqrt2Sqrt3ExpectedFactors |>.map fun coeffs =>
            (coeffs, 1))
  | none => false
#guard
  let factors := ZPoly.factorize monomialWithContent
  Factorization.product factors = monomialWithContent
#guard
  let φ := ZPoly.factorize monomialWithContent
  φ.scalar = 6 && φ.factors == #[(ZPoly.X, 2)]
#guard
  let φ := ZPoly.factorize negativeMonomial
  φ.scalar = -1 && φ.factors == #[(ZPoly.X, 1)]
#guard
  let φ := ZPoly.factorize repeatedRootPoly
  φ.scalar = 1 && φ.factors == #[(linear 1, 2)]
#guard
  let φ := ZPoly.factorize negativeRepeatedRootWithContent
  φ.scalar = -2 && φ.factors == #[(linear 1, 2)] &&
    Factorization.product φ = negativeRepeatedRootWithContent
#guard
  factorPreservesProduct cubicLinear123
#guard
  let factors := ZPoly.factorize cyclo11Times22
  factorPreservesProduct cyclo11Times22 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[phi11, phi22] |>.map fun coeffs => (coeffs, 1))
#guard
  let factors := ZPoly.factorize quadSqrt2Sqrt3
  factorPreservesProduct quadSqrt2Sqrt3 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[zpoly #[-3, 0, 1], zpoly #[-2, 0, 1]] |>.map fun coeffs =>
        (coeffs, 1))
-- `X^4 + 1` splits into two quadratics mod every admissible prime yet is
-- irreducible over `ℤ`, so the fast recombination "misses" and the public
-- `factor` falls back to returning the single irreducible input.
#guard
  let factors := ZPoly.factorize x4Plus1
  factorPreservesProduct x4Plus1 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[x4Plus1] |>.map fun coeffs => (coeffs, 1))

-- Heavy (8-way split) adversarial backstop cases: `swinnertonDyerSD3` and
-- `phi15` each split into eight linear factors over their small admissible
-- prime yet are irreducible over `ℤ`.  Size-ordered full classical recombination
-- must reject every one of the `2^8` proper subset products and fall back to
-- the single irreducible input. This is the genuine worst case for "no
-- spurious recombination," dual to the `quadSqrt2Sqrt3` / `x4Plus1` guards
-- above.
#guard
  match factorClassicalNoDecline swinnertonDyerSD3 with
  | some φ =>
      Factorization.product φ = swinnertonDyerSD3 &&
        sameFactorCoeffSet (factorizationCoeffSummary φ)
          (factorCoeffSummary #[swinnertonDyerSD3] |>.map fun coeffs => (coeffs, 1))
  | none => false
#guard
  let factors := ZPoly.factorize swinnertonDyerSD3
  factorPreservesProduct swinnertonDyerSD3 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[swinnertonDyerSD3] |>.map fun coeffs => (coeffs, 1))
#guard
  match factorClassicalNoDecline phi15 with
  | some φ =>
      Factorization.product φ = phi15 &&
        sameFactorCoeffSet (factorizationCoeffSummary φ)
          (factorCoeffSummary #[phi15] |>.map fun coeffs => (coeffs, 1))
  | none => false
#guard
  let factors := ZPoly.factorize phi15
  factorPreservesProduct phi15 &&
    sameFactorCoeffSet (factorizationCoeffSummary factors)
      (factorCoeffSummary #[phi15] |>.map fun coeffs => (coeffs, 1))

#guard PrimeFactorData.degreeSum primeDataValidQuad = 2
#guard coeffNats (PrimeFactorData.factorProduct primeDataValidQuad) = [2, 0, 1]
#guard PrimeFactorData.containsDegree primeDataValidQuad 2
#guard !PrimeFactorData.containsDegree primeDataValidQuad 1
#guard !PrimeFactorData.hasSubsetDegree primeDataValidQuad 1
#guard PrimeFactorData.hasSubsetDegree primeDataValidQuad 2
#guard PrimeFactorData.checkFactorCerts primeDataValidQuad
#guard PrimeFactorData.checkForPolynomial (zpoly #[2, 0, 1]) primeDataValidQuad
#guard !PrimeFactorData.checkForPolynomial (zpoly #[1, 0, 1]) primeDataValidQuad
#guard checkIrreducibleCert 1 constantCert

#guard !PrimeFactorData.checkFactorCerts primeDataWrongPrimeCert
#guard !checkIrreducibleCert (zpoly #[2, 0, 1]) certWrongPrime
#guard !PrimeFactorData.checkFactorCerts primeDataMalformedDegree
#guard !checkIrreducibleCert (zpoly #[2, 0, 1]) certMalformedDegree
#guard !checkIrreducibleCert (zpoly #[2, 0, 1]) certMissingObstruction
#guard !checkIrreducibleCert (zpoly #[1, -3, 2]) certValidQuad

/-! ### Compiled certificate generators (#8552)

The generators are the compiled *prep* half of certifying irreducibility. They
carry no soundness proof; the round-trip guards below confirm that whatever they
emit is accepted by the executable checkers (`Berlekamp.checkIrreducibilityCertificate`
and `checkIrreducibleCert`), and that reducible / trivial inputs yield `none`.
Correctness of an accepted certificate rides on the separately proved
`checkIrreducibleCert_sound`.

These `#guard`s exercise the *compiled* checker path (executable correctness of
the generator output). The complementary *kernel* replay — reducing the checker
on literal certificate data under `decide` — is demonstrated for the
finite-field layer by `validQuadCert_linear_check` in
`conformance/HexBerlekamp/Conformance.lean`, and for the integer checker by
the `irreducible_cert` tactic (#8566, Part 2 of #8552): the tactic reifies
generator output as literal data at elaboration time and lets the kernel
reduce `checkIrreducibleCertLinear`; its end-to-end tests live in
`HexBerlekampZassenhausMathlib/IrreducibleCertTest.lean`. The `Linear`
round-trip guards below pin the compiled form of exactly the check the kernel
replays. -/

/-- The Rabin certificate generator produces a certificate the executable
checker accepts. -/
private def fpCertRoundTrips {p : Nat} [ZMod64.Bounds p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) : Bool :=
  match Berlekamp.buildIrreducibilityCertificate? f hmonic with
  | some cert => Berlekamp.checkIrreducibilityCertificate f hmonic cert
  | none => false

/-- The integer certificate generator produces a certificate the executable
checker accepts. -/
private def zCertRoundTrips (f : ZPoly) : Bool :=
  match certifyIrreducible? f with
  | some cert => checkIrreducibleCert f cert
  | none => false

/-- The integer certificate generator's output is accepted by the
kernel-reducible checker as well; the `irreducible_cert` tactic replays
exactly this check in the kernel. -/
private def zCertRoundTripsLinear (f : ZPoly) : Bool :=
  match certifyIrreducible? f with
  | some cert => checkIrreducibleCertLinear f cert
  | none => false

-- Rabin generator: irreducible monic `x² + 2` over `F₅` round-trips; the unit
-- polynomial (degree 0) fails Rabin's test, so no certificate is emitted.
#guard fpCertRoundTrips irreducibleQuadFive irreducibleQuadFive_monic
#guard (Berlekamp.buildIrreducibilityCertificate? unitPolyFive unitPolyFive_monic).isNone

-- Integer generator: monic irreducibles with an admissible obstructing prime
-- for each candidate degree round-trip through the executable checker.
#guard zCertRoundTrips (zpoly #[2, 0, 1])
#guard zCertRoundTrips (zpoly #[1, 1, 1])

-- A degree-1 primitive is irreducible with no candidate factor degrees to
-- obstruct: the generator emits the (valid) empty certificate.
#guard zCertRoundTrips (zpoly #[3, 1])

-- Reducible or non-admissible inputs yield no certificate: `x² - 1` splits into
-- linear factors modulo every prime (degree-1 obstruction impossible), and
-- `(x - 1)²` has no admissible prime at all.
#guard (certifyIrreducible? (zpoly #[-1, 0, 1])).isNone
#guard (certifyIrreducible? repeatedRootPoly).isNone

-- Inputs excluded by `checkIrreducibleCert_sound`'s side conditions are
-- declined up front: constants and zero (`natDegree = 0`) and non-primitive
-- inputs (`2·x² + 2 = 2·(x² + 1)` is reducible over `ℤ` even though the checker
-- would accept its mod-`p` certificate).
#guard (certifyIrreducible? (zpoly #[7])).isNone
#guard (certifyIrreducible? (0 : ZPoly)).isNone
#guard (certifyIrreducible? (zpoly #[2, 0, 2])).isNone

-- A cubic irreducible over `ℤ` with an inert prime (`x³ - x - 1` is irreducible
-- modulo `3`): the single inert block obstructs every proper factor degree at
-- once, so the generator scales past quadratics whenever a suitable prime exists.
#guard zCertRoundTrips (zpoly #[-1, -1, 0, 1])

-- The kernel-reducible checker accepts the same generator outputs (compiled
-- form of the `irreducible_cert` kernel replay).
#guard zCertRoundTripsLinear (zpoly #[2, 0, 1])
#guard zCertRoundTripsLinear (zpoly #[1, 1, 1])
#guard zCertRoundTripsLinear (zpoly #[3, 1])
#guard zCertRoundTripsLinear (zpoly #[-1, -1, 0, 1])

-- Design limitation, NOT a generator bug: the checker's per-prime degree-sum
-- obstruction (`checkDegreeObstructions`) must rule out *every* candidate degree
-- in `1 .. deg/2`, but degree `deg/2` is essentially never obstructable when the
-- local factorization is "balanced". Swinnerton-Dyer `√2+√3+√5` factors as
-- `[2,2,2,2]` / `[1×8]` at every prime (degrees 2 and 4 always reachable), and
-- `Φ₁₅` never avoids a subset summing to 4. Both are irreducible over `ℤ` yet
-- admit no certificate the current checker can accept, so the generator returns
-- `none`. Certifying them needs a stronger obstruction than per-prime degree
-- sums (a checker-design change with its own soundness proof, out of scope for a
-- compiled generator).
#guard (certifyIrreducible? swinnertonDyerSD3).isNone
#guard (certifyIrreducible? phi15).isNone

-- Issue #8691: the word-sized Montgomery CLD kernel `cldQuotientModWord?` is
-- byte-identical to the bignum `cldQuotientMod` whenever its guard
-- (`Odd (p^a) ∧ p^a < 2^64`) holds, and declines (returns `none`) otherwise.
-- `g` is monic (leading coefficient `1`), as the lifted local factors are.
private def cldTestDivisor : ZPoly := DensePoly.ofCoeffs #[3, 1]
#guard cldQuotientModWord? swinnertonDyerSD3 cldTestDivisor 7 5
        = some (cldQuotientMod swinnertonDyerSD3 cldTestDivisor 7 5)
#guard cldQuotientModWord? swinnertonDyerSD3 cldTestDivisor 11 13
        = some (cldQuotientMod swinnertonDyerSD3 cldTestDivisor 11 13)
#guard cldQuotientModWord? quadSqrt2Sqrt3 cldTestDivisor 5 9
        = some (cldQuotientMod quadSqrt2Sqrt3 cldTestDivisor 5 9)
-- Guard declines when `p^a` overflows the word.
#guard (cldQuotientModWord? swinnertonDyerSD3 cldTestDivisor 11 400).isNone

end BZConformance
end Hex
