import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexHensel.Multifactor
import HexHensel.QuadraticMultifactor
import HexLLL.Basic

/-!
Executable data records for the Berlekamp-Zassenhaus factorization pipeline.

This module contains the shared records passed between prime selection,
Hensel lifting, and LLL-based integer recombination in the `ZPoly`
factorization pipeline.
-/
namespace Hex

namespace ZPoly

private def intModNat (z : Int) (m : Nat) : Nat :=
  Int.toNat (z % Int.ofNat m)

/-- The integer polynomial `X`. -/
def X : ZPoly :=
  DensePoly.monomial 1 1

private def splitInitialZeros : List Int → Nat × List Int
  | [] => (0, [])
  | coeff :: coeffs =>
      if coeff = 0 then
        let rest := splitInitialZeros coeffs
        (rest.1 + 1, rest.2)
      else
        (0, coeff :: coeffs)

/-- Data from extracting the largest visible power of `X` from a dense integer polynomial. -/
structure XPowerData where
  power : Nat
  core : ZPoly

/--
Remove the initial zero-coefficient run from a dense integer polynomial.

Dense coefficients are stored in ascending degree order, so the initial zero
run is exactly the executable power of `X` dividing the polynomial.
-/
def extractXPower (f : ZPoly) : XPowerData :=
  let split := splitInitialZeros f.toArray.toList
  { power := split.1, core := DensePoly.ofCoeffs split.2.toArray }

/-- The integer leading coefficient reduced to the candidate prime field. -/
def leadingCoeffModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : ZMod64 p :=
  ZMod64.ofNat p (intModNat (DensePoly.leadingCoeff f) p)

end ZPoly

/-- The candidate prime does not divide the integer leading coefficient. -/
def leadingCoeffAdmissible (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  ZPoly.leadingCoeffModP f p ≠ 0

/-- The modular image is square-free according to the executable gcd criterion. -/
def squareFreeModP (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Prop :=
  let fModP := ZPoly.modP p f
  DensePoly.gcd fModP (DensePoly.derivative fModP) = 1

/--
Executable good-prime predicate for the Berlekamp-Zassenhaus pipeline.

It checks that the modulus is nontrivial, that the integer leading coefficient
survives reduction modulo `p`, and that the modular image is square-free.
-/
def isGoodPrime (f : ZPoly) (p : Nat) [ZMod64.Bounds p] : Bool :=
  let fModP := ZPoly.modP p f
  p > 1 &&
    ZPoly.leadingCoeffModP f p != 0 &&
    DensePoly.gcd fModP (DensePoly.derivative fModP) == 1

private theorem bounds_two : ZMod64.Bounds 2 := by
  constructor <;> decide

private theorem bounds_three : ZMod64.Bounds 3 := by
  constructor <;> decide

private theorem bounds_five : ZMod64.Bounds 5 := by
  constructor <;> decide

private theorem bounds_seven : ZMod64.Bounds 7 := by
  constructor <;> decide

private theorem bounds_eleven : ZMod64.Bounds 11 := by
  constructor <;> decide

private theorem bounds_thirteen : ZMod64.Bounds 13 := by
  constructor <;> decide

private theorem bounds_seventeen : ZMod64.Bounds 17 := by
  constructor <;> decide

private theorem bounds_nineteen : ZMod64.Bounds 19 := by
  constructor <;> decide

private theorem bounds_twenty_three : ZMod64.Bounds 23 := by
  constructor <;> decide

private theorem bounds_thirty_one : ZMod64.Bounds 31 := by
  constructor <;> decide

private theorem bounds_seventy_one : ZMod64.Bounds 71 := by
  constructor <;> decide

private theorem prime_two : Nat.Prime 2 := by
  sorry

private theorem prime_three : Nat.Prime 3 := by
  sorry

private theorem prime_five : Nat.Prime 5 := by
  sorry

private theorem prime_seven : Nat.Prime 7 := by
  sorry

private theorem prime_eleven : Nat.Prime 11 := by
  sorry

private theorem prime_thirteen : Nat.Prime 13 := by
  sorry

private theorem prime_seventeen : Nat.Prime 17 := by
  sorry

private theorem prime_nineteen : Nat.Prime 19 := by
  sorry

private theorem prime_twenty_three : Nat.Prime 23 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 23 := Nat.le_of_dvd (by decide : 0 < 23) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => omega
    | 20 => omega
    | 21 => omega
    | 22 => omega
    | 23 => exact Or.inr rfl
    | _ + 24 => omega

private theorem prime_thirty_one : Nat.Prime 31 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 31 := Nat.le_of_dvd (by decide : 0 < 31) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => omega
    | 20 => omega
    | 21 => omega
    | 22 => omega
    | 23 => omega
    | 24 => omega
    | 25 => omega
    | 26 => omega
    | 27 => omega
    | 28 => omega
    | 29 => omega
    | 30 => omega
    | 31 => exact Or.inr rfl
    | _ + 32 => omega

private theorem prime_seventy_one : Nat.Prime 71 := by
  refine ⟨?_, ?_⟩
  · decide
  · intro a hdvd
    have hle : a ≤ 71 := Nat.le_of_dvd (by decide : 0 < 71) hdvd
    rcases hdvd with ⟨k, hk⟩
    match a with
    | 0 => omega
    | 1 => exact Or.inl rfl
    | 2 => omega
    | 3 => omega
    | 4 => omega
    | 5 => omega
    | 6 => omega
    | 7 => omega
    | 8 => omega
    | 9 => omega
    | 10 => omega
    | 11 => omega
    | 12 => omega
    | 13 => omega
    | 14 => omega
    | 15 => omega
    | 16 => omega
    | 17 => omega
    | 18 => omega
    | 19 => omega
    | 20 => omega
    | 21 => omega
    | 22 => omega
    | 23 => omega
    | 24 => omega
    | 25 => omega
    | 26 => omega
    | 27 => omega
    | 28 => omega
    | 29 => omega
    | 30 => omega
    | 31 => omega
    | 32 => omega
    | 33 => omega
    | 34 => omega
    | 35 => omega
    | 36 => omega
    | 37 => omega
    | 38 => omega
    | 39 => omega
    | 40 => omega
    | 41 => omega
    | 42 => omega
    | 43 => omega
    | 44 => omega
    | 45 => omega
    | 46 => omega
    | 47 => omega
    | 48 => omega
    | 49 => omega
    | 50 => omega
    | 51 => omega
    | 52 => omega
    | 53 => omega
    | 54 => omega
    | 55 => omega
    | 56 => omega
    | 57 => omega
    | 58 => omega
    | 59 => omega
    | 60 => omega
    | 61 => omega
    | 62 => omega
    | 63 => omega
    | 64 => omega
    | 65 => omega
    | 66 => omega
    | 67 => omega
    | 68 => omega
    | 69 => omega
    | 70 => omega
    | 71 => exact Or.inr rfl
    | _ + 72 => omega

private def zmod64ZPow {p : Nat} [ZMod64.Bounds p] (a : ZMod64 p) : Int → ZMod64 p
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

private instance zmod64IntPow {p : Nat} [ZMod64.Bounds p] :
    HPow (ZMod64 p) Int (ZMod64 p) where
  hPow := zmod64ZPow

private instance zmod64FieldOfPrime
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) :
    Lean.Grind.Field (ZMod64 p) := by
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    rfl
  · sorry
  · sorry
  · intro a ha
    rw [Lean.Grind.CommSemiring.mul_comm]
    exact ZMod64.inv_mul_eq_one_of_prime hp ha
  · sorry
  · sorry
  · sorry

private structure SmallPrimeCandidate where
  p : Nat
  [bounds : ZMod64.Bounds p]
  prime : Nat.Prime p
  field : Lean.Grind.Field (ZMod64 p)

/-- A scored admissible small-prime candidate for default prime selection. -/
structure PrimeCandidateScore where
  /-- Candidate prime. -/
  p : Nat
  /-- Smaller scores are preferred; equal scores retain the earlier smaller prime. -/
  factorCount : Nat

private def smallPrimeCandidates : List SmallPrimeCandidate :=
  [ { p := 2, bounds := bounds_two, prime := prime_two,
      field := @zmod64FieldOfPrime 2 bounds_two prime_two },
    { p := 3, bounds := bounds_three, prime := prime_three,
      field := @zmod64FieldOfPrime 3 bounds_three prime_three },
    { p := 5, bounds := bounds_five, prime := prime_five,
      field := @zmod64FieldOfPrime 5 bounds_five prime_five },
    { p := 7, bounds := bounds_seven, prime := prime_seven,
      field := @zmod64FieldOfPrime 7 bounds_seven prime_seven },
    { p := 11, bounds := bounds_eleven, prime := prime_eleven,
      field := @zmod64FieldOfPrime 11 bounds_eleven prime_eleven },
    { p := 13, bounds := bounds_thirteen, prime := prime_thirteen,
      field := @zmod64FieldOfPrime 13 bounds_thirteen prime_thirteen },
    { p := 17, bounds := bounds_seventeen, prime := prime_seventeen,
      field := @zmod64FieldOfPrime 17 bounds_seventeen prime_seventeen },
    { p := 19, bounds := bounds_nineteen, prime := prime_nineteen,
      field := @zmod64FieldOfPrime 19 bounds_nineteen prime_nineteen },
    { p := 23, bounds := bounds_twenty_three, prime := prime_twenty_three,
      field := @zmod64FieldOfPrime 23 bounds_twenty_three prime_twenty_three },
    { p := 31, bounds := bounds_thirty_one, prime := prime_thirty_one,
      field := @zmod64FieldOfPrime 31 bounds_thirty_one prime_thirty_one },
    { p := 71, bounds := bounds_seventy_one, prime := prime_seventy_one,
      field := @zmod64FieldOfPrime 71 bounds_seventy_one prime_seventy_one } ]

private def monicModularImage {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : FpPoly p :=
  if f.isZero then
    0
  else
    DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f

private theorem monicModularImage_monic
    {p : Nat} [ZMod64.Bounds p] (hp : Nat.Prime p) (f : FpPoly p)
    (hgood : f.isZero = false) :
    DensePoly.Monic (monicModularImage f) := by
  sorry

private def berlekampFactorsModP (f : ZPoly) (c : SmallPrimeCandidate) :
    Array (@FpPoly c.p c.bounds) :=
  letI := c.bounds
  letI := c.field
  let fModP := ZPoly.modP c.p f
  if hzero : fModP.isZero = false then
    (Berlekamp.berlekampFactor
      (monicModularImage fModP)
      (monicModularImage_monic c.prime fModP hzero)).factors.toArray
  else
    #[]

private def intCoeffModNat (z : Int) (p : Nat) : Nat :=
  Int.toNat (z % Int.ofNat p)

private def evalZPolyModNat (f : ZPoly) (p x : Nat) : Nat :=
  f.toArray.toList.reverse.foldl
    (fun acc coeff => (intCoeffModNat coeff p + x * acc) % p)
    0

private def completeLinearDegreeSplit? (f : ZPoly) (p : Nat) [ZMod64.Bounds p] :
    Option (Array Nat) :=
  let degree := (ZPoly.modP p f).degree?.getD 0
  let roots := (List.range p).filter fun x => evalZPolyModNat f p x == 0
  if degree != 0 && roots.length == degree then
    some (Array.replicate degree 1)
  else
    none

/--
Return the sorted degrees of the Berlekamp factors of `f mod p` at an
explicit small prime supported by the executable prime-selection list.

This testing-facing surface deliberately reuses the production small-prime
pipeline. For complete linear splits, it records the explicit root-degree
evidence directly so pinned conformance checks are not sensitive to the current
Berlekamp witness splitting surface. It returns `none` if `p` is unsupported or
the leading coefficient vanishes modulo `p`; the Berlekamp branch also requires
the usual good-prime predicate.
-/
def modularFactorDegreesAt? (f : ZPoly) (p : Nat) : Option (Array Nat) :=
  smallPrimeCandidates.foldl
    (fun found (c : SmallPrimeCandidate) =>
      match found with
      | some degrees => some degrees
      | none =>
          if c.p == p then
            letI : ZMod64.Bounds c.p := c.bounds
            if ZPoly.leadingCoeffModP f c.p != 0 then
              match completeLinearDegreeSplit? f c.p with
              | some degrees => some degrees
              | none =>
                  if isGoodPrime f c.p then
                    some ((berlekampFactorsModP f c).map (fun factor =>
                      factor.degree?.getD 0) |>.qsort (· ≤ ·))
                  else
                    none
            else
              none
          else
            none)
    none

private def scoreCandidate (f : ZPoly) (c : SmallPrimeCandidate) : Option PrimeCandidateScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let factors := berlekampFactorsModP f c
    some { p := c.p, factorCount := factors.size }
  else
    none

private def betterScore (old new : PrimeCandidateScore) : PrimeCandidateScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

/-- Scan the fixed small-prime list and return the best admissible scored candidate, if any. -/
def choosePrimeScore? (f : ZPoly) : Option PrimeCandidateScore :=
  smallPrimeCandidates.foldl
    (fun best c =>
      match best, scoreCandidate f c with
      | none, score => score
      | some old, none => some old
      | some old, some new => some (betterScore old new))
    none

/--
Choose a small admissible prime for the Berlekamp-Zassenhaus pipeline.

The search is bounded to a fixed ascending list of small primes. Candidate
scores use the currently available executable modular factor surface; strict
score improvement replaces the incumbent, so equal scores keep the smaller
earlier prime.
-/
def choosePrime (f : ZPoly) : Nat :=
  match choosePrimeScore? f with
  | some score => score.p
  | none => 2

theorem choosePrimeScore?_isGoodPrime
    (f : ZPoly) (score : PrimeCandidateScore)
    (hscore : choosePrimeScore? f = some score) :
    ∃ hbounds : ZMod64.Bounds score.p,
      @isGoodPrime f score.p hbounds = true := by
  sorry

theorem choosePrime_isGoodPrime_of_selected
    (f : ZPoly) (score : PrimeCandidateScore)
    (hscore : choosePrimeScore? f = some score)
    (hchoose : choosePrime f = score.p) :
    ∃ hbounds : ZMod64.Bounds (choosePrime f),
      @isGoodPrime f (choosePrime f) hbounds = true := by
  sorry

/-- A successful good-prime check certifies leading-coefficient admissibility. -/
theorem isGoodPrime_leadingCoeffAdmissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    leadingCoeffAdmissible f p := by
  sorry

/-- A successful good-prime check certifies the modular square-free precondition. -/
theorem isGoodPrime_squareFreeModP
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hgood : isGoodPrime f p = true) :
    squareFreeModP f p := by
  sorry

/--
Data produced by modular prime selection: the selected prime, the image of the
input polynomial over that prime field, and its modular factors.
-/
structure PrimeChoiceData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  fModP : FpPoly p
  factorsModP : Array (FpPoly p)

/--
Data produced by Hensel lifting and consumed by integer recombination: the
prime, the requested lift precision, and the lifted integer factors.
-/
structure LiftData where
  p : Nat
  k : Nat
  liftedFactors : Array ZPoly

/--
Executable normalization data for the public integer factorization API.

The public input is first split into its integer content, primitive part,
initial `X` power, and primitive square-free core. The Berlekamp-Zassenhaus
prime/lift/recombine pipeline runs on `squareFreeCore`; the other fields are
reassembled around the resulting core factors.
-/
structure FactorNormalizationData where
  content : Int
  primitive : ZPoly
  xPower : Nat
  xFreePrimitive : ZPoly
  squareFreeCore : ZPoly
  repeatedPart : ZPoly

/--
Public integer-polynomial factorization result.

The scalar carries the signed content of the input. Polynomial factors are
stored with explicit multiplicities; factor order remains operational.
-/
structure Factorization where
  scalar : Int
  factors : Array (ZPoly × Nat)
deriving DecidableEq

namespace Factorization

private def polyPow (f : ZPoly) : Nat → ZPoly
  | 0 => 1
  | n + 1 => polyPow f n * f

/-- Expand multiplicity pairs into the ordered polynomial product. -/
def product (φ : Factorization) : ZPoly :=
  φ.factors.foldl (fun acc factor => acc * polyPow factor.1 factor.2) (DensePoly.C φ.scalar)

end Factorization

/-- Compute the normalization data required before the square-free pipeline. -/
def normalizeForFactor (f : ZPoly) : FactorNormalizationData :=
  let primitive := ZPoly.primitivePart f
  let xData := ZPoly.extractXPower primitive
  let sqData := ZPoly.primitiveSquareFreeDecomposition xData.core
  { content := ZPoly.content f
    primitive
    xPower := xData.power
    xFreePrimitive := xData.core
    squareFreeCore := sqData.squareFreeCore
    repeatedPart := sqData.repeatedPart }

private def contentFactorArray (content : Int) : Array ZPoly :=
  if content = 1 then
    #[]
  else
    #[DensePoly.C content]

private def xPowerFactorArray (power : Nat) : Array ZPoly :=
  (List.replicate power ZPoly.X).toArray

private def repeatedPartFactorArray (repeatedPart : ZPoly) : Array ZPoly :=
  if repeatedPart = 1 then
    #[]
  else
    #[repeatedPart]

private def signedContentScalar (f : ZPoly) : Int :=
  if f = 0 then
    0
  else if DensePoly.leadingCoeff f < 0 then
    -ZPoly.content f
  else
    ZPoly.content f

private def normalizeFactorSign (f : ZPoly) : ZPoly :=
  if DensePoly.leadingCoeff f < 0 then
    DensePoly.scale (-1 : Int) f
  else
    f

private def shouldRecordPolynomialFactor (f : ZPoly) : Bool :=
  f ≠ 0 && f ≠ 1 && f ≠ DensePoly.C (-1)

private def bumpFactorMultiplicity (f : ZPoly) : List (ZPoly × Nat) → List (ZPoly × Nat)
  | [] => [(f, 1)]
  | entry :: entries =>
      if entry.1 = f then
        (entry.1, entry.2 + 1) :: entries
      else
        entry :: bumpFactorMultiplicity f entries

private def collectFactorMultiplicities (factors : Array ZPoly) : Array (ZPoly × Nat) :=
  factors.toList.foldl
    (fun acc factor =>
      let factor := normalizeFactorSign factor
      if shouldRecordPolynomialFactor factor then
        bumpFactorMultiplicity factor acc
      else
        acc)
    []
  |>.reverse.toArray

private def polynomialNormalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  xPowerFactorArray d.xPower ++ repeatedPartFactorArray d.repeatedPart

/-- Factors that come from normalization before the square-free core is factored. -/
def normalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  contentFactorArray d.content ++
    xPowerFactorArray d.xPower ++
    repeatedPartFactorArray d.repeatedPart

/-- Reassemble normalization factors around the factors of the square-free core. -/
def reassembleNormalizedFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  normalizationPrefixFactors d ++ coreFactors

private def reassemblePolynomialFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  polynomialNormalizationPrefixFactors d ++ coreFactors

private def factorizationOfFactors (f : ZPoly) (factors : Array ZPoly) : Factorization :=
  { scalar := signedContentScalar f
    factors := collectFactorMultiplicities factors }

private def normalizedConstantFactors (d : FactorNormalizationData) : Array ZPoly :=
  let coreFactor :=
    if d.squareFreeCore = 1 then
      #[]
    else
      #[d.squareFreeCore]
  normalizationPrefixFactors d ++ coreFactor

/--
Per-prime modular irreducibility evidence for integer irreducibility
certificates.

The factor array records the modular factors observed at this prime. The degree
list and Rabin certificates are zipped with those concrete factors so the
checker can validate certificate metadata and the executable Rabin witness
against the polynomial it is meant to certify.
-/
structure PrimeFactorData where
  p : Nat
  [bounds : ZMod64.Bounds p]
  factorDegrees : Array Nat
  factorPolys : Array (FpPoly p)
  factorCerts : Array Berlekamp.IrreducibilityCertificate

/--
Evidence that a candidate integer factor degree is impossible for one recorded
prime block.

If an integer factor has degree `targetDegree`, then reducing modulo any good
prime gives a product of modular irreducible factors whose degrees sum to
`targetDegree`. The checker validates an obstruction by confirming that the
referenced prime block has no subset of recorded factor degrees with this sum.
-/
structure DegreeObstruction where
  targetDegree : Nat
  primeIndex : Nat

/--
Checker-first certificate data for irreducibility over `Z[x]`.

Each entry groups all modular degree and irreducibility-certificate data for a
single prime so the checker can validate the prime and degree metadata before
the later proof layer interprets the degree obstruction mathematically.
-/
structure ZPolyIrreducibilityCertificate where
  perPrime : Array PrimeFactorData
  degreeObstructions : Array DegreeObstruction

namespace PrimeFactorData

/-- Sum the recorded modular factor degrees for one prime. -/
def degreeSum (d : PrimeFactorData) : Nat :=
  d.factorDegrees.toList.foldl (fun acc n => acc + n) 0

/-- Ordered product of the recorded modular factors for one prime. -/
def factorProduct (d : PrimeFactorData) : @FpPoly d.p d.bounds :=
  letI := d.bounds
  d.factorPolys.foldl (· * ·) 1

/-- Does the recorded degree multiset contain `n`? -/
def containsDegree (d : PrimeFactorData) (n : Nat) : Bool :=
  d.factorDegrees.toList.any fun degree => degree == n

private def hasSubsetDegreeAux : List Nat → Nat → Bool
  | [], target => target == 0
  | degree :: degrees, target =>
      hasSubsetDegreeAux degrees target ||
        (degree ≤ target && hasSubsetDegreeAux degrees (target - degree))

/--
Does some subset of this prime block's modular factor degrees sum to `target`?
-/
def hasSubsetDegree (d : PrimeFactorData) (target : Nat) : Bool :=
  hasSubsetDegreeAux d.factorDegrees.toList target

/--
Check one nested finite-field irreducibility certificate against its degree slot
and the concrete modular factor occupying that slot.
-/
def checkCertAtFactor
    (d : PrimeFactorData) (degree : Nat) (factor : @FpPoly d.p d.bounds)
    (cert : Berlekamp.IrreducibilityCertificate) : Bool :=
  letI := d.bounds
  decide (cert.p = d.p) &&
    decide (cert.n = degree) &&
    d.containsDegree cert.n &&
    factor.degree? == some degree &&
    if hmonic : factor.leadingCoeff = 1 then
      Berlekamp.checkIrreducibilityCertificate factor (by exact hmonic) cert
    else
      false

/--
Check that nested certificates match the enclosing prime, degree array, and
concrete modular factor array.
-/
def checkFactorCerts (d : PrimeFactorData) : Bool :=
  d.factorDegrees.size == d.factorCerts.size &&
    d.factorDegrees.size == d.factorPolys.size &&
    (d.factorDegrees.toList.zip (d.factorPolys.toList.zip d.factorCerts.toList)).all fun pair =>
      checkCertAtFactor d pair.1 pair.2.1 pair.2.2

/-- Check one prime block against the integer polynomial being certified. -/
def checkForPolynomial (f : ZPoly) (d : PrimeFactorData) : Bool :=
  letI := d.bounds
  isGoodPrime f d.p &&
    d.factorDegrees.all (fun degree => 0 < degree) &&
    d.degreeSum == (ZPoly.modP d.p f).degree?.getD 0 &&
    d.factorProduct == ZPoly.modP d.p f &&
    d.checkFactorCerts

end PrimeFactorData

namespace ZPolyIrreducibilityCertificate

/-- Nontrivial integer factor degrees that must be ruled out for `f`. -/
def candidateFactorDegrees (f : ZPoly) : List Nat :=
  (List.range ((f.degree?.getD 0) / 2)).map fun i => i + 1

/-- Look up a per-prime block by the index stored in an obstruction. -/
def primeDataAt? (cert : ZPolyIrreducibilityCertificate) (idx : Nat) :
    Option PrimeFactorData :=
  match cert.perPrime.toList.drop idx with
  | [] => none
  | primeData :: _ => some primeData

end ZPolyIrreducibilityCertificate

namespace DegreeObstruction

/--
Check one degree obstruction against the certificate's per-prime degree data.

The target must be one of the nontrivial candidate degrees for `f`, and the
referenced prime block must have no subset of modular factor degrees summing to
that target.
-/
def checkForCertificate
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (obs : DegreeObstruction) : Bool :=
  decide (obs.targetDegree ∈ ZPolyIrreducibilityCertificate.candidateFactorDegrees f) &&
    match cert.primeDataAt? obs.primeIndex with
    | none => false
    | some primeData => !primeData.hasSubsetDegree obs.targetDegree

end DegreeObstruction

namespace ZPolyIrreducibilityCertificate

/-- Does the obstruction array contain a valid obstruction for `targetDegree`? -/
def hasObstructionFor (f : ZPoly)
    (cert : ZPolyIrreducibilityCertificate) (targetDegree : Nat) : Bool :=
  cert.degreeObstructions.toList.any fun obs =>
    obs.targetDegree == targetDegree && obs.checkForCertificate f cert

/-- Check that every candidate nontrivial factor degree is ruled out. -/
def checkDegreeObstructions (f : ZPoly)
    (cert : ZPolyIrreducibilityCertificate) : Bool :=
  (cert.degreeObstructions.all fun obs => obs.checkForCertificate f cert) &&
    (candidateFactorDegrees f).all fun targetDegree =>
      cert.hasObstructionFor f targetDegree

end ZPolyIrreducibilityCertificate

/--
Executable surface checker for integer-polynomial irreducibility certificates.

This validates all computational alignment data available at this layer: every
prime block must use an admissible prime for `f`, its recorded modular factors
must multiply back to the modular image, each nested finite-field certificate
must match the enclosing prime and its concrete factor, and every nontrivial
integer factor degree must be excluded by explicit per-prime degree data.
-/
def checkIrreducibleCert
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) : Bool :=
  cert.perPrime.all (fun primeData => primeData.checkForPolynomial f) &&
    cert.checkDegreeObstructions f

private structure PrimeChoiceDataScore where
  data : PrimeChoiceData
  factorCount : Nat

private def primeChoiceDataScore (f : ZPoly) (c : SmallPrimeCandidate) :
    Option PrimeChoiceDataScore :=
  letI := c.bounds
  if isGoodPrime f c.p then
    let fModP := ZPoly.modP c.p f
    let factorsModP := berlekampFactorsModP f c
    some
      { data := { p := c.p, fModP, factorsModP }
        factorCount := factorsModP.size }
  else
    none

private def betterPrimeChoiceDataScore
    (old new : PrimeChoiceDataScore) : PrimeChoiceDataScore :=
  if new.factorCount < old.factorCount then
    new
  else
    old

private def choosePrimeData? (f : ZPoly) : Option PrimeChoiceData :=
  smallPrimeCandidates.foldl
    (fun best c =>
      match best, primeChoiceDataScore f c with
      | none, score => score
      | some old, none => some old
      | some old, some new => some (betterPrimeChoiceDataScore old new))
    none
  |>.map (fun score => score.data)

private def fallbackPrimeChoiceData (f : ZPoly) : PrimeChoiceData :=
  letI := bounds_two
  let c : SmallPrimeCandidate :=
    { p := 2, bounds := bounds_two, prime := prime_two,
      field := @zmod64FieldOfPrime 2 bounds_two prime_two }
  let fModP := ZPoly.modP 2 f
  let factorsModP := berlekampFactorsModP f c
  { p := 2, fModP, factorsModP }

/--
Choose an admissible small prime and package the modular image together with
its Berlekamp irreducible factor data for the rest of the pipeline.
-/
def choosePrimeData (f : ZPoly) : PrimeChoiceData :=
  match choosePrimeData? f with
  | some data => data
  | none => fallbackPrimeChoiceData f

/--
Lift the chosen modular factors to the requested precision for integer
recombination.
-/
def henselLiftData (f : ZPoly) (B : Nat) (d : PrimeChoiceData) : LiftData :=
  letI := d.bounds
  let factors := d.factorsModP.map (fun factor => FpPoly.liftToZ factor)
  { p := d.p
    k := B
    liftedFactors := ZPoly.multifactorLiftQuadratic d.p B f factors }

/--
Integer upper bound for the BHKS fast-recombination precision schedule.

This is the conservative all-integer cap from the `hex-berlekamp-zassenhaus`
SPEC: `1 + n * 4^(n^2) * (sumSquared + 1)^n * log2(sumSquared + 1)^n`, where
`n` is the executable degree bound and `sumSquared` is the squared coefficient
norm.
-/
def bhksBound (f : ZPoly) : Nat :=
  let n := f.degree?.getD 0
  let sumSquared := ZPoly.coeffNormSq f
  1 + n * 4 ^ (n * n) * (sumSquared + 1) ^ n * (Nat.log2 (sumSquared + 1)) ^ n

/-- Integer coefficient bound `B_j` used by the BHKS all-coefficients CLD lattice. -/
def bhksCoeffBound (f : ZPoly) (j : Nat) : Nat :=
  let n := f.degree?.getD 0
  Nat.choose (n - 1) j * n * ZPoly.coeffL2NormBound f

private def ceilLogPAux (p target : Nat) : Nat → Nat → Nat → Nat
  | 0, ell, _ => ell
  | fuel + 1, ell, power =>
      if target ≤ power then
        ell
      else
        ceilLogPAux p target fuel (ell + 1) (power * p)

/--
Small executable `ceil_log_p` helper.

For `1 < p`, `ceilLogP p target` searches for the least visible exponent
whose `p`-power is at least `target`. The degenerate `p ≤ 1` case returns
zero because the BHKS fast path is only used with admissible primes.
-/
def ceilLogP (p target : Nat) : Nat :=
  if p ≤ 1 then
    0
  else
    ceilLogPAux p target (target + 1) 0 1

/-- Per-coordinate BHKS precision threshold `ell_j := ceil_log_p (2 * B_j + 1)`. -/
def bhksCoeffCutThreshold (p : Nat) (f : ZPoly) (j : Nat) : Nat :=
  ceilLogP p (2 * bhksCoeffBound f j + 1)

private def subsetSplits : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => [([], [])]
  | factor :: factors =>
      let rest := subsetSplits factors
      rest.map (fun split => (split.1, factor :: split.2)) ++
        rest.map (fun split => (factor :: split.1, split.2))

private def subsetSplitsWithFirst : List ZPoly → List (List ZPoly × List ZPoly)
  | [] => []
  | factor :: factors =>
      (subsetSplits factors).map fun split => (factor :: split.1, split.2)

private def firstSome {α β : Type} : List α → (α → Option β) → Option β
  | [], _ => none
  | x :: xs, f =>
      match f x with
      | some y => some y
      | none => firstSome xs f

private def exactQuotient? (target candidate : ZPoly) : Option ZPoly :=
  if candidate.isZero || candidate = 1 then
    none
  else
    let qr := DensePoly.divMod target candidate
    if qr.2 = 0 && qr.1 * candidate == target then
      some qr.1
    else
      none

private theorem one_mul_zpoly (g : ZPoly) :
    (1 : ZPoly) * g = g := by
  rw [DensePoly.mul_comm_poly (S := Int), DensePoly.mul_one_right_poly]

private theorem list_foldl_mul_eq_mul_foldl_one (g : ZPoly) (xs : List ZPoly) :
    xs.foldl (fun acc factor => acc * factor) g =
      g * xs.foldl (fun acc factor => acc * factor) 1 := by
  induction xs generalizing g with
  | nil =>
      simpa using (DensePoly.mul_one_right_poly (S := Int) g).symm
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [one_mul_zpoly]
      calc
        xs.foldl (fun acc factor => acc * factor) (g * x) =
            (g * x) * xs.foldl (fun acc factor => acc * factor) 1 := ih (g * x)
        _ = g * (x * xs.foldl (fun acc factor => acc * factor) 1) := by
            rw [DensePoly.mul_assoc_poly (S := Int)]
        _ = g * xs.foldl (fun acc factor => acc * factor) x := by
            rw [ih x]

private theorem polyProduct_cons_toArray (g : ZPoly) (rest : List ZPoly) :
    Array.polyProduct (g :: rest).toArray = g * Array.polyProduct rest.toArray := by
  simpa [Array.polyProduct, one_mul_zpoly] using
    (list_foldl_mul_eq_mul_foldl_one g rest)

private theorem polyProduct_singleton (g : ZPoly) :
    Array.polyProduct #[g] = g := by
  simpa [Array.polyProduct] using one_mul_zpoly g

private theorem polyProduct_empty :
    Array.polyProduct (#[] : Array ZPoly) = 1 := by
  rfl

private theorem polyProduct_append (xs ys : Array ZPoly) :
    Array.polyProduct (xs ++ ys) = Array.polyProduct xs * Array.polyProduct ys := by
  rw [Array.polyProduct, Array.foldl_append]
  cases ys with
  | mk ylist =>
      simpa [Array.polyProduct] using list_foldl_mul_eq_mul_foldl_one
        (Array.foldl (fun acc factor => acc * factor) 1 xs) ylist

private theorem polyProduct_contentFactorArray (content : Int) :
    Array.polyProduct (contentFactorArray content) =
      if content = 1 then 1 else DensePoly.C content := by
  unfold contentFactorArray
  by_cases hcontent : content = 1
  · simp [hcontent, polyProduct_empty]
  · simp [hcontent, polyProduct_singleton]

private theorem polyProduct_repeatedPartFactorArray (repeatedPart : ZPoly) :
    Array.polyProduct (repeatedPartFactorArray repeatedPart) =
      if repeatedPart = 1 then 1 else repeatedPart := by
  unfold repeatedPartFactorArray
  by_cases hrepeated : repeatedPart = 1
  · simp [hrepeated, polyProduct_empty]
  · simp [hrepeated, polyProduct_singleton]

private theorem polyProduct_replicate_X_zero :
    Array.polyProduct ((List.replicate 0 ZPoly.X).toArray) = 1 := by
  rfl

private theorem polyProduct_replicate_X_succ (power : Nat) :
    Array.polyProduct ((List.replicate (power + 1) ZPoly.X).toArray) =
      ZPoly.X * Array.polyProduct ((List.replicate power ZPoly.X).toArray) := by
  simpa [List.replicate] using polyProduct_cons_toArray ZPoly.X (List.replicate power ZPoly.X)

private theorem polyProduct_xPowerFactorArray_zero :
    Array.polyProduct (xPowerFactorArray 0) = 1 := by
  simpa [xPowerFactorArray] using polyProduct_replicate_X_zero

private theorem polyProduct_xPowerFactorArray_succ (power : Nat) :
    Array.polyProduct (xPowerFactorArray (power + 1)) =
      ZPoly.X * Array.polyProduct (xPowerFactorArray power) := by
  simpa [xPowerFactorArray] using polyProduct_replicate_X_succ power

private theorem polyProduct_polynomialNormalizationPrefixFactors
    (d : FactorNormalizationData) :
    Array.polyProduct (polynomialNormalizationPrefixFactors d) =
      Array.polyProduct (xPowerFactorArray d.xPower) *
        Array.polyProduct (repeatedPartFactorArray d.repeatedPart) := by
  unfold polynomialNormalizationPrefixFactors
  rw [polyProduct_append]

private theorem polyProduct_normalizationPrefixFactors (d : FactorNormalizationData) :
    Array.polyProduct (normalizationPrefixFactors d) =
      Array.polyProduct (contentFactorArray d.content) *
        (Array.polyProduct (xPowerFactorArray d.xPower) *
          Array.polyProduct (repeatedPartFactorArray d.repeatedPart)) := by
  unfold normalizationPrefixFactors
  rw [polyProduct_append, polyProduct_append]
  rw [DensePoly.mul_assoc_poly (S := Int)]

private theorem exactQuotient?_product
    {target candidate quotient : ZPoly}
    (hquot : exactQuotient? target candidate = some quotient) :
    quotient * candidate = target := by
  unfold exactQuotient? at hquot
  split at hquot
  · contradiction
  · rename_i hnontrivial
    generalize hqr : DensePoly.divMod target candidate = qr at hquot
    cases qr with
    | mk q r =>
        simp only at hquot
        split at hquot
        · rename_i hcheck
          cases hquot
          exact (by
            simpa [Bool.and_eq_true, beq_iff_eq] using hcheck : r = 0 ∧ quotient * candidate = target).2
        · contradiction

private def positiveDivisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun d => d != 0 && n % d == 0

private def integerRootCandidates (f : ZPoly) : List Int :=
  (positiveDivisors (f.coeff 0).natAbs).flatMap fun d =>
    let r : Int := Int.ofNat d
    [r, -r]

private def linearFactorForRoot (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

private def splitIntegerRootFactorsAux :
    ZPoly → List Int → Nat → Array ZPoly × ZPoly
  | target, _roots, 0 => (#[], target)
  | target, [], _fuel + 1 => (#[], target)
  | target, root :: roots, fuel + 1 =>
      let factor := linearFactorForRoot root
      match exactQuotient? target factor with
      | some quotient =>
          let rest := splitIntegerRootFactorsAux quotient roots fuel
          (#[factor] ++ rest.1, rest.2)
      | none => splitIntegerRootFactorsAux target roots fuel

private def quadraticIntegerRootFactors? (core : ZPoly) : Option (Array ZPoly) :=
  if core.degree?.getD 0 = 2 then
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    if split.1.size = 0 then
      none
    else if split.2 = 1 then
      some split.1
    else if split.2.degree?.getD 0 ≤ 1 then
      some (split.1.push split.2)
    else
      none
  else
    none

private def centeredModNat (z : Int) (m : Nat) : Int :=
  if m = 0 then
    z
  else
    let r := z % Int.ofNat m
    if 2 * r.natAbs ≤ m then
      r
    else if r < 0 then
      r + Int.ofNat m
    else
      r - Int.ofNat m

/-- Centred residue modulo `p^b`, the `mod^±` operation in the BHKS cut. -/
def centeredResiduePow (p b : Nat) (x : Int) : Int :=
  centeredModNat x (p ^ b)

/--
BHKS two-sided cut `Psi^a_b(x) = (x - (x mod^± p^b)) / p^b`.

The precision parameter `a` records the ambient modulus `p^a`; the executable
cut only needs the lower threshold `b`.
-/
def psiCut (p _a b : Nat) (x : Int) : Int :=
  let modulus := p ^ b
  if modulus = 0 then
    0
  else
    (x - centeredResiduePow p b x) / Int.ofNat modulus

private def cldQuotientMod (f g : ZPoly) (p a : Nat) : ZPoly :=
  let numerator := ZPoly.reduceModPow (f * DensePoly.derivative g) p a
  let quotient := (DensePoly.divMod numerator g).1
  ZPoly.reduceModPow quotient p a

/--
Centred high-bit CLD coefficients for one lifted local factor.

The returned array has one entry for each coefficient index
`0, ..., deg(f)-1`; entry `j` is
`Psi^a_{ell_j}([x^j] (f * g.derivative / g mod p^a))`.
-/
def cldCoeffs (f : ZPoly) (p a : Nat) (g : ZPoly) : Array Int :=
  let quotient := cldQuotientMod f g p a
  let n := f.degree?.getD 0
  (List.range n).map
    (fun j => psiCut p a (bhksCoeffCutThreshold p f j) (quotient.coeff j))
    |>.toArray

/-- Per-coordinate BHKS cut thresholds for the all-coefficients CLD lattice. -/
def bhksCutThresholds (f : ZPoly) (p : Nat) : Array Nat :=
  let n := f.degree?.getD 0
  (List.range n).map (fun j => bhksCoeffCutThreshold p f j) |>.toArray

/--
Executable row-basis data for the BHKS all-coefficients CLD lattice.

The basis has row and column dimension `factorCount + coeffWidth`. Its first
`factorCount` columns are indicator coordinates, and its remaining
`coeffWidth` columns are CLD high-bit coordinates.
-/
structure BhksLatticeBasis where
  p : Nat
  precision : Nat
  factorCount : Nat
  coeffWidth : Nat
  liftedFactors : Array ZPoly
  cutThresholds : Array Nat
  cldRows : Array (Array Int)
  basis : Matrix Int (factorCount + coeffWidth) (factorCount + coeffWidth)

/--
Projected BHKS rows after LLL reduction and the Gram-Schmidt cut.

`cutRadiusSq4` stores `4 * B'^2 = 4r + n*r^2`, avoiding square-root or
floating-point arithmetic for the BHKS cut radius.
-/
structure BhksProjectedRows where
  factorCount : Nat
  coeffWidth : Nat
  cutRadiusSq4 : Nat
  reducedRowCount : Nat
  projectedRows : Array (Array Int)

private def bhksLatticeEntry
    (r n p a : Nat) (thresholds : Array Nat) (cldRows : Array (Array Int))
    (i j : Fin (r + n)) : Int :=
  if _hi : i.val < r then
    if _hj : j.val < r then
      if i.val = j.val then 1 else 0
    else
      (cldRows.getD i.val #[]).getD (j.val - r) 0
  else if _hj : j.val < r then
    0
  else
    let coord := i.val - r
    if j.val - r = coord then
      Int.ofNat (p ^ (a - thresholds.getD coord 0))
    else
      0

/--
Build the BHKS all-coefficients CLD row-basis matrix
`[ I_r | A_tilde ; 0 | diag(p^(a-l_j)) ]`.

The diagonal exponent uses natural subtraction; callers that need the exact
BHKS hypotheses should lift to a precision `a` satisfying every `l_j ≤ a`.
-/
def bhksLatticeBasis (f : ZPoly) (p a : Nat) (liftedFactors : Array ZPoly) :
    BhksLatticeBasis :=
  let r := liftedFactors.size
  let n := f.degree?.getD 0
  let thresholds := bhksCutThresholds f p
  let cldRows := liftedFactors.map (fun g => cldCoeffs f p a g)
  let basis : Matrix Int (r + n) (r + n) :=
    Matrix.ofFn (bhksLatticeEntry r n p a thresholds cldRows)
  { p
    precision := a
    factorCount := r
    coeffWidth := n
    liftedFactors
    cutThresholds := thresholds
    cldRows
    basis }

/-- Four times the squared BHKS cut radius, `4 * (r + n * (r / 2)^2)`. -/
def bhksCutRadiusSq4 (L : BhksLatticeBasis) : Nat :=
  4 * L.factorCount + L.coeffWidth * L.factorCount * L.factorCount

private def bhksWithinGramSchmidtCut (L : BhksLatticeBasis)
    (dets : Vector Nat (L.factorCount + L.coeffWidth + 1))
    (i : Fin (L.factorCount + L.coeffWidth)) : Bool :=
  let d0 := dets.get ⟨i.val,
    Nat.lt_trans i.isLt (Nat.lt_succ_self (L.factorCount + L.coeffWidth))⟩
  let d1 := dets.get ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  if d0 = 0 then
    false
  else
    4 * ((d1 : Rat) / (d0 : Rat)) ≤ (bhksCutRadiusSq4 L : Rat)

private def bhksProjectIndicator (r n : Nat) (v : Vector Int (r + n)) : Array Int :=
  (List.range r).map
    (fun j =>
      if h : j < r + n then
        v.get ⟨j, h⟩
      else
        0)
    |>.toArray

private def bhksRowsArrayToMatrix {m : Nat} (n : Nat) (rows : Array (Vector Int m)) :
    Matrix Int n m :=
  Matrix.ofFn fun i j => (rows.getD i.val (Vector.ofFn fun _ => 0))[j]

private theorem lll_delta_lower : (1 / 4 : Rat) < 3 / 4 := by
  grind

private theorem lll_delta_upper : (3 / 4 : Rat) ≤ 1 := by
  grind

private def bhksCutProjectReducedRows
    (L : BhksLatticeBasis)
    (reduced : Matrix Int (L.factorCount + L.coeffWidth)
        (L.factorCount + L.coeffWidth)) :
    Array (Array Int) :=
  let dets := GramSchmidt.Int.gramDetVec reduced
  (List.finRange (L.factorCount + L.coeffWidth)).foldl
    (fun acc i =>
      if bhksWithinGramSchmidtCut L dets i then
        acc.push (bhksProjectIndicator L.factorCount L.coeffWidth (reduced.row i))
      else
        acc)
    #[]

/--
Run LLL on a BHKS row-basis lattice, discard rows whose Gram-Schmidt squared
length exceeds the BHKS radius, and project survivors to the first `r`
indicator coordinates. The squared Gram-Schmidt lengths are computed from the
integer leading Gram determinant vector as `d_{i+1}/d_i`.

The result is the executable `L'` row data consumed by the later RREF /
equivalence-class recovery stage.
-/
def bhksProjectedRows (L : BhksLatticeBasis)
    (hrows : 1 ≤ L.factorCount + L.coeffWidth)
    (hind : L.basis.independent) : BhksProjectedRows :=
  let reducedRows :=
    lll.shortVectors L.basis (3 / 4) lll_delta_lower lll_delta_upper hrows hind
  let reducedBasis :=
    bhksRowsArrayToMatrix (L.factorCount + L.coeffWidth) reducedRows
  { factorCount := L.factorCount
    coeffWidth := L.coeffWidth
    cutRadiusSq4 := bhksCutRadiusSq4 L
    reducedRowCount := reducedRows.size
    projectedRows := bhksCutProjectReducedRows L reducedBasis }

private theorem bhksLatticeBasis_independent (L : BhksLatticeBasis) :
    L.basis.independent := by
  sorry

#guard psiCut 5 4 1 3 = 1
#guard psiCut 5 4 1 3 ≠ 3 / (5 : Int)

private def cldGuardF : ZPoly :=
  DensePoly.ofCoeffs #[6, -5, 1]

private def cldGuardG : ZPoly :=
  DensePoly.ofCoeffs #[-2, 1]

#guard cldQuotientMod cldGuardF cldGuardG 5 2 = DensePoly.ofCoeffs #[22, 1]

private def bhksGuardFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1]]

private def bhksGuardBasis : BhksLatticeBasis :=
  bhksLatticeBasis cldGuardF 5 2 bhksGuardFactors

#guard bhksGuardBasis.factorCount = 2
#guard bhksGuardBasis.coeffWidth = 2
#guard bhksGuardBasis.basis[0][0] = 1
#guard bhksGuardBasis.basis[0][1] = 0
#guard bhksGuardBasis.basis[0][2] = (bhksGuardBasis.cldRows.getD 0 #[]).getD 0 0
#guard bhksGuardBasis.basis[0][3] = (bhksGuardBasis.cldRows.getD 0 #[]).getD 1 0
#guard bhksGuardBasis.basis[0][2] ≠ bhksGuardFactors[0].coeff 0
#guard bhksGuardBasis.basis[1][0] = 0
#guard bhksGuardBasis.basis[1][1] = 1
#guard bhksGuardBasis.basis[2][0] = 0
#guard bhksGuardBasis.basis[2][2] =
  Int.ofNat (5 ^ (2 - bhksGuardBasis.cutThresholds.getD 0 0))
#guard bhksGuardBasis.basis[3][3] =
  Int.ofNat (5 ^ (2 - bhksGuardBasis.cutThresholds.getD 1 0))
#guard bhksCutRadiusSq4 bhksGuardBasis = 16
#guard bhksProjectIndicator 2 2 bhksGuardBasis.basis[0] = #[1, 0]
#guard (bhksProjectIndicator 2 2 bhksGuardBasis.basis[0]).size = bhksGuardBasis.factorCount

/--
Lift the projected integer rows of `L` into a rational row-basis matrix
sized `n × r`, with `n := L.projectedRows.size` and `r := L.factorCount`.
The matrix is the input to BHKS Lemma 3.3 RREF-based equivalence-class
identification.
-/
def bhksProjectedRowsAsRatMatrix
    (rows : Array (Array Int)) (n r : Nat) : Matrix Rat n r :=
  Matrix.ofFn fun i j =>
    ((rows.getD i.val #[]).getD j.val (0 : Int) : Rat)

private def bhksColumnSignature
    (echelonRows : Array (Array Rat)) (j : Nat) : Array Rat :=
  echelonRows.map (·.getD j 0)

private def bhksInsertSignatureClass
    (sig : Array Rat) (j : Nat) :
    List (Array Rat × List Nat) → List (Array Rat × List Nat)
  | [] => [(sig, [j])]
  | (s, members) :: rest =>
      if s = sig then (s, members ++ [j]) :: rest
      else (s, members) :: bhksInsertSignatureClass sig j rest

private def bhksClassIndicator (r : Nat) (members : List Nat) : Array Int :=
  ((List.range r).map (fun i => if i ∈ members then (1 : Int) else 0)).toArray

/--
BHKS equivalence-class indicator vectors over the projected lattice rows
of `L`.

Lifts the projected integer rows into a rational row-basis matrix, runs
`Matrix.rref` over `Q`, and groups column indices `0, …, r - 1` by their
echelon-column signature: indices `i` and `j` are equivalent iff every
echelon row agrees at positions `i` and `j` (BHKS Lemma 3.3 / FLINT
Algorithm 8). Each equivalence class produces one compact `0/1` indicator
of length `r`. Classes are emitted in the order they are first observed by
ascending column index.
-/
def bhksEquivalenceClassIndicators (L : BhksProjectedRows) : Array (Array Int) :=
  let n := L.projectedRows.size
  let r := L.factorCount
  let M : Matrix Rat n r := bhksProjectedRowsAsRatMatrix L.projectedRows n r
  let D := Matrix.rref M
  let echelonRows : Array (Array Rat) := D.echelon.toArray.map (·.toArray)
  let groups : List (List Nat) :=
    ((List.range r).foldl
        (fun acc j =>
          bhksInsertSignatureClass (bhksColumnSignature echelonRows j) j acc)
        []).map Prod.snd
  (groups.map (fun cls => bhksClassIndicator r cls)).toArray

private def bhksTwoClassProjectedRows : BhksProjectedRows :=
  { factorCount := 4
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 1
    projectedRows := #[#[1, 1, 0, 0]] }

#guard bhksEquivalenceClassIndicators bhksTwoClassProjectedRows =
  #[#[1, 1, 0, 0], #[0, 0, 1, 1]]

private def bhksSingletonClassProjectedRows : BhksProjectedRows :=
  { factorCount := 3
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 0
    projectedRows := #[] }

#guard bhksEquivalenceClassIndicators bhksSingletonClassProjectedRows =
  #[#[1, 1, 1]]

private def bhksNoProgressProjectedRows : BhksProjectedRows :=
  { factorCount := 3
    coeffWidth := 0
    cutRadiusSq4 := 0
    reducedRowCount := 3
    projectedRows := #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]] }

#guard bhksEquivalenceClassIndicators bhksNoProgressProjectedRows =
  #[#[1, 0, 0], #[0, 1, 0], #[0, 0, 1]]

private def liftModulus (d : LiftData) : Nat :=
  d.p ^ d.k

private def centeredLiftPoly (f : ZPoly) (m : Nat) : ZPoly :=
  DensePoly.ofCoeffs <| f.toArray.map fun coeff => centeredModNat coeff m

private def normalizeCandidateFactor (candidate : ZPoly) : ZPoly :=
  let primitive := ZPoly.primitivePart candidate
  if DensePoly.leadingCoeff primitive < 0 then
    DensePoly.scale (-1 : Int) primitive
  else
    primitive

private def bhksIndicatorSelectedFactors
    (liftedFactors : Array ZPoly) (indicator : Array Int) : Option (Array ZPoly) :=
  if indicator.size != liftedFactors.size then
    none
  else
    let indices := List.range indicator.size
    if indices.all (fun i => indicator.getD i 0 == 0 || indicator.getD i 0 == 1) &&
        indices.any (fun i => indicator.getD i 0 == 1) then
      some <| indices.foldl
        (fun selected i =>
          if indicator.getD i 0 == 1 then
            selected.push (liftedFactors.getD i 0)
          else
            selected)
        #[]
    else
      none

/--
Reconstruct and verify one BHKS equivalence-class indicator.

The indicator row is supplied by the later RREF recovery stage. This helper
only checks that the row is a nonempty `0/1` vector over the lifted factors,
forms `lc(f) * product selected g_i` modulo the Hensel modulus, applies the
centred integer lift, normalizes content and sign, and accepts the candidate
only when exact division of `f` succeeds.
-/
def bhksIndicatorCandidate?
    (f : ZPoly) (d : LiftData) (indicator : Array Int) : Option (ZPoly × ZPoly) :=
  match bhksIndicatorSelectedFactors d.liftedFactors indicator with
  | none => none
  | some selected =>
      let modulus := liftModulus d
      let raw := DensePoly.scale (DensePoly.leadingCoeff f) (Array.polyProduct selected)
      let candidate := normalizeCandidateFactor <|
        centeredLiftPoly (ZPoly.reduceModPow raw d.p d.k) modulus
      match exactQuotient? f candidate with
      | some quotient => some (candidate, quotient)
      | none => none

private def bhksIndicatorOneCount (r : Nat) (indicator : Array Int) : Nat :=
  (List.range r).foldl
    (fun count i => if indicator.getD i 0 == 1 then count + 1 else count)
    0

private def bhksIndicatorAllOnes (r : Nat) (indicator : Array Int) : Bool :=
  indicator.size == r && bhksIndicatorOneCount r indicator == r

private def bhksDegenerateIndicatorPartition
    (L : BhksProjectedRows) (indicators : Array (Array Int)) : Bool :=
  indicators.isEmpty ||
    L.projectedRows.isEmpty ||
    (indicators.size == 1 &&
      bhksIndicatorAllOnes L.factorCount (indicators.getD 0 #[]))

private def bhksIndicatorCandidates?
    (f : ZPoly) (d : LiftData) (indicators : Array (Array Int)) :
    Option (Array ZPoly) :=
  indicators.foldl
    (fun acc indicator =>
      match acc with
      | none => none
      | some candidates =>
          match bhksIndicatorCandidate? f d indicator with
          | some candidate => some (candidates.push candidate.1)
          | none => none)
    (some #[])

/--
Run the fixed-precision BHKS recovery pipeline.

This executable glue builds the CLD lattice for the lifted factors, runs LLL
plus the Gram-Schmidt cut, extracts BHKS Lemma 3.3 equivalence-class
indicators by RREF, reconstructs every indicated candidate by centred lifting,
and accepts only when the verified candidates multiply back to `f`.
-/
def bhksRecover? (f : ZPoly) (d : LiftData) : Option (Array ZPoly) :=
  let L := bhksLatticeBasis f d.p d.k d.liftedFactors
  if hrows : 1 ≤ L.factorCount + L.coeffWidth then
    let projected := bhksProjectedRows L hrows (bhksLatticeBasis_independent L)
    let indicators := bhksEquivalenceClassIndicators projected
    if bhksDegenerateIndicatorPartition projected indicators then
      none
    else
      match bhksIndicatorCandidates? f d indicators with
      | none => none
      | some candidates =>
          if Array.polyProduct candidates == f then
            some candidates
          else
            none
  else
    none

private def bhksIndicatorGuardLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := bhksGuardFactors }

#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[1, 0] =
  some (DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-3, 1])
#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[0, 0] = none
#guard bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[2, 0] = none
#guard (bhksIndicatorCandidate? cldGuardF bhksIndicatorGuardLift #[0, 1]).map Prod.snd =
  some (DensePoly.ofCoeffs #[-2, 1])

#guard bhksRecover? cldGuardF bhksIndicatorGuardLift =
  some bhksGuardFactors

private def bhksDegenerateRecoverLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[1]] }

#guard bhksRecover? cldGuardF bhksDegenerateRecoverLift = none

private def bhksFailedDivisionRecoverLift : LiftData :=
  { p := 5
    k := 2
    liftedFactors := #[DensePoly.ofCoeffs #[-2, 1], DensePoly.ofCoeffs #[-4, 1]] }

#guard bhksIndicatorCandidate? cldGuardF bhksFailedDivisionRecoverLift #[0, 1] = none
#guard bhksRecover? cldGuardF bhksFailedDivisionRecoverLift = none

private structure RecombinationLattice where
  rows : Nat
  cols : Nat
  coeffWidth : Nat
  rows_pos : 1 ≤ rows
  coeffWidth_le_cols : coeffWidth ≤ cols
  basis : Matrix Int rows cols

private def recombinationLattice? (d : LiftData) (coeffWidth : Nat) :
    Option RecombinationLattice :=
  if hrows : 0 < d.liftedFactors.size then
    let rows := d.liftedFactors.size
    let cols := coeffWidth + rows
    let modulusNat := liftModulus d
    let modulus := Int.ofNat modulusNat
    let basis : Matrix Int rows cols :=
      Matrix.ofFn fun i j =>
        if hcoeff : j.val < coeffWidth then
          centeredModNat (d.liftedFactors[i].coeff j.val) modulusNat
        else if j.val - coeffWidth = i.val then
          modulus
        else
          0
    some
      { rows
        cols
        coeffWidth
        rows_pos := hrows
        coeffWidth_le_cols := Nat.le_add_right coeffWidth rows
        basis }
  else
    none

private theorem recombinationLattice_independent (L : RecombinationLattice) :
    L.basis.independent := by
  sorry

private def decodeShortVector (coeffWidth cols : Nat) (v : Vector Int cols) : ZPoly :=
  DensePoly.ofCoeffs <|
    (List.range coeffWidth).map
      (fun i =>
        if h : i < cols then
          v.get ⟨i, h⟩
        else
          0)
    |>.toArray

private def shortVectorCandidates (L : RecombinationLattice) : Array ZPoly :=
  (lll.shortVectors L.basis (3 / 4) lll_delta_lower lll_delta_upper L.rows_pos
      (recombinationLattice_independent L)).map
    (decodeShortVector L.coeffWidth L.cols)

private structure RecombinationState where
  target : ZPoly
  factors : Array ZPoly

private def acceptRecombinationCandidate
    (state : RecombinationState) (candidate : ZPoly) : RecombinationState :=
  match exactQuotient? state.target candidate with
  | some quotient => { target := quotient, factors := state.factors.push candidate }
  | none => state

private def verifyShortVectorCandidates (target : ZPoly) (candidates : Array ZPoly) :
    Option (Array ZPoly) :=
  let final :=
    candidates.foldl acceptRecombinationCandidate { target, factors := #[] }
  if final.target = 1 then
    some final.factors
  else
    none

/--
Recombine lifted local factors via LLL short-vector enumeration.

The production recombination path; returns `none` when the LLL pass produces
no candidates that exactly partition `f`. Exposed (rather than `private`) so
the SPEC-sanctioned LLL-vs-exhaustive cross-check in `HexBerlekampZassenhaus/
CrossCheck.lean` can compare its output against `recombinationSearch` on the
same lifted-factor set.
-/
def recombineLLL? (f : ZPoly) (d : LiftData) : Option (Array ZPoly) :=
  let coeffWidth := f.degree?.getD 0 + 1
  match recombinationLattice? d coeffWidth with
  | none => none
  | some L => verifyShortVectorCandidates f (shortVectorCandidates L)

private def recombinationSearchAux
    (target : ZPoly) (localFactors : List ZPoly) : Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate := Array.polyProduct split.1.toArray
          match exactQuotient? target candidate with
          | none => none
          | some quotient =>
              match recombinationSearchAux quotient split.2 fuel with
              | none => none
              | some rest => some (candidate :: rest)

/--
Search for an integer-factor recombination of the lifted local factors.

The search enumerates subsets containing the first remaining local factor,
accepts a subset only when its product exactly divides the current target, and
then recurses on the quotient and unused local factors.
-/
def recombinationSearch (f : ZPoly) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchAux f localFactors (localFactors.length + 1)

private def recombinationSearchModAux
    (target : ZPoly) (modulus : Nat) (localFactors : List ZPoly) :
    Nat → Option (List ZPoly)
  | 0 => none
  | fuel + 1 =>
      if target = 1 then
        some []
      else
        firstSome (subsetSplitsWithFirst localFactors) fun split =>
          let candidate :=
            ZPoly.primitivePart <|
              centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
          match exactQuotient? target candidate with
          | none => none
          | some quotient =>
              match recombinationSearchModAux quotient modulus split.2 fuel with
              | none => none
              | some rest => some (candidate :: rest)

private def recombinationSearchMod
    (f : ZPoly) (modulus : Nat) (localFactors : List ZPoly) : Option (List ZPoly) :=
  recombinationSearchModAux f modulus localFactors (localFactors.length + 1)

private def recombineExhaustive (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearchMod f (liftModulus d) d.liftedFactors.toList with
  | some factors => factors.toArray
  | none => #[]

private def exhaustiveRecombinationLocalFactorLimit : Nat := 4

private def canUseExhaustiveRecombination (d : LiftData) : Bool :=
  d.liftedFactors.size ≤ exhaustiveRecombinationLocalFactorLimit

/--
The lifted factors contain enough information for the executable exhaustive
recombination search to recover factors of `f`.
-/
def LiftedFactorsRecombineTo (f : ZPoly) (d : LiftData) : Prop :=
  (∃ factors, recombineLLL? f d = some factors ∧ Array.polyProduct factors = f) ∨
    (recombineLLL? f d = none ∧ canUseExhaustiveRecombination d ∧
      ∃ factors,
        recombinationSearchMod f (liftModulus d) d.liftedFactors.toList = some factors)

/--
Recombine lifted local factors into integer factors.

The production path is LLL-based. Exhaustive subset recombination is retained
only as a small-input fallback; for larger inputs, an LLL miss is reported as
an explicit recombination failure.
-/
def recombine (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombineLLL? f d with
  | some factors => factors
  | none =>
      if canUseExhaustiveRecombination d then
        recombineExhaustive f d
      else
        #[]

private def recombineLLLBranchGuardFactors : Array ZPoly :=
  #[DensePoly.ofCoeffs #[-1, 1],
    DensePoly.ofCoeffs #[-2, 1],
    DensePoly.ofCoeffs #[-3, 1],
    DensePoly.ofCoeffs #[-4, 1],
    DensePoly.ofCoeffs #[-5, 1]]

private def recombineLLLBranchGuardInput : ZPoly :=
  Array.polyProduct recombineLLLBranchGuardFactors

private def recombineLLLBranchGuardLift : LiftData :=
  { p := 2
    k := 8
    liftedFactors := recombineLLLBranchGuardFactors }

#guard !canUseExhaustiveRecombination recombineLLLBranchGuardLift

#guard Array.polyProduct (recombine recombineLLLBranchGuardInput recombineLLLBranchGuardLift) =
  recombineLLLBranchGuardInput

private def initialHenselPrecision (B : Nat) : Nat :=
  if B ≤ 4 then B else 4

private def nextHenselPrecision (k B : Nat) : Nat :=
  if 2 * k < B then
    2 * k
  else
    B

private def factorFastCoreWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Nat → Nat → Option (Array ZPoly)
  | _k, 0 => none
  | k, fuel + 1 =>
      let liftData := henselLiftData core k primeData
      match bhksRecover? core liftData with
      | some factors => some factors
      | none =>
        if k ≥ B then
          none
        else
          factorFastCoreWithBound core B primeData (nextHenselPrecision k B) fuel

private def factorFastCoreGuardPrimeData : PrimeChoiceData :=
  choosePrimeData cldGuardF

#guard factorFastCoreWithBound cldGuardF 1 factorFastCoreGuardPrimeData
    (initialHenselPrecision 1) (ZPoly.quadraticDoublingSteps 1 + 2) =
  none

#guard factorFastCoreWithBound cldGuardF 4 factorFastCoreGuardPrimeData
    (initialHenselPrecision 4) (ZPoly.quadraticDoublingSteps 4 + 2) =
  some bhksGuardFactors

/--
Adaptively lift and retry LLL recombination, using the explicit bound as the
ceiling. If LLL recombination still fails at the bound, report the core as
irreducible under that bound.
-/
private def adaptiveCoreFactors
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Nat → Nat → Array ZPoly
  | _k, 0 => #[core]
  | k, fuel + 1 =>
      let liftData := henselLiftData core k primeData
      match recombineLLL? core liftData with
      | some factors => factors
      | none =>
          if k ≥ B then
            #[core]
          else
            adaptiveCoreFactors core B primeData
              (nextHenselPrecision k B) fuel

private def exhaustiveCoreFactorsWithBound
    (core : ZPoly) (B : Nat) (primeData : PrimeChoiceData) : Array ZPoly :=
  if B = 0 then
    #[core]
  else
    let liftData := henselLiftData core B primeData
    let factors := recombineExhaustive core liftData
    if factors.isEmpty then
      #[core]
    else
      factors

private def factorSlowFactorsWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    reassemblePolynomialFactors normalized #[]
  else
    match quadraticIntegerRootFactors? normalized.squareFreeCore with
    | some coreFactors => reassemblePolynomialFactors normalized coreFactors
    | none =>
        let primeData := choosePrimeData normalized.squareFreeCore
        let coreFactors :=
          exhaustiveCoreFactorsWithBound normalized.squareFreeCore B primeData
        reassemblePolynomialFactors normalized coreFactors

private def factorSlowWithBound (f : ZPoly) (B : Nat) : Factorization :=
  factorizationOfFactors f (factorSlowFactorsWithBound f B)

/--
Factor using the exhaustive recombination path at the default Mignotte
coefficient bound. This is the public slow-path backstop for the two-tier BZ
API.
-/
def factorSlow (f : ZPoly) : Factorization :=
  factorSlowWithBound f (ZPoly.defaultFactorCoeffBound f)

private def factorFastFactorsWithBound (f : ZPoly) (B : Nat) : Option (Array ZPoly) :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    some (reassemblePolynomialFactors normalized #[])
  else if B = 0 then
    none
  else
    if B = 1 then
      let primeData := choosePrimeData normalized.squareFreeCore
      if primeData.factorsModP.size ≤ 1 then
        some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
      else
        match factorFastCoreWithBound normalized.squareFreeCore B primeData
            (initialHenselPrecision B) (ZPoly.quadraticDoublingSteps B + 2) with
        | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
        | none => none
    else
      match quadraticIntegerRootFactors? normalized.squareFreeCore with
      | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
      | none =>
        let primeData := choosePrimeData normalized.squareFreeCore
        if primeData.factorsModP.size ≤ 1 then
          some (reassemblePolynomialFactors normalized #[normalized.squareFreeCore])
        else
          match factorFastCoreWithBound normalized.squareFreeCore B primeData
              (initialHenselPrecision B) (ZPoly.quadraticDoublingSteps B + 2) with
          | some coreFactors => some (reassemblePolynomialFactors normalized coreFactors)
          | none => none

#guard factorFastFactorsWithBound cldGuardF 1 = none

#guard factorFastFactorsWithBound cldGuardF 4 =
  some bhksGuardFactors

/--
Precision cap used by the public fast path.

The cap is the larger of the BHKS separation threshold bound and the
Mignotte coefficient bound, so later termination proofs can use the same
precision for both lattice separation and exact integer reconstruction.
-/
def factorFastPrecisionCap (f : ZPoly) : Nat :=
  max (bhksBound f) (ZPoly.defaultFactorCoeffBound f)

private def factorFastWithBound (f : ZPoly) (B : Nat) : Option Factorization :=
  (factorFastFactorsWithBound f B).map (factorizationOfFactors f)

/--
Public van Hoeij CLD fast path with a combined BHKS/Mignotte precision cap.

The bounded core loop only accepts candidates certified by the fixed-precision
BHKS recovery pipeline; if every precision up to the cap misses, this reports
`none` so the public `factor` combinator can use the slow backstop.
-/
def factorFast (f : ZPoly) : Option Factorization :=
  factorFastWithBound f (factorFastPrecisionCap f)

#guard (factorFast (DensePoly.ofCoeffs #[1, 1, 1, 1, 1])).map Factorization.product =
  some (DensePoly.ofCoeffs #[1, 1, 1, 1, 1])

#guard factorFastWithBound (DensePoly.ofCoeffs #[1, 0, 0, 0, 1]) 4 = none

/-- Factor with an explicit coefficient bound for the recombination stage. -/
def factorWithBound (f : ZPoly) (B : Nat) : Factorization :=
  (factorFastWithBound f B).getD (factorSlowWithBound f B)

#guard Factorization.product (factorWithBound cldGuardF 1) = cldGuardF

/--
Factor using the Mignotte-bounded fast attempt with exhaustive slow fallback.

The standalone `factorFast` entry point exposes the proof-facing combined
BHKS/Mignotte cap. The default total factorization combinator keeps the
runtime-oriented coefficient bound before falling back to exhaustive
recombination, so irreducible inputs that split modulo the chosen prime do not
force the full BHKS threshold search.
-/
def factor (f : ZPoly) : Factorization :=
  factorWithBound f (ZPoly.defaultFactorCoeffBound f)

namespace ZPoly

/-- Mathlib-free irreducibility predicate for integer polynomials. -/
class Irreducible (f : ZPoly) : Prop where
  not_zero : f ≠ 0
  not_unit : ¬ ZPoly.IsUnit f
  no_factors :
    ∀ a b : ZPoly, f = a * b → ZPoly.IsUnit a ∨ ZPoly.IsUnit b

private def isNatPrime (n : Nat) : Bool :=
  2 ≤ n && !((List.range n).any fun d => 2 ≤ d && d * d ≤ n && n % d == 0)

/-- Computational irreducibility checker backed by the public factorization API. -/
def isIrreducible (f : ZPoly) : Bool :=
  if f = 0 then
    false
  else if f.degree?.getD 0 = 0 then
    let k := (f.coeff 0).natAbs
    isNatPrime k
  else
    let φ := factor f
    decide (φ.scalar.natAbs = 1) &&
      φ.factors.size == 1 &&
      match φ.factors.toList with
      | [entry] => decide (entry.2 = 1)
      | _ => false

theorem isIrreducible_iff (f : ZPoly) :
    isIrreducible f = true ↔ Irreducible f := by
  sorry

instance instDecidableIrreducible (f : ZPoly) : Decidable (Irreducible f) :=
  decidable_of_iff _ (isIrreducible_iff f)

end ZPoly

/--
Conditional product contract for the bounded factorization entry point.
The bound hypothesis is the computational correctness assumption supplied by
the later proof layer.
-/
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ B) :
    Factorization.product (factorWithBound f B) = f := by
  sorry

/--
The normalization prefix and square-free core reassemble to the sign-normalized
input. The signed scalar in `Factorization` carries the original leading sign;
the polynomial factor array is normalized to positive leading sign.
-/
theorem normalizeForFactor_reassembles (f : ZPoly) :
    let normalized := normalizeForFactor f
    Array.polyProduct (normalizationPrefixFactors normalized ++ #[normalized.squareFreeCore]) =
      normalizeFactorSign f := by
  sorry

/--
Replacing the square-free core by a product-equivalent factor array preserves
the sign-normalized input.
-/
theorem reassembleNormalizedFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData) (coreFactors : Array ZPoly)
    (hnormalized : normalizeForFactor f = normalized)
    (hcore : Array.polyProduct coreFactors = normalized.squareFreeCore) :
    Array.polyProduct (reassembleNormalizedFactors normalized coreFactors) =
      normalizeFactorSign f := by
  subst normalized
  unfold reassembleNormalizedFactors
  rw [polyProduct_append, hcore]
  have hnormalized := normalizeForFactor_reassembles f
  change
    Array.polyProduct
        (normalizationPrefixFactors (normalizeForFactor f) ++
          #[(normalizeForFactor f).squareFreeCore]) =
      normalizeFactorSign f at hnormalized
  rw [polyProduct_append, polyProduct_singleton] at hnormalized
  exact hnormalized

/--
For constant square-free cores, the normalization-only factor array preserves the
sign-normalized input.
-/
theorem normalizedConstantFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData)
    (hnormalized : normalizeForFactor f = normalized)
    (hconst : normalized.squareFreeCore.degree?.getD 0 = 0) :
    Array.polyProduct (normalizedConstantFactors normalized) = normalizeFactorSign f := by
  subst normalized
  unfold normalizedConstantFactors
  split
  · rename_i hcore_one
    change Array.polyProduct (reassembleNormalizedFactors (normalizeForFactor f) #[]) =
      normalizeFactorSign f
    exact reassembleNormalizedFactors_product f (normalizeForFactor f) #[] rfl (by
      simp [Array.polyProduct, hcore_one])
  · change
      Array.polyProduct
          (reassembleNormalizedFactors (normalizeForFactor f)
            #[(normalizeForFactor f).squareFreeCore]) =
        normalizeFactorSign f
    exact reassembleNormalizedFactors_product f (normalizeForFactor f)
      #[(normalizeForFactor f).squareFreeCore] rfl (by
        exact polyProduct_singleton (normalizeForFactor f).squareFreeCore)

private theorem firstSome_some
    {α β : Type} {xs : List α} {f : α → Option β} {y : β}
    (h : firstSome xs f = some y) :
    ∃ x, f x = some y := by
  induction xs with
  | nil =>
      simp [firstSome] at h
  | cons x xs ih =>
      unfold firstSome at h
      cases hx : f x with
      | none =>
          simp [hx] at h
          exact ih h
      | some y' =>
          simp [hx] at h
          cases h
          exact ⟨x, hx⟩

private theorem recombinationSearchAux_product
    (target : ZPoly) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchAux target localFactors fuel = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        cases hquot : exactQuotient? target (Array.polyProduct split.1.toArray) with
        | none =>
            simp [hquot] at hsplit
        | some quotient =>
            simp [hquot] at hsplit
            cases hrec : recombinationSearchAux quotient split.2 fuel with
            | none =>
                simp [hrec] at hsplit
            | some rest =>
                simp [hrec] at hsplit
                cases hsplit
                have hrest :
                    Array.polyProduct rest.toArray = quotient :=
                  ih quotient split.2 rest hrec
                have hquot_prod :
                    quotient * Array.polyProduct split.1.toArray = target :=
                  exactQuotient?_product hquot
                calc
                  Array.polyProduct (Array.polyProduct split.1.toArray :: rest).toArray =
                      Array.polyProduct split.1.toArray * Array.polyProduct rest.toArray := by
                    exact polyProduct_cons_toArray (Array.polyProduct split.1.toArray) rest
                  _ = Array.polyProduct split.1.toArray * quotient := by
                    rw [hrest]
                  _ = quotient * Array.polyProduct split.1.toArray := by
                    rw [DensePoly.mul_comm_poly (S := Int)]
                  _ = target := hquot_prod

/-- A successful exhaustive recombination search preserves the target product. -/
theorem recombinationSearch_product
    (f : ZPoly) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearch f localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchAux_product f localFactors factors (localFactors.length + 1) hsearch

private theorem recombinationSearchModAux_product
    (target : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly) (fuel : Nat)
    (hsearch : recombinationSearchModAux target modulus localFactors fuel = some factors) :
    Array.polyProduct factors.toArray = target := by
  induction fuel generalizing target localFactors factors with
  | zero =>
      simp [recombinationSearchModAux] at hsearch
  | succ fuel ih =>
      unfold recombinationSearchModAux at hsearch
      by_cases htarget : target = 1
      · simp [htarget] at hsearch
        cases hsearch
        simpa [Array.polyProduct] using htarget.symm
      · simp [htarget] at hsearch
        rcases firstSome_some hsearch with ⟨split, hsplit⟩
        let candidate :=
          ZPoly.primitivePart <|
            centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        cases hquot : exactQuotient? target candidate with
        | none =>
            simp [candidate, hquot] at hsplit
        | some quotient =>
            simp [candidate, hquot] at hsplit
            cases hrec : recombinationSearchModAux quotient modulus split.2 fuel with
            | none =>
                simp [hrec] at hsplit
            | some rest =>
                simp [hrec] at hsplit
                cases hsplit
                have hrest :
                    Array.polyProduct rest.toArray = quotient :=
                  ih quotient split.2 rest hrec
                have hquot_prod : quotient * candidate = target :=
                  exactQuotient?_product hquot
                calc
                  Array.polyProduct (candidate :: rest).toArray =
                      candidate * Array.polyProduct rest.toArray := by
                    exact polyProduct_cons_toArray candidate rest
                  _ = candidate * quotient := by
                    rw [hrest]
                  _ = quotient * candidate := by
                    rw [DensePoly.mul_comm_poly (S := Int)]
                  _ = target := hquot_prod

private theorem recombinationSearchMod_product
    (f : ZPoly) (modulus : Nat) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearchMod f modulus localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  exact recombinationSearchModAux_product
    f modulus localFactors factors (localFactors.length + 1) hsearch

private theorem recombineExhaustive_product
    (f : ZPoly) (d : LiftData) (factors : List ZPoly)
    (hsearch :
      recombinationSearchMod f (liftModulus d) d.liftedFactors.toList =
        some factors) :
    Array.polyProduct (recombineExhaustive f d) = f := by
  unfold recombineExhaustive
  simp [hsearch, recombinationSearchMod_product f (liftModulus d)
    d.liftedFactors.toList factors hsearch]

/--
Product preservation for `recombine` under the lifted-factor recombination
hypothesis supplied by the Hensel/recombination proof layer.
-/
theorem recombine_product_of_lifted_factors
    (f : ZPoly) (d : LiftData)
    (hvalid : LiftedFactorsRecombineTo f d) :
    Array.polyProduct (recombine f d) = f := by
  unfold LiftedFactorsRecombineTo at hvalid
  unfold recombine
  rcases hvalid with hlll | hexhaustive
  · rcases hlll with ⟨factors, hlll, hproduct⟩
    simp [hlll, hproduct]
  · rcases hexhaustive with ⟨hlll, hsmall, factors, hsearch⟩
    have hproduct : Array.polyProduct (recombineExhaustive f d) = f :=
      recombineExhaustive_product f d factors hsearch
    simpa [recombine, hlll, hsmall] using hproduct

theorem checkIrreducibleCert_prime_data
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      primeData.checkForPolynomial f = true := by
  sorry

/--
A successful integer certificate exposes the per-prime nested Rabin checks:
`checkFactorCerts` validates the concrete modular factor array, the recorded
degrees, and the upstream `Berlekamp.checkIrreducibilityCertificate` result for
each aligned entry.
-/
theorem checkIrreducibleCert_certificate_alignment
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ primeData ∈ cert.perPrime.toList,
      primeData.checkFactorCerts = true := by
  sorry

theorem checkIrreducibleCert_degree_obstructions
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    cert.checkDegreeObstructions f = true := by
  sorry

theorem checkIrreducibleCert_obstructs_candidate_degrees
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (hcert : checkIrreducibleCert f cert = true) :
    ∀ targetDegree ∈ ZPolyIrreducibilityCertificate.candidateFactorDegrees f,
      cert.hasObstructionFor f targetDegree = true := by
  sorry

theorem degreeObstruction_no_subset_degree
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate)
    (obs : DegreeObstruction) (primeData : PrimeFactorData)
    (hobs : obs.checkForCertificate f cert = true)
    (hprime : cert.primeDataAt? obs.primeIndex = some primeData) :
    primeData.hasSubsetDegree obs.targetDegree = false := by
  sorry

end Hex
