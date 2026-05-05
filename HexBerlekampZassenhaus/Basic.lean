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
      field := @zmod64FieldOfPrime 19 bounds_nineteen prime_nineteen } ]

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

/-- Factors that come from normalization before the square-free core is factored. -/
def normalizationPrefixFactors (d : FactorNormalizationData) : Array ZPoly :=
  contentFactorArray d.content ++
    xPowerFactorArray d.xPower ++
    repeatedPartFactorArray d.repeatedPart

/-- Reassemble normalization factors around the factors of the square-free core. -/
def reassembleNormalizedFactors
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) : Array ZPoly :=
  normalizationPrefixFactors d ++ coreFactors

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

private def liftModulus (d : LiftData) : Nat :=
  d.p ^ d.k

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

private theorem lll_delta_lower : (1 / 4 : Rat) < 3 / 4 := by
  sorry

private theorem lll_delta_upper : (3 / 4 : Rat) ≤ 1 := by
  sorry

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

private def recombineExhaustive (f : ZPoly) (d : LiftData) : Array ZPoly :=
  match recombinationSearch f d.liftedFactors.toList with
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
  ∃ factors, recombinationSearch f d.liftedFactors.toList = some factors

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

/-- Factor with an explicit coefficient bound for the recombination stage. -/
def factorWithBound (f : ZPoly) (B : Nat) : Array ZPoly :=
  let normalized := normalizeForFactor f
  if normalized.squareFreeCore.degree?.getD 0 = 0 then
    normalizedConstantFactors normalized
  else
    let primeData := choosePrimeData normalized.squareFreeCore
    let liftData := henselLiftData normalized.squareFreeCore B primeData
    let coreFactors := recombine normalized.squareFreeCore liftData
    if coreFactors.isEmpty then
      #[]
    else
      reassembleNormalizedFactors normalized coreFactors

/-- Factor using the library's uniform executable Mignotte coefficient bound. -/
def factor (f : ZPoly) : Array ZPoly :=
  factorWithBound f (ZPoly.defaultFactorCoeffBound f)

/--
Conditional product contract for the bounded factorization entry point.
The bound hypothesis is the computational correctness assumption supplied by
the later proof layer.
-/
theorem factor_product_of_bound (f : ZPoly) (B : Nat)
    (hB : ∀ g : ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ B) :
    Array.foldl (· * ·) 1 (factorWithBound f B) = f := by
  sorry

/--
The normalization prefix and square-free core reassemble to the original
input. This is the proof-facing invariant connecting content extraction,
`X`-power extraction, and primitive square-free reduction.
-/
theorem normalizeForFactor_reassembles (f : ZPoly) :
    let normalized := normalizeForFactor f
    Array.polyProduct (normalizationPrefixFactors normalized ++ #[normalized.squareFreeCore]) = f := by
  sorry

/--
Replacing the square-free core by a product-equivalent factor array preserves
the original normalized input.
-/
theorem reassembleNormalizedFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData) (coreFactors : Array ZPoly)
    (hnormalized : normalizeForFactor f = normalized)
    (hcore : Array.polyProduct coreFactors = normalized.squareFreeCore) :
    Array.polyProduct (reassembleNormalizedFactors normalized coreFactors) = f := by
  sorry

/--
For constant square-free cores, the normalization-only factor array preserves
the original input.
-/
theorem normalizedConstantFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData)
    (hnormalized : normalizeForFactor f = normalized)
    (hconst : normalized.squareFreeCore.degree?.getD 0 = 0) :
    Array.polyProduct (normalizedConstantFactors normalized) = f := by
  sorry

/-- A successful exhaustive recombination search preserves the target product. -/
theorem recombinationSearch_product
    (f : ZPoly) (localFactors factors : List ZPoly)
    (hsearch : recombinationSearch f localFactors = some factors) :
    Array.polyProduct factors.toArray = f := by
  sorry

/--
Product preservation for `recombine` under the lifted-factor recombination
hypothesis supplied by the Hensel/recombination proof layer.
-/
theorem recombine_product_of_lifted_factors
    (f : ZPoly) (d : LiftData)
    (hvalid : LiftedFactorsRecombineTo f d) :
    Array.polyProduct (recombine f d) = f := by
  sorry

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
