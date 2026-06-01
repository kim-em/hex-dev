import HexBerlekampZassenhaus.Basic

/-!
BHKS fast-path vs slow-backstop cross-check for `HexBerlekampZassenhaus`.

Oracle: none (Tier-G fast-vs-fast)
Mode: always

`SPEC/Libraries/hex-berlekamp-zassenhaus.md` pins the production fast path
to the van Hoeij/BHKS CLD lattice, with exhaustive subset recombination
retained only as the slow backstop.  This module operationalises that
contract: for each fixture polynomial we run `factorSlow`, and when
fixed-precision `bhksRecover?` returns `some` on the committed lifted-factor
set we check that the certified fast result preserves the same input product.
If fixed-precision recovery returns `none`, the fast path has made no
correctness claim; that is an allowed miss for this Lean-only cross-check.

Fixtures cover lifted-factor counts `n ∈ {3, 4, 5}`.  Most fixture
polynomials are products of distinct integer linear factors with roots fitting
inside the centred residue range for the shared lift modulus `37 ^ 2 = 1369`,
so the linear factors are themselves valid `mod p^k` representatives.  A
separate adversarial fixture uses four Hensel-lifted linear factors whose
expected integer factors are two quadratic subset products.  The fixtures
therefore double as ground truth: every accepted fast or slow factor multiset
must reproduce the input polynomial, and the adversarial fast result must match
the committed factor buckets.
-/
namespace Hex
namespace BZCrossCheck

private instance boundsTwentyThree : ZMod64.Bounds 23 := ⟨by decide, by decide⟩
private instance boundsThirteen : ZMod64.Bounds 13 := ⟨by decide, by decide⟩
private instance boundsThirtyOne : ZMod64.Bounds 31 := ⟨by decide, by decide⟩

/-- The integer linear polynomial `x - r`. -/
private def linear (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

private def zpoly (coeffs : Array Int) : ZPoly :=
  DensePoly.ofCoeffs coeffs

private def polyTwentyThree (coeffs : Array Nat) : FpPoly 23 :=
  FpPoly.ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 23 n))

/-- The integer polynomial whose distinct integer roots are `roots`. -/
private def fromRoots (roots : List Int) : ZPoly :=
  Array.polyProduct (roots.map linear).toArray

private def positiveRoots (n : Nat) : List Int :=
  (List.range n).map fun i => Int.ofNat (i + 1)

private def positiveRootNats (n : Nat) : List Nat :=
  (List.range n).map fun i => i + 1

/-- Sort the factor array by negated constant term, which equals the
unique integer root for each linear factor and so determines the factor
multiset uniquely under the fixture-design assumption (distinct integer
roots, all factors linear). -/
private def sortedRoots (factors : Array ZPoly) : Array Int :=
  (factors.map fun p => -(p.coeff 0)).qsort (· ≤ ·)

private def coeffs (f : ZPoly) : List Int :=
  f.toArray.toList

private def factorCoeffSummary (factors : Array ZPoly) : List (List Int) :=
  factors.toList.map coeffs

private def sameCoeffSet (actual expected : List (List Int)) : Bool :=
  actual.length == expected.length &&
    expected.all (fun target => actual.any (fun got => got == target)) &&
    actual.all (fun got => expected.any (fun target => got == target))

/-- Lift modulus exponent used uniformly across the fixtures.  The shared
modulus is `37 ^ 2 = 1369`; every fixture's true factors are linear with
distinct residues modulo `37` and `|root| ≤ 15`, well inside the centred
residue range. -/
private def liftP : Nat := 37
private def liftK : Nat := 2

/-- Fixed lift modulus used by the committed `LiftData` fixtures. -/
private def liftModulus : Nat :=
  liftP ^ liftK

/-- True when the constant coefficient of `x - r` is already represented by
the centred residue interval for the fixed modulus.  The linear coefficient
is `1`, so the root bound is the only nontrivial coefficient check for these
fixtures. -/
private def rootFitsCentredLift (r : Int) : Bool :=
  r.natAbs ≤ liftModulus / 2

/-- Fixture roots are intentionally pairwise distinct so each integer factor is
a separate linear irreducible and `sortedRoots` identifies the factor multiset
by its roots. -/
private def rootsDistinct (roots : List Int) : Bool :=
  roots.length == roots.eraseDups.length

/-- Local fixture precondition: distinct integer roots, all already in the
centred residue range for the fixed `p^k`. -/
private def fixtureAssumptions (roots : List Int) : Bool :=
  rootsDistinct roots && roots.all rootFitsCentredLift

private def batchAssumptions (batch : List (List Int)) : Bool :=
  batch.all fixtureAssumptions

/-- Construct a `LiftData` whose `liftedFactors` are the exact integer
linear factors of `fromRoots roots`.  These factors are already in
`mod p^k` form because their coefficients fit inside the centred
residue range for `p^k = 1369`, so this short-circuits `henselLiftData`
without changing the recombination input the algorithms see.  We still
exercise the fixed-precision BHKS recovery path on the resulting
lifted-factor set; the Hensel-lift production surface is covered separately
by `HexHensel/Conformance.lean`. -/
private def liftDataOf (roots : List Int) : LiftData :=
  { p := liftP
    p_pos := by decide
    k := liftK
    liftedFactors := (roots.map linear).toArray }

/-- Check the slow backstop, and compare fixed-precision BHKS recovery against
the fixture product when recovery succeeds.

The `none` branch means the fixed-precision fast path did not certify a
recombination at `liftP ^ liftK`; it is accepted here because the public
factorization API falls back to `factorSlow` in that case. -/
private def crossCheck (roots : List Int) : Bool :=
  let f := fromRoots roots
  let liftData := liftDataOf roots
  let slow := factorSlow f
  let fastMatches :=
    match bhksRecover? f liftData with
    | none => true
    | some recovered =>
        decide (Array.polyProduct recovered = f)
  decide (Factorization.product slow = f) && fastMatches

private def sqrtTwoThreeProduct : ZPoly :=
  zpoly #[6, 0, -5, 0, 1]

private def sqrtTwoThreeExpectedFactors : Array ZPoly :=
  #[zpoly #[-2, 0, 1], zpoly #[-3, 0, 1]]

private def sqrtTwoThreePrimeData : PrimeChoiceData :=
  { p := 23
    fModP := ZPoly.modP 23 sqrtTwoThreeProduct
    factorsModP :=
      #[ polyTwentyThree #[18, 1]
       , polyTwentyThree #[5, 1]
       , polyTwentyThree #[16, 1]
       , polyTwentyThree #[7, 1] ] }

private def sqrtTwoThreeLiftData : LiftData :=
  henselLiftData sqrtTwoThreeProduct 4 sqrtTwoThreePrimeData

/-- Check a fixture where several lifted linear factors recombine into each
expected integer factor.  The fixed-precision BHKS path may conservatively
return `none`; if it returns `some`, the recovered buckets must match the
committed integer factorization shape. -/
private def crossCheckBuckets
    (f : ZPoly) (liftData : LiftData) (expectedFactors : Array ZPoly) : Bool :=
  let slow := factorSlow f
  let fastMatches :=
    match bhksRecover? f liftData with
    | none => true
    | some recovered =>
        decide (Array.polyProduct recovered = f) &&
          sameCoeffSet (factorCoeffSummary recovered) (factorCoeffSummary expectedFactors)
  decide (Factorization.product slow = f) && fastMatches

/-! ## Fixture batches by lifted-factor count `n` -/

private def fixturesN3 : List (List Int) :=
  [ [1, 2, 3]
  , [-1, 2, 5]
  , [3, -7, 11] ]

private def fixturesN4 : List (List Int) :=
  [ [1, 2, 3, 4]
  , [-1, -2, 3, 4]
  , [1, -3, 5, -7] ]

private def fixturesN5 : List (List Int) :=
  [ [1, 2, 3, 4, 5]
  , [-1, 2, -3, 4, -5]
  , [2, 3, 5, 7, 11] ]

#guard batchAssumptions fixturesN3
#guard batchAssumptions fixturesN4
#guard batchAssumptions fixturesN5

#guard fixturesN3.all crossCheck
#guard fixturesN4.all crossCheck
#guard fixturesN5.all crossCheck

#guard sqrtTwoThreeLiftData.liftedFactors.size = 4
#guard crossCheckBuckets sqrtTwoThreeProduct sqrtTwoThreeLiftData sqrtTwoThreeExpectedFactors

/-! ## Good-prime regression fixtures -/

private def splitProduct11 : ZPoly := fromRoots (positiveRoots 11)
private def splitProduct24 : ZPoly := fromRoots (positiveRoots 24)

private def hasRootCollisionModulo (p : Nat) (roots : List Nat) : Bool :=
  let residues := roots.map (fun r => r % p)
  residues.length != residues.eraseDups.length

#guard isGoodPrime splitProduct11 13
#guard isGoodPrime splitProduct24 31
#guard (choosePrimeData? splitProduct11).isSome
#guard (choosePrimeData? splitProduct24).isSome
#guard [3, 5, 7, 11, 13, 17, 19, 23, 31, 71].all
  (fun p => hasRootCollisionModulo p (positiveRootNats 72))

end BZCrossCheck
end Hex
