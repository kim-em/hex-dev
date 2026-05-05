import HexBerlekampZassenhaus.Basic

/-!
LLL vs exhaustive recombination cross-check for `HexBerlekampZassenhaus`.

Oracle: none (Tier-G fast-vs-fast)
Mode: always

`SPEC/Libraries/hex-berlekamp-zassenhaus.md` sanctions exhaustive subset
recombination as a small-input fallback / conformance oracle for the
production LLL recombination path.  This module operationalises that
contract: for each fixture polynomial we run `recombineLLL?` (the
production LLL path) and `recombinationSearch` (the exhaustive subset
path) on the same lifted-factor set and assert they produce the same
factor multiset.

Fixtures cover lifted-factor counts `n ∈ {3, 4, 5, 6, 8}`.  Each fixture
polynomial is a product of distinct integer linear factors with roots
fitting inside the centred residue range for the shared lift modulus
`2 ^ 8 = 256`, so the linear factors are themselves valid `mod p^k`
representatives — the same shape as the production-path branch guard
`recombineLLLBranchGuardLift` in `HexBerlekampZassenhaus/Basic`.  The
fixtures therefore double as ground truth: both algorithms must
additionally produce a factor multiset whose ordered product reproduces
the input polynomial.  The Hensel-lift production surface is covered
separately by `HexHensel/Conformance.lean`.
-/
namespace Hex
namespace BZCrossCheck

/-- The integer linear polynomial `x - r`. -/
private def linear (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

/-- The integer polynomial whose distinct integer roots are `roots`. -/
private def fromRoots (roots : List Int) : ZPoly :=
  Array.polyProduct (roots.map linear).toArray

/-- Sort the factor array by negated constant term, which equals the
unique integer root for each linear factor and so determines the factor
multiset uniquely under the fixture-design assumption (distinct integer
roots, all factors linear). -/
private def sortedRoots (factors : Array ZPoly) : Array Int :=
  (factors.map fun p => -(p.coeff 0)).qsort (· ≤ ·)

/-- Lift modulus exponent used uniformly across the fixtures.  The shared
modulus is `2 ^ 8 = 256`; every fixture's true factors are linear with
`|root| ≤ 15`, well inside the centred residue range `[-128, 127]`.
This matches the lift precision used by the production-path branch
guard `recombineLLLBranchGuardLift` in `HexBerlekampZassenhaus/Basic`. -/
private def liftP : Nat := 2
private def liftK : Nat := 8

/-- Construct a `LiftData` whose `liftedFactors` are the exact integer
linear factors of `fromRoots roots`.  These factors are already in
`mod p^k` form because their coefficients fit inside the centred
residue range for `p^k = 256`, so this short-circuits `henselLiftData`
without changing the recombination input the algorithms see.  We still
exercise the full `recombineLLL?` / `recombinationSearch` cross-check
on the resulting lifted-factor set; the Hensel-lift production surface
is covered separately by `HexHensel/Conformance.lean`. -/
private def liftDataOf (roots : List Int) : LiftData :=
  { p := liftP
    k := liftK
    liftedFactors := (roots.map linear).toArray }

/-- Run `recombineLLL?` and `recombinationSearch` on the same lifted-factor
set, and check the two factorisations agree as multisets and that each
multiset is a true factorisation of the fixture polynomial. -/
private def crossCheck (roots : List Int) : Bool :=
  let f := fromRoots roots
  let liftData := liftDataOf roots
  match recombineLLL? f liftData,
        recombinationSearch f liftData.liftedFactors.toList with
  | some lll, some search =>
      let searchArr := search.toArray
      decide (lll.size = search.length) &&
        decide (sortedRoots lll = sortedRoots searchArr) &&
        decide (Array.polyProduct lll = f) &&
        decide (Array.polyProduct searchArr = f)
  | _, _ => false

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

private def fixturesN6 : List (List Int) :=
  [ [1, 2, 3, 4, 5, 6]
  , [-1, -2, 3, 4, -5, 6]
  , [1, 2, 4, 5, 7, 8] ]

private def fixturesN8 : List (List Int) :=
  [ [1, 2, 3, 4, 5, 6, 7, 8]
  , [-1, -2, -3, -4, 5, 6, 7, 8]
  , [1, 3, 5, 7, 9, 11, 13, 15] ]

#guard fixturesN3.all crossCheck
#guard fixturesN4.all crossCheck
#guard fixturesN5.all crossCheck
#guard fixturesN6.all crossCheck
#guard fixturesN8.all crossCheck

end BZCrossCheck
end Hex
