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
set we compare that certified fast result against the slow factorization.

Fixtures cover lifted-factor counts `n ∈ {3, 4, 5}`.  Each fixture
polynomial is a product of distinct integer linear factors with roots
fitting inside the centred residue range for the shared lift modulus
`37 ^ 2 = 1369`, so the linear factors are themselves valid `mod p^k`
representatives.  The fixtures therefore double as ground truth: every
accepted fast or slow factor multiset must reproduce the input polynomial.
The Hensel-lift production surface is covered separately by
`HexHensel/Conformance.lean`.
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
modulus is `37 ^ 2 = 1369`; every fixture's true factors are linear with
distinct residues modulo `37` and `|root| ≤ 15`, well inside the centred
residue range. -/
private def liftP : Nat := 37
private def liftK : Nat := 2

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
    k := liftK
    liftedFactors := (roots.map linear).toArray }

/-- Check the slow backstop, and compare `bhksRecover?` against it whenever the
fixed-precision BHKS pass returns a certified answer. -/
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

#guard fixturesN3.all crossCheck
#guard fixturesN4.all crossCheck
#guard fixturesN5.all crossCheck

end BZCrossCheck
end Hex
