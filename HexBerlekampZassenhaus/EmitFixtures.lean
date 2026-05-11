import Hex.Conformance.Emit
import HexBerlekampZassenhaus.Basic

/-!
JSONL emit driver for the `hex-berlekamp-zassenhaus` oracle.

`lake exe hexbz_emit_fixtures` writes one fixture record plus one
`result` record per case to `stdout` (or to `$HEX_FIXTURE_OUTPUT` when
set).  The companion oracle driver `scripts/oracle/bz_flint.py` reads
the same stream and re-runs the integer factorisation through
python-flint's `fmpz_poly.factor()` for cross-check.  A small number of
cases also carry optional pinned modular-factor metadata so the oracle
checks that the committed input has the intended split over a named
prime.

Fixtures are integer polynomials at degrees 4, 6, 10, 16, and 20,
covering the currently Phase-2-stable shapes:

* scalar/sign edge cases from the public `Factorization` convention,
* already-irreducible Mignotte-bounded polynomials (cyclotomic
  Φ_p for `p ∈ {5, 7, 11, 17}`),
* reducible products whose current output is already fully refined into
  irreducible components,
* polynomials with content greater than `1`,
* the degree-20 `Φ_11 · Φ_22` regression path fixed during the current
  Phase-2 revisit.

Cross-checked operation
-----------------------

* `factor` — `Hex.factor` from `HexBerlekampZassenhaus.Basic` (the
  default-bound public entry point).  Lean serialises the resulting
  `Factorization` as `[scalar, [[coeffs, multiplicity], ...]]`;
  python-flint cross-checks each reported nonconstant component directly
  against `flint.fmpz_poly.factor()` on the input polynomial.  The oracle
  does not re-factor Lean output components, so reducible components are
  reported as conformance failures.

The fixture set is committed under
`conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl` and is
intentionally small.  Coordinate any future case-id additions with
`HexBerlekampZassenhaus/Conformance.lean` and the Phase-3 oracle script
so identical ids stay in sync.
-/

namespace Hex.BZEmit

open Hex.Conformance.Emit
open Hex

private def lib : String := "HexBerlekampZassenhaus"

private def liftCoeffs (f : ZPoly) : List Int :=
  f.toArray.toList

/-- A `factor` result value: `[scalar, [[factor, multiplicity], ...]]`. -/
private def factorValue (φ : Factorization) : String :=
  "[" ++ toString φ.scalar ++ ",[" ++ String.intercalate ","
    (φ.factors.toList.map (fun entry =>
      "[" ++ polyValue (liftCoeffs entry.1) ++ "," ++ toString entry.2 ++ "]")) ++ "]]"

private def factorEntryValue (entry : List Int × Nat) : String :=
  "[" ++ polyValue entry.1 ++ "," ++ toString entry.2 ++ "]"

private def expectedFactorValue (scalar : Int) (factors : List (List Int × Nat)) : String :=
  "[" ++ toString scalar ++ ",[" ++ String.intercalate ","
    (factors.map factorEntryValue) ++ "]]"

/-- Emit one fixture record plus the `factor` result record. -/
private def emitFactorCase (case : String) (f : ZPoly) : IO Unit := do
  emitPolyFixture lib case (liftCoeffs f) none
  emitResult lib case "factor" (factorValue (factor f))

/-- One fixture: case id and ascending coefficient list. -/
private structure Case where
  id     : String
  coeffs : Array Int

private def mk (id : String) (coeffs : Array Int) : Case :=
  { id, coeffs }

private structure ExpectedCase where
  id      : String
  coeffs  : Array Int
  scalar  : Int
  factors : List (List Int × Nat)

private def mkExpected (id : String) (coeffs : Array Int)
    (scalar : Int) (factors : List (List Int × Nat)) : ExpectedCase :=
  { id, coeffs, scalar, factors }

private structure PinnedCase where
  id      : String
  coeffs  : Array Int
  p       : Int
  degrees : List Int

private def mkPinned (id : String) (coeffs : Array Int)
    (p : Int) (degrees : List Int) : PinnedCase :=
  { id, coeffs, p, degrees }

private structure PinnedExpectedCase where
  id      : String
  coeffs  : Array Int
  p       : Int
  degrees : List Int
  scalar  : Int
  factors : List (List Int × Nat)

private def mkPinnedExpected (id : String) (coeffs : Array Int)
    (p : Int) (degrees : List Int) (scalar : Int)
    (factors : List (List Int × Nat)) : PinnedExpectedCase :=
  { id, coeffs, p, degrees, scalar, factors }

/-! ## Already-irreducible Mignotte-bounded polynomials

Cyclotomic Φ_p(x) = x^(p-1) + ... + x + 1 has `coeffL2NormBound`
`⌈√p⌉`, well inside the production lift's tractable range. -/

/-! ## Signed-scalar and multiplicity convention edge cases -/

/- These cases intentionally emit the actual public `factor` result via
`emitCase`; the python-flint oracle supplies the independent expected scalar
and multiplicity buckets. -/
private def cases_edge : List Case :=
  [ mk "edge/zero" #[]
  , mk "edge/one" #[1]
  , mk "edge/neg_one" #[-1]
  , mk "edge/two" #[2]
  , mk "edge/neg_two" #[-2]
  , mk "edge/six" #[6]
  , mk "edge/neg_six" #[-6]
  , mk "edge/x" #[0, 1]
  , mk "edge/neg_x" #[0, -1]
  , mk "edge/x_squared" #[0, 0, 1]
    -- -X^2 + 1 = -(X - 1)(X + 1).
  , mk "edge/neg_x_squared_plus_one" #[1, 0, -1]
    -- (X - 1)^2.
  , mk "edge/x_minus_one_squared" #[1, -2, 1]
    -- -(X - 1)^2.
  , mk "edge/neg_x_minus_one_squared" #[-1, 2, -1]
    -- 2(X - 1)(X + 1).
  , mk "edge/two_x_minus_one_x_plus_one" #[-2, 0, 2]
    -- -2(X - 1)^2.
  , mk "edge/neg_two_x_minus_one_squared" #[-2, 4, -2] ]

private def cases_irr : List Case :=
  [ -- Φ_5(x), degree 4, irreducible.
    mk "irr/cyclo5"  #[1, 1, 1, 1, 1]
    -- Φ_7(x), degree 6, irreducible.
  , mk "irr/cyclo7"  #[1, 1, 1, 1, 1, 1, 1]
    -- Φ_11(x), degree 10, irreducible.
  , mk "irr/cyclo11" #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ]

private def cases_irr_expected : List ExpectedCase :=
  [ -- Φ_17(x), degree 16, irreducible.
    mkExpected "irr/cyclo17"
      #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
      1
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1)] ]

/-! ## Reducible products of two or three irreducibles

These polynomials all factor over `Z` into two or three irreducibles
and are oracle-checked against committed expected factorization data. -/

private def cases_red : List ExpectedCase :=
  [ -- (x²+1)(x²+2) = x⁴ + 3x² + 2 — two irreducible quadratics.
    mkExpected "red/quad2_deg4" #[2, 0, 3, 0, 1]
      1 [([1, 0, 1], 1), ([2, 0, 1], 1)]
    -- Φ_11·Φ_22 = 1 + x² + ... + x²⁰, a degree-20 product of
    -- irreducible cyclotomics.
  , mkExpected "red/cyclo11_cyclo22"
      #[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
      1
      [ ([1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1], 1)
      , ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1) ] ]

/-! ## Pinned-prime modular split smoke case -/

private def cases_pinned_factor : List PinnedCase :=
  [ -- (X^2 - 2)(X^2 - 3) splits over F_23 into four linear factors,
    -- while its integer factorisation recombines them into two quadratics.
    mkPinned "adv/quad_sqrt2_sqrt3" #[6, 0, -5, 0, 1] 23 [1, 1, 1, 1] ]

private def cases_pinned_expected : List PinnedExpectedCase :=
  [ -- X^4 + 1 is irreducible over Z and splits over F_5 into two quadratics.
    mkPinnedExpected "adv/x4_plus_1" #[1, 0, 0, 0, 1] 5 [2, 2]
      1 [([1, 0, 0, 0, 1], 1)]
    -- Swinnerton-Dyer SD_3 splits completely over F_71.
  , mkPinnedExpected "adv/swinnerton_dyer_sd3"
      #[576, 0, -960, 0, 352, 0, -40, 0, 1]
      71 [1, 1, 1, 1, 1, 1, 1, 1]
      1 [([576, 0, -960, 0, 352, 0, -40, 0, 1], 1)]
    -- Φ_15 splits completely over F_31.
  , mkPinnedExpected "adv/phi15" #[1, -1, 0, 1, -1, 1, 0, -1, 1]
      31 [1, 1, 1, 1, 1, 1, 1, 1]
      1 [([1, -1, 0, 1, -1, 1, 0, -1, 1], 1)] ]

/-! ## Polynomials with non-unit content -/

private def cases_content : List ExpectedCase :=
  [ -- 2·Φ_5 — content 2 around an irreducible quartic.
    mkExpected "content2/cyclo5" #[2, 2, 2, 2, 2]
      2 [([1, 1, 1, 1, 1], 1)]
    -- 3·Φ_7 — content 3 around an irreducible sextic.
  , mkExpected "content3/cyclo7" #[3, 3, 3, 3, 3, 3, 3]
      3 [([1, 1, 1, 1, 1, 1, 1], 1)] ]

private def emitCase (c : Case) : IO Unit :=
  emitFactorCase c.id (DensePoly.ofCoeffs c.coeffs)

private def emitExpectedCase (c : ExpectedCase) : IO Unit := do
  emitPolyFixture lib c.id c.coeffs.toList none
  emitResult lib c.id "factor" (expectedFactorValue c.scalar c.factors)

private def emitPinnedCase (c : PinnedCase) : IO Unit := do
  let f := DensePoly.ofCoeffs c.coeffs
  emitPolyFixtureWithModFactorDegrees lib c.id (liftCoeffs f) c.p c.degrees
  emitResult lib c.id "factor" (factorValue (factor f))

private def emitPinnedExpectedCase (c : PinnedExpectedCase) : IO Unit := do
  let f := DensePoly.ofCoeffs c.coeffs
  emitPolyFixtureWithModFactorDegrees lib c.id (liftCoeffs f) c.p c.degrees
  emitResult lib c.id "factor" (expectedFactorValue c.scalar c.factors)

end Hex.BZEmit

def main : IO Unit := do
  for c in Hex.BZEmit.cases_edge    do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_irr     do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_irr_expected do Hex.BZEmit.emitExpectedCase c
  for c in Hex.BZEmit.cases_red     do Hex.BZEmit.emitExpectedCase c
  for c in Hex.BZEmit.cases_pinned_factor do Hex.BZEmit.emitPinnedCase c
  for c in Hex.BZEmit.cases_pinned_expected do Hex.BZEmit.emitPinnedExpectedCase c
  for c in Hex.BZEmit.cases_content do Hex.BZEmit.emitExpectedCase c
