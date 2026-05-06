import Hex.Conformance.Emit
import HexBerlekampZassenhaus.Basic

/-!
JSONL emit driver for the `hex-berlekamp-zassenhaus` oracle.

`lake exe hexbz_emit_fixtures` writes one fixture record plus one
`result` record per case to `stdout` (or to `$HEX_FIXTURE_OUTPUT` when
set).  The companion oracle driver `scripts/oracle/bz_flint.py` reads
the same stream and re-runs the integer factorisation through
python-flint's `fmpz_poly.factor()` for cross-check.

Fixtures are integer polynomials at degrees 4, 6, 10, 16, and 20,
covering the currently Phase-2-stable shapes:

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
  `Array ZPoly` as a JSON array of coefficient lists; python-flint
  cross-checks by comparing each reported nonconstant component directly
  against `flint.fmpz_poly.factor()` on the input polynomial.  The oracle
  does not re-factor Lean output components, so reducible components are
  reported as conformance failures.

The fixture set is committed under
`conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl` and is
intentionally small.  Coordinate any future case-id additions with
the eventual `HexBerlekampZassenhaus/Conformance.lean` Phase-3 module
so identical ids stay in sync.
-/

namespace Hex.BZEmit

open Hex.Conformance.Emit
open Hex

private def lib : String := "HexBerlekampZassenhaus"

private def liftCoeffs (f : ZPoly) : List Int :=
  f.toArray.toList

/-- A `factor` result value: a JSON array of coefficient lists. -/
private def factorValue (factors : Array ZPoly) : String :=
  "[" ++ String.intercalate ","
    (factors.toList.map (fun f => polyValue (liftCoeffs f))) ++ "]"

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

/-! ## Already-irreducible Mignotte-bounded polynomials

Cyclotomic Φ_p(x) = x^(p-1) + ... + x + 1 has `coeffL2NormBound`
`⌈√p⌉`, well inside the production lift's tractable range. -/

private def cases_irr : List Case :=
  [ -- Φ_5(x), degree 4, irreducible.
    mk "irr/cyclo5"  #[1, 1, 1, 1, 1]
    -- Φ_7(x), degree 6, irreducible.
  , mk "irr/cyclo7"  #[1, 1, 1, 1, 1, 1, 1]
    -- Φ_11(x), degree 10, irreducible.
  , mk "irr/cyclo11" #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    -- Φ_17(x), degree 16, irreducible.
  , mk "irr/cyclo17" #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ]

/-! ## Reducible products of two or three irreducibles

These polynomials all factor over `Z` into two or three irreducibles
and have small enough Mignotte bound that the production lift
completes quickly. -/

private def cases_red : List Case :=
  [ -- (x²+1)(x²+2) = x⁴ + 3x² + 2 — two irreducible quadratics.
    mk "red/quad2_deg4" #[2, 0, 3, 0, 1]
    -- Φ_11·Φ_22 = 1 + x² + ... + x²⁰, a degree-20 product of
    -- irreducible cyclotomics.
  , mk "red/cyclo11_cyclo22"
      #[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ]

/-! ## Polynomials with non-unit content -/

private def cases_content : List Case :=
  [ -- 2·Φ_5 — content 2 around an irreducible quartic.
    mk "content2/cyclo5" #[2, 2, 2, 2, 2]
    -- 3·Φ_7 — content 3 around an irreducible sextic.
  , mk "content3/cyclo7" #[3, 3, 3, 3, 3, 3, 3] ]

private def emitCase (c : Case) : IO Unit :=
  emitFactorCase c.id (DensePoly.ofCoeffs c.coeffs)

end Hex.BZEmit

def main : IO Unit := do
  for c in Hex.BZEmit.cases_irr     do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_red     do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_content do Hex.BZEmit.emitCase c
