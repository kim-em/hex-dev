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

Fixtures are integer polynomials at degrees 4, 6, 8, 10, 16, and 20,
covering the currently Phase-2-stable shapes:

* scalar/sign edge cases from the public `Factorization` convention,
* already-irreducible Mignotte-bounded polynomials (cyclotomic
  Φ_p for `p ∈ {5, 7, 11, 17}`),
* reducible products whose current output is already fully refined into
  irreducible components,
* polynomials with content greater than `1`,
* the degree-20 `Φ_11 · Φ_22` reducible product,
* HO-2 (#2565) adversarial cases where mod-p factors split more finely
  than the integer factorisation; see "HO-2 adversarial coverage" below.

HO-2 adversarial coverage
-------------------------

`SPEC/Libraries/hex-berlekamp-zassenhaus.md` §"Conformance fixtures"
requires the core profile to include at least one input where the integer
factorisation requires a non-trivial subset product of lifted mod-p factors,
and at least one input that splits heavily (≥ 4 distinct mod-p factors)
over a small admissible prime.  Four `adv/*` cases are emitted with pinned
`modFactorPrime` / `modFactorDegrees` metadata so the oracle independently
verifies the named modular split:

* `adv/quad_sqrt2_sqrt3` — `(X² − 2)(X² − 3)` splits over F₂₃ as four
  linear factors that recombine into two integer quadratics
  (non-trivial subset product, heavy split over a small admissible prime).
* `adv/x4_plus_1` — `X⁴ + 1`, irreducible over ℤ, splits over F₅ as
  two quadratics (subset-product over a small admissible prime).
* `adv/swinnerton_dyer_sd3` — degree-8 Swinnerton-Dyer SD₃, irreducible
  over ℤ, splits completely as eight linear factors over F₇₁
  (heavy split).
* `adv/phi15` — Φ₁₅, irreducible over ℤ, splits completely as eight
  linear factors over F₃₁ (heavy split, small admissible prime).

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

/--
One `Factorization.factors` entry as `[coeffs, multiplicity]`.

`coeffs` are ascending integer coefficients for a primitive nonconstant
polynomial factor, and `multiplicity` is the positive exponent attached to
that factor.
-/
private def factorEntryValue (entry : List Int × Nat) : String :=
  "[" ++ polyValue entry.1 ++ "," ++ toString entry.2 ++ "]"

/-- The factor-entry list inside a `Factorization` value. -/
private def factorEntriesValue (factors : List (List Int × Nat)) : String :=
  "[" ++ String.intercalate "," (factors.map factorEntryValue) ++ "]"

/--
A `factor` result value: `[scalar, [[coeffs, multiplicity], ...]]`.

The scalar is the signed content (`sign(lc(f)) * content(f)`, or `0` for
zero input).  Polynomial factors are emitted separately from the scalar, with
explicit multiplicity buckets; factor order is not part of the public
contract.
-/
private def factorValue (φ : Factorization) : String :=
  "[" ++ toString φ.scalar ++ "," ++
    factorEntriesValue (φ.factors.toList.map (fun entry => (liftCoeffs entry.1, entry.2))) ++ "]"

/-- Expected `Factorization` JSON in the same shape as `factorValue`. -/
private def expectedFactorValue (scalar : Int) (factors : List (List Int × Nat)) : String :=
  "[" ++ toString scalar ++ "," ++ factorEntriesValue factors ++ "]"

/-- Emit the size-ordered classical tier's result (`factorClassical`) for cross
checking against FLINT. Emits `null` when the tier declines (no admissible prime
or subset budget exceeded), which the oracle treats as a skip. -/
private def emitClassicalResult (case : String) (f : ZPoly) : IO Unit :=
  match factorClassical f with
  | some φ => emitResult lib case "classicalFactor" (factorValue φ)
  | none => emitResult lib case "classicalFactor" "null"

/-- Emit one fixture record plus the `factor` and `classicalFactor` result records. -/
private def emitFactorCase (case : String) (f : ZPoly) : IO Unit := do
  emitPolyFixture lib case (liftCoeffs f) none
  emitResult lib case "factor" (factorValue (factor f))
  emitClassicalResult case f

/-- One fixture whose result is emitted by running the public Lean `factor`. -/
private structure Case where
  id     : String
  coeffs : Array Int

private def mk (id : String) (coeffs : Array Int) : Case :=
  { id, coeffs }

/-- One fixture with a hand-pinned expected `Factorization` JSON value. -/
private structure ExpectedCase where
  id      : String
  coeffs  : Array Int
  /-- Signed scalar field of the expected `Factorization`. -/
  scalar  : Int
  /-- Primitive polynomial factors, by ascending coefficients and multiplicity. -/
  factors : List (List Int × Nat)

private def mkExpected (id : String) (coeffs : Array Int)
    (scalar : Int) (factors : List (List Int × Nat)) : ExpectedCase :=
  { id, coeffs, scalar, factors }

private def linear (r : Int) : ZPoly :=
  DensePoly.ofCoeffs #[-r, 1]

private def positiveRoots (n : Nat) : List Int :=
  (List.range n).map fun i => Int.ofNat (i + 1)

private def splitProductCoeffs (n : Nat) : Array Int :=
  liftCoeffs (Array.polyProduct ((positiveRoots n).map linear).toArray) |>.toArray

private def splitProductExpectedFactors (n : Nat) : List (List Int × Nat) :=
  (positiveRoots n).map fun r => ([-r, 1], 1)

/-- One fixture whose modular split metadata is checked by the FLINT oracle. -/
private structure PinnedCase where
  id      : String
  coeffs  : Array Int
  /-- Prime used only for the pinned modular-factor sanity check. -/
  p       : Int
  /-- Sorted degrees of the irreducible factors of the input reduced mod `p`. -/
  degrees : List Int

private def mkPinned (id : String) (coeffs : Array Int)
    (p : Int) (degrees : List Int) : PinnedCase :=
  { id, coeffs, p, degrees }

/--
One pinned modular-split fixture with a hand-pinned expected
`Factorization` JSON value.
-/
private structure PinnedExpectedCase where
  id      : String
  coeffs  : Array Int
  p       : Int
  degrees : List Int
  /-- Signed scalar field of the expected `Factorization`. -/
  scalar  : Int
  /-- Primitive polynomial factors, by ascending coefficients and multiplicity. -/
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
  , mk "irr/cyclo7"  #[1, 1, 1, 1, 1, 1, 1] ]

private def cases_irr_expected : List ExpectedCase :=
  [ -- Φ_11(x), degree 10, irreducible.
    mkExpected "irr/cyclo11"
      #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
      1
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1)]
    -- Φ_17(x), degree 16, irreducible.
  , mkExpected "irr/cyclo17"
      #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
      1
      [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1)] ]

/-! ## Reducible products of two or three irreducibles

These polynomials all factor over `Z` into two or three irreducibles
and are oracle-checked against committed expected `Factorization` data. -/

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

/-! ## HO-2 adversarial cases with pinned modular split metadata

These cases discharge `SPEC/Libraries/hex-berlekamp-zassenhaus.md`
§"Conformance fixtures" (HO-2, #2565); see the module docstring above
for the case-by-case role.  Each case is emitted with
`modFactorPrime` / `modFactorDegrees`, which the python-flint oracle
cross-checks via `nmod_poly.factor`.  Conformance buckets for the same
polynomials live in `HexBerlekampZassenhaus/Conformance.lean` under
"Adversarial modular split cases"; case-id stems
(`quad_sqrt2_sqrt3`, `x4_plus_1`, `swinnerton_dyer_sd3`, `phi15`) match
the local Lean polynomial names there. -/

private def cases_pinned_factor : List PinnedCase :=
  [ -- adv/quad_sqrt2_sqrt3 — (X^2 - 2)(X^2 - 3) splits over F_23 into
    -- four linear factors that the integer factorisation recombines
    -- into two quadratics.  Discharges the HO-2 non-trivial
    -- subset-product requirement.
    mkPinned "adv/quad_sqrt2_sqrt3" #[6, 0, -5, 0, 1] 23 [1, 1, 1, 1] ]

private def cases_pinned_expected : List PinnedExpectedCase :=
  [ -- adv/x4_plus_1 — X^4 + 1 is irreducible over Z and splits over F_5
    -- into two quadratics; HO-2 subset-product case at a small
    -- admissible prime.
    mkPinnedExpected "adv/x4_plus_1" #[1, 0, 0, 0, 1] 5 [2, 2]
      1 [([1, 0, 0, 0, 1], 1)]
    -- adv/swinnerton_dyer_sd3 — Swinnerton-Dyer SD_3 (degree 8, root
    -- field Q(√2, √3, √5)) is irreducible over Z and splits completely
    -- over F_71 as eight linear factors; HO-2 heavy-split case.
  , mkPinnedExpected "adv/swinnerton_dyer_sd3"
      #[576, 0, -960, 0, 352, 0, -40, 0, 1]
      71 [1, 1, 1, 1, 1, 1, 1, 1]
      1 [([576, 0, -960, 0, 352, 0, -40, 0, 1], 1)]
    -- adv/phi15 — Φ_15 (degree 8) is irreducible over Z and splits
    -- completely over F_31 as eight linear factors; HO-2 heavy-split
    -- case at a small admissible prime.
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

/-! ## Good-prime regression cases

These split products exercise the path where the raw executable gcd can return
a non-monic unit for square-free modular images.  Results are pinned rather
than emitted through `factor` so the oracle catches any reducible Hex output. -/

private def cases_good_prime_regression : List ExpectedCase :=
  [ mkExpected "regression/split_roots_1_11" (splitProductCoeffs 11)
      1 (splitProductExpectedFactors 11)
  , mkExpected "regression/split_roots_1_24" (splitProductCoeffs 24)
      1 (splitProductExpectedFactors 24)
  , mkExpected "regression/split_roots_1_72" (splitProductCoeffs 72)
      1 (splitProductExpectedFactors 72) ]

private def emitCase (c : Case) : IO Unit :=
  emitFactorCase c.id (DensePoly.ofCoeffs c.coeffs)

private def emitExpectedCase (c : ExpectedCase) : IO Unit := do
  emitPolyFixture lib c.id c.coeffs.toList none
  emitResult lib c.id "factor" (expectedFactorValue c.scalar c.factors)
  emitClassicalResult c.id (DensePoly.ofCoeffs c.coeffs)

private def emitPinnedCase (c : PinnedCase) : IO Unit := do
  let f := DensePoly.ofCoeffs c.coeffs
  emitPolyFixtureWithModFactorDegrees lib c.id (liftCoeffs f) c.p c.degrees
  emitResult lib c.id "factor" (factorValue (factor f))
  emitClassicalResult c.id f

private def emitPinnedExpectedCase (c : PinnedExpectedCase) : IO Unit := do
  let f := DensePoly.ofCoeffs c.coeffs
  emitPolyFixtureWithModFactorDegrees lib c.id (liftCoeffs f) c.p c.degrees
  emitResult lib c.id "factor" (expectedFactorValue c.scalar c.factors)
  emitClassicalResult c.id f

end Hex.BZEmit

def main : IO Unit := do
  for c in Hex.BZEmit.cases_edge    do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_irr     do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_irr_expected do Hex.BZEmit.emitExpectedCase c
  for c in Hex.BZEmit.cases_red     do Hex.BZEmit.emitExpectedCase c
  for c in Hex.BZEmit.cases_pinned_factor do Hex.BZEmit.emitPinnedCase c
  for c in Hex.BZEmit.cases_pinned_expected do Hex.BZEmit.emitPinnedExpectedCase c
  for c in Hex.BZEmit.cases_content do Hex.BZEmit.emitExpectedCase c
  for c in Hex.BZEmit.cases_good_prime_regression do Hex.BZEmit.emitExpectedCase c
