/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexBerlekampZassenhaus

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

Lattice-tier merge requirement
------------------------------

Two corpus cases can be answered **only by the lattice tier**, one per
lattice answer arm, so together they make both answer paths
merge-required through the public dispatcher:

* `adv/swinnerton_dyer_sd5_pair` — `SD₅(x)·SD₅(x+1)` (degree 64, the
  two true factors are the 32-blocks `SD₅(x)` and `SD₅(x+1)`) exercises
  the **split** arm: CLD recovery separates the two 32-blocks at modest
  precision.
* `adv/swinnerton_dyer_sd6` — SD₆ (degree 64, minimal polynomial of
  √2+√3+√5+√7+√11+√13, irreducible over ℤ) exercises the
  **irreducibility-certification** arm: recovery converges to the
  single all-ones class and the certificate-backed early stop (#8395)
  answers `some #[core]` without grinding to the `bhksBound` cap.

Swinnerton-Dyer blocks split into factors of degree ≤ 2 modulo every
admissible (squarefree-image) prime, so the lifted-factor count is
`r ≥ 32` no matter which prime the selector picks (at the selected
primes, 29 and 19, all blocks are quadratic and `r = 32`), and the
size-ordered classical search would need ΣC(31,≤15) ≈ 2³⁰ subset
candidates to reach its half-size frontier — for `sd5_pair` that is
where the two 16-block factors live, and for `sd6` that is what
exhausting all nontrivial subset products takes — far past its
level-aware budget (`levelAwareSubsetBudget 32 defaultSubsetBudget =
206368`), so it provably declines and the hybrid falls through to the
van Hoeij CLD lattice arm.  Both cases emit the
*hybrid* trace (`factorTraced`) rather than the classical one,
making the tier a merge requirement three ways: the emit helper itself
errors unless the lattice tier answered, the committed-fixture
byte-diff pins the exact trace (`tier = "lattice"`, `declined = true`,
the prime, `r = 32`, `subsetCandidates = 206368`), and the
`bz_trace_gate.py` baseline pins tier/decline and upper-bounds the
candidate count.  A dispatch change, a lattice regression, or a
precision-cap change that silently loses the tier fails the merge.
There is deliberately no `#guard` twin in `Conformance.lean` —
elaboration-time interpretation of the lattice run would cost minutes
of build time; the compiled emit executable covers it in seconds.

Cross-checked operation
-----------------------

* `factor` — `Hex.ZPoly.factorize` from `HexBerlekampZassenhaus` (the
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

/-- Serialise a `FactorTrace` to JSON for the performance gate. Deterministic
(no wall-clock), so it lives in the committed fixtures and is pinned by the gate
baseline. -/
private def traceValue (t : FactorTrace) : String :=
  "{\"tier\":\"" ++ t.tier ++ "\",\"prime\":" ++ toString t.prime ++
    ",\"r\":" ++ toString t.liftedFactorCount ++
    ",\"subsetCandidates\":" ++ toString t.subsetCandidates ++
    ",\"declined\":" ++ (if t.declined then "true" else "false") ++ "}"

/-- Emit the size-ordered classical tier's result (`factorClassical`) for cross
checking against FLINT, plus its diagnostic `trace` (tier, prime, `r`, subset
candidate count, declined) for the performance gate. The `classicalFactor` value
is `null` when the tier declines (no admissible prime or subset budget exceeded),
which the oracle treats as a skip. -/
private def emitClassicalResult (case : String) (f : ZPoly) : IO Unit := do
  let (result, trace) := factorClassicalTraced f
  match result with
  | some φ => emitResult lib case "classicalFactor" (factorValue φ)
  | none => emitResult lib case "classicalFactor" "null"
  emitResult lib case "trace" (traceValue trace)

/-- Emit one fixture record plus the `factor` and `classicalFactor` result records. -/
private def emitFactorCase (case : String) (f : ZPoly) : IO Unit := do
  emitPolyFixture lib case (liftCoeffs f) none
  emitResult lib case "factor" (factorValue (ZPoly.factorize f))
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

/-- Adversarial conformance corpus (per-PR; the heavy high-`r` cases SD4-SD6 and
`Φ_105` live in the scheduled fixture set). One representative per family; all
cross-checked against FLINT via both `factor` and `classicalFactor`. -/
private def cases_adversarial : List Case :=
  [ mk "adv/swinnerton_dyer_2" #[1, 0, -10, 0, 1]                          -- √2±√3, irreducible
  , mk "adv/swinnerton_dyer_3_shift1" #[-71, -744, 580, 664, -178, -184, -12, 8, 1]
  , mk "adv/cyclotomic_8" #[1, 0, 0, 0, 1]
  , mk "adv/cyclotomic_12" #[1, 0, -1, 0, 1]
  , mk "adv/cyclotomic_15" #[1, -1, 0, 1, -1, 1, 0, -1, 1]
  , mk "adv/x6_minus_1" #[-1, 0, 0, 0, 0, 0, 1]                            -- product of cyclotomics
  , mk "adv/x12_minus_1" #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  , mk "adv/large_height" #[3001500000, -2500500, -1501, 1]               -- roots far apart
  , mk "adv/high_multiplicity" #[9, -6, 28, -18, 30, -18, 12, -6, 1]      -- (x²+1)³(x-3)²
  , mk "adv/non_monic" #[-15, 1, 6]                                       -- (2x-3)(3x+5)
  , mk "adv/neg_content" #[8, -6, -2]                                     -- -2(x-1)(x+4)
  , mk "adv/reciprocal" #[1, 0, -7, 0, 1]                                 -- palindromic
  , mk "adv/identical_mod_profile" #[6, 0, -5, 0, 1]                      -- (x²-2)(x²-3)
  , mk "adv/eisenstein_5" #[-2, 0, 0, 0, 0, 1]                            -- x⁵-2
  , mk "adv/trinomial" #[1, 1, 0, 0, 1]                                   -- x⁴+x+1
  , mk "adv/planted_1" #[-6, -7, -5, 2, 0, 3, 0, 1]
  , mk "adv/planted_nonmonic" #[-5, -7, -12, -3, 1, 2]
  , mk "adv/bad_prime_retry" #[-180, 0, 156, 0, -35, 0, 1]               -- (x²-2)(x²-3)(x²-30)
  , mk "adv/large_plus_distractors" #[-6, 5, -1, 0, 0, 6, -5, 1]
  , mk "adv/mignotte_swell" #[1, 0, -10000, 0, 2, 0, 0, 0, 1] ]          -- (x⁴-100x+1)(x⁴+100x+1)

/-! ## Lattice-tier merge requirement

See the module docstring §"Lattice-tier merge requirement".  The cases are
emitted through the public `factor` path (`factorTraced`, whose `.1`
is `factor`) so the pinned trace catches dispatch regressions, not just
lattice ones. -/

/-- The two lattice-only cases, one per lattice answer arm:

* `adv/swinnerton_dyer_sd5_pair` (split arm) — `SD₅(x)·SD₅(x+1)`, the
  product of Swinnerton-Dyer SD₅ (the committed scheduled-corpus
  `adv/swinnerton_dyer_5` polynomial, minimal polynomial of
  √2+√3+√5+√7+√11) with its shift by one.  Degree 64, content 1, exactly
  two integer factors (the two 32-blocks).
* `adv/swinnerton_dyer_sd6` (certification arm) — Swinnerton-Dyer SD₆
  (the committed bench `sd6` polynomial from
  `bench/HexBench/LatticeSpike.lean`, minimal polynomial of
  √2+√3+√5+√7+√11+√13).  Degree 64, content 1, irreducible over ℤ. -/
private def cases_lattice : List PinnedCase :=
  [ mkPinned "adv/swinnerton_dyer_sd5_pair"
      #[11101827931906700692775396966400, -20149686329260169158205217177600,
        -401485862864015096914747179663360,
        542434245172328681950369347010560,
        5012420864790130900370848844087296,
        -3960296326489454660478287277457408,
        -28871495437215984552457055575736320,
        11815096040503473304118591431376896,
        90368762389881951552993316215717888,
        -13442597726530711239756206246461440,
        -169318168569256976670002306583887872,
        -5106043062269303041007476577140736,
        203790362268099712418642466877997056,
        31842327843847761548027667364708352,
        -166334963114402183779967280242491392,
        -41646299510886909758182690325004288,
        95874293133421566632128940101033984,
        31326757230671744837148463739961344,
        -40187520195658809490187600727801856,
        -15900390561260410792279551448449024,
        12498575684329014278226171313364992,
        5825581268692550371280448447840256,
        -2916887831323939096164149638410240,
        -1600596315332161707818522495549440,
        511272707272924709604596704746752,
        338023896633458155076239295324160,
        -66207908947743815016914836967936,
        -55807892326401711872028021776384, 5967370836164084103445688902528,
        7288775394478910547448726589440, -290278430652522926846805232064,
        -759046229065707375681704978432, -9985470465978726142566051647,
        63320575321577635160023538080, 3616672133248706617687751600,
        -4237357988791915834302206880, -406182697044518040602433480,
        226959069964451393388035360, 30132996847158857667661456,
        -9660637130776100972376608, -1659605660525774158311716,
        321903767632358798247712, 70559426385456543819184,
        -8139551415430337779488, -2350253717762252454136,
        144958892545273337504, 61530513414120188304, -1377982586328124832,
        -1260267322467469178, -10241566640720160, 19948369397622416,
        666700176676640, -238675624057208, -13436639601312, 2076738859824,
        166363635616, -12197577892, -1365630880, 39901712, 7273376, -10696,
        -22816, -400, 32, 1]
      29 (List.replicate 32 2)
  , mkPinned "adv/swinnerton_dyer_sd6"
      #[198828783273803025550632280753863681, 0,
        -8316202966928528723117528333532208416, 0,
        100392008259975194458539996111340080624, 0,
        -511762449216265420619809586571618679392, 0,
        1258829468814790188483900997578812102776, 0,
        -1771080720430629161685158978892152599456, 0,
        1585722240968892813653220405983168716752, 0,
        -968316307427310602872375357706532108000, 0,
        423140580409718469187953106123559340828, 0,
        -137048942135190916858196960829292680864, 0,
        33785494292069713784801456649105169648, 0,
        -6471399892949448329687739464771529952, 0,
        978878175154164215599705915851796296, 0,
        -118444912349891951852181962142375200, 0,
        11582497564629879101390954172990800, 0,
        -922739669127277027441017551584608, 0,
        60261059130667890854325275719238, 0, -3240853899326109989616514647392,
        0, 143976257181996292530653998416, 0, -5292590468585153795497272608,
        0, 161038437520893531719546696, 0, -4051269676739248306877664, 0,
        84041236543621002233072, 0, -1431186296399427673760, 0,
        19875965471079809820, 0, -223010452468129504, 0, 1995413247403984, 0,
        -13981172308896, 0, 74737287288, 0, -293134944, 0, 792048, 0, -1312,
        0, 1]
      19 (List.replicate 32 2) ]

-- Metamorphic relations (checked without an external oracle): factoring a
-- transformed input relates predictably to factoring the original.
private def metamorphicBase : ZPoly := DensePoly.ofCoeffs #[6, 0, -5, 0, 1]  -- (x²-2)(x²-3)

-- multiply-then-factor: a product of two irreducible quadratics yields two factors.
#guard ((factorClassical metamorphicBase).map (·.factors.size)) = some 2

-- negation: `factor (-f)` keeps the same polynomial factors and negates the scalar.
#guard
  match factorClassical metamorphicBase, factorClassical (DensePoly.scale (-1) metamorphicBase) with
  | some φ, some ψ => ψ.scalar == -φ.scalar && Factorization.product ψ == DensePoly.scale (-1) metamorphicBase
  | _, _ => false

-- content scaling: `factor (k·f)` keeps the factors and scales the scalar by `k`.
#guard
  match factorClassical metamorphicBase, factorClassical (DensePoly.scale 3 metamorphicBase) with
  | some φ, some ψ => ψ.scalar == 3 * φ.scalar && Factorization.product ψ == DensePoly.scale 3 metamorphicBase
  | _, _ => false

private def emitCase (c : Case) : IO Unit :=
  emitFactorCase c.id (DensePoly.ofCoeffs c.coeffs)

private def emitExpectedCase (c : ExpectedCase) : IO Unit := do
  emitPolyFixture lib c.id c.coeffs.toList none
  emitResult lib c.id "factor" (expectedFactorValue c.scalar c.factors)
  emitClassicalResult c.id (DensePoly.ofCoeffs c.coeffs)

private def emitPinnedCase (c : PinnedCase) : IO Unit := do
  let f := DensePoly.ofCoeffs c.coeffs
  emitPolyFixtureWithModFactorDegrees lib c.id (liftCoeffs f) c.p c.degrees
  emitResult lib c.id "factor" (factorValue (ZPoly.factorize f))
  emitClassicalResult c.id f

/-- Emit one lattice-sentinel fixture through the *hybrid* traced path: a
single `factorTraced` run supplies the `factor` result (its `.1` is the
public `factor`) **and** the trace, so the committed trace pins the tier
`factor` actually used.  The helper is sentinel-only: it errors out unless the
classical tier declined and the lattice tier answered, which is the case's
whole point — a case that stops routing to the lattice arm must not emit
quietly.  (The merge still fails either way: a tier change also breaks the
committed-fixture byte-diff and the `bz_trace_gate.py` baseline.)  Since the
lattice tier answered, the classical tier returned `none`, so
`classicalFactor` is `null` (an oracle skip) without paying the classical
decline burn a second time.  The exact `prime` / `r` / `subsetCandidates`
values are pinned by the committed-fixture byte-diff in
`scripts/ci/run_oracles.sh`; the trace-gate baseline additionally pins
tier/decline and upper-bounds `subsetCandidates`. -/
private def emitHybridTracedCase (c : PinnedCase) : IO Unit := do
  let f := DensePoly.ofCoeffs c.coeffs
  let (φ, trace) := factorTraced f
  unless trace.tier == "lattice" && trace.declined do
    throw <| IO.userError
      s!"emitHybridTracedCase {c.id}: expected the classical tier to decline and \
        the lattice tier to answer, got tier={trace.tier}, declined={trace.declined}"
  emitPolyFixtureWithModFactorDegrees lib c.id (liftCoeffs f) c.p c.degrees
  emitResult lib c.id "factor" (factorValue φ)
  emitResult lib c.id "classicalFactor" "null"
  emitResult lib c.id "trace" (traceValue trace)

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
  for c in Hex.BZEmit.cases_adversarial do Hex.BZEmit.emitCase c
  for c in Hex.BZEmit.cases_lattice do Hex.BZEmit.emitHybridTracedCase c
