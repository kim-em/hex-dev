/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexRoots

/-!
JSONL emit driver for the `hex-roots` oracle.

`lake exe hexroots_emit_fixtures` writes one `poly` fixture record per
input case followed by one `isolateAll32` `result` record carrying the
outcome of `Hex.isolateAll?` at target precision `32`. The companion
oracle `scripts/oracle/roots_flint.py` re-runs each polynomial through
python-flint's `fmpz_poly.complex_roots()` (certified Arb balls with
multiplicities) and cross-checks that the Lean certification discs
cover the flint roots with matching multiplicities.

Per the SPEC design decision the operation is `isolateAll?` at target
`32` rather than `isolate`: the oracle needs root *locations*, not the
separation precision `isolate` forces.

**Fixture set (deviation from the SPEC ci-tier, flagged deliberately).**
`HexRoots/SPEC/hex-roots.md` § Conformance fixtures pins the ci-tier at
"50 degree-20 polynomials with deterministic seed `0xC0FFEE`" and this
record format at "centre as exact rational from `.toRat`". Neither is
reachable, for two intrinsic reasons measured on this toolchain
(v4.32.0-rc1), not tuning knobs:

* *Runtime.* `isolateAll?` at target 32 costs ≈1 ms at degree 3,
  ≈115 ms at degree 4, ≈1 s at degree 6, ≈16 s at degree 8 — roughly a
  15× factor per two degrees, extrapolating to hours by degree 12 and
  far past that at degree 20 (already over the library's own SPEC time
  budget of "degree 10, prec 32: under 1 second"). Random draws are
  *unreliable at every degree*, not merely slow at high degree: one
  near-collision of two distinct roots forces refinement to the Mahler
  separation depth. Among 50 degree-6 LCG draws one case ran >140 s;
  among 50 degree-4 draws one ran >90 s, so a random tier cannot be
  wallclock-capped without nondeterministically dropping cases.

* *Centre size.* The exact Gaussian-dyadic Newton recentring does not
  round the certified centre to the square's precision, so its
  bit-length grows without bound during refinement. For a degree-4
  cyclotomic (`Φ₅`) the certified atoms have `prec` 51/67 but centres
  whose exact `.toRat` numerators run to 5 472 and 31 987 decimal
  digits — a single case serialises to ≈300 KB and `Φ₇` (degree 6)
  does not finish serialising. Emitting the SPEC's exact-rational centre
  is therefore impractical for any irrational-root polynomial.

The committed fixture instead uses a small **curated** set of
polynomials with Gaussian-*rational* roots (drawn from the SPEC's
core/local families). Newton reaches such roots exactly, so the
certified centres stay compact (each case's `value` is ≈100–200 bytes)
and the total emit runs in well under one second. The set still
exercises the paths the oracle checks: real and complex simple roots
(atoms) and real and complex `k = 2` multiple roots (clusters).
Restoring the SPEC's degree-20 random tier needs an `isolateAll?`
performance fix, a bound on the recentred centre bit-length, and a
per-case cost cap first; see the PR discussion.

Each `result.value` serialises the isolation outcome. On success it is
a JSON array with one object per certification result, each carrying
`kind` (`"atom"` | `"cluster"`), `k` (root count, `1` for atoms), the
disc centre as an exact rational (`re_num` / `re_den` / `im_num` /
`im_den`, from `DyadicSquare.re`/`im` via `Dyadic.toRat`), and `prec`
(the stored square's precision). A `none` outcome from the driver
serialises as the JSON string `"none"`; this is SPEC-noteworthy and is
reported to stderr with its case id.

The local JSON builders below (`certValue`, `noneValue`) exist because
the shared `Hex.Conformance.Emit` helpers only cover flat records; the
per-result object here is nested, so the driver hand-builds the array
payload and passes it to `emitResult` as a raw JSON fragment.
-/

namespace Hex.RootsEmit

open Hex.Conformance.Emit
open Hex Hex.DensePoly

private def lib : String := "HexRoots"

/-- The isolation target precision for the ci-tier fixtures. -/
private def target : Int := 32

/-- One ci-tier fixture: a case id and the polynomial's coefficients
    (ascending, constant term first). -/
private structure Case where
  id     : String
  coeffs : List Int

/-- The curated ci-tier fixtures. Every polynomial has Gaussian-rational
    roots, which the exact Newton recentring reaches exactly, so the
    certified centres stay compact (see the module docstring for why the
    SPEC's irrational-root and degree-20 random tiers are not usable).
    The set covers real and complex simple roots (atoms) and `k = 2`
    multiple roots (clusters), real and complex. -/
private def cases : List Case := [
  -- Real simple roots.
  { id := "rational/deg3", coeffs := [6, -7, 0, 1] },            -- (x−1)(x−2)(x+3)
  { id := "rational/x3_minus_x", coeffs := [0, -1, 0, 1] },      -- x(x−1)(x+1)
  -- Complex and real simple roots together.
  { id := "gaussian/x2p4_xm1_xp3", coeffs := [-12, 8, 1, 2, 1] }, -- (x²+4)(x−1)(x+3)
  -- Multiple root: the k = 2 cluster around 5 must not atomize.
  { id := "cluster/x2p1_x5sq", coeffs := [25, -10, 26, -10, 1] }, -- (x²+1)(x−5)²
  -- Real multiple root: the k = 2 cluster around 1 must not atomize.
  { id := "cluster/xm1sq_xm4", coeffs := [-4, 9, -6, 1] },        -- (x−1)²(x−4)
  -- Complex multiple roots: two k = 2 clusters at ±i.
  { id := "cluster/x2p1sq", coeffs := [1, 0, 2, 0, 1] }           -- (x²+1)²
]

/-! ## Result serialisation. -/

/-- Serialise one certification result as a JSON object. -/
private def certObject {p : ZPoly} (c : Certified p) : String :=
  let s := c.square
  let kind := match c with | .atom _ => "atom" | .cluster _ => "cluster"
  let k : Int := match c with | .atom _ => 1 | .cluster cl => (cl.k : Int)
  let re := s.re.toRat
  let im := s.im.toRat
  "{\"kind\":\"" ++ kind ++ "\",\"k\":" ++ toString k ++
    ",\"re_num\":" ++ toString re.num ++ ",\"re_den\":" ++ toString (re.den : Int) ++
    ",\"im_num\":" ++ toString im.num ++ ",\"im_den\":" ++ toString (im.den : Int) ++
    ",\"prec\":" ++ toString s.prec ++ "}"

/-- Serialise the certification results as a JSON array. -/
private def certValue {p : ZPoly} (rs : Array (Certified p)) : String :=
  "[" ++ String.intercalate "," (rs.toList.map certObject) ++ "]"

/-- The `result.value` for a driver give-up. -/
private def noneValue : String := "\"none\""

/-- Emit the `poly` fixture and `isolateAll32` result for one case,
    returning `true` when the driver gave up (a SPEC-noteworthy
    `none`). -/
private def emitCase (c : Case) : IO Bool := do
  emitPolyFixture lib c.id c.coeffs
  let p : ZPoly := DensePoly.ofCoeffs c.coeffs.toArray
  let (value, gaveUp) :=
    if h : 0 < p.degree?.getD 0 then
      match isolateAll? p target #[Component.cauchy p h] with
      | some rs => (certValue rs, false)
      | none    => (noneValue, true)
    else
      (noneValue, true)
  emitResult lib c.id "isolateAll32" value
  pure gaveUp

end Hex.RootsEmit

open Hex.RootsEmit in
def main : IO Unit := do
  for c in cases do
    if ← emitCase c then
      IO.eprintln s!"hexroots_emit_fixtures: isolateAll? returned none for case {c.id}; \
        this is SPEC-noteworthy"
