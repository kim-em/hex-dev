/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexRealRoots

/-!
JSONL emit driver for the `hex-real-roots` oracle.

`lake exe hexrealroots_emit_fixtures` writes one `poly` fixture record
per input polynomial followed by `result` records carrying Lean's
computed answer for each operation.  The companion driver
`scripts/oracle/realroots_flint.py` reads the same stream and
re-derives the real roots through python-flint's `fmpz_poly`
(`complex_roots` for the certified isolating balls, `factor` for the
exact rational roots), never by re-running the Lean isolator.

Operations covered:

* `root_count`   — `Hex.rootCount p`, the total number of real roots,
  value an `Int`.
* `isolations`   — the isolating intervals from `Hex.isolate? p`,
  value a matrix of rows `[lo_num, lo_exp, hi_num, hi_exp]`.  Each
  dyadic endpoint is encoded as `[num, exp]` with value `num · 2^(−exp)`
  (`Dyadic.zero` as `[0, 0]`, `Dyadic.ofOdd n k _` as `[n, k]`).
* `isolate_none` — value `true` for the rejection cases (the zero
  polynomial and non-square-free inputs), where both engines decline.

**Descartes-engine cross-check (the deferred-theorem stand-in).**  Per
`SPEC/Libraries/hex-real-roots.md` §"Conformance fixtures", until the
companion proves `isolateDescartes?_isSome`, every fixture asserts that
the fast Descartes engine does not fall back and agrees with the Sturm
engine.  This driver computes *both* engines on every case and
`throw`s (exiting non-zero) on any disagreement: for a square-free case
both engines must return `some` with identical isolating intervals; for
a rejection case both must return `none`.

**ci tier.**  Thirty degree-15 polynomials with coefficients in
`[−9, 9]` drawn from the POSIX `rand` LCG
(`xₙ₊₁ = (1103515245·xₙ + 12345) mod 2^31`) folded into `[−9, 9]` by
`raw ↦ (raw mod 19) − 9`.  Candidate `i` takes coefficient `j` from the
`(i·16 + j + 1)`-th LCG state after the fixed seed.  A candidate is
accepted iff its degree-15 (leading) coefficient is nonzero *and* it is
`SquareFreeRat`; rejected candidates are skipped deterministically, and
the first thirty accepted candidates form the ci tier.  Only square-free
inputs receive isolation results, per the oracle-discipline rule that
non-square-free inputs are rejection cases.
-/

namespace Hex.RealRootsEmit

open Hex
open Hex.Conformance.Emit

private def lib : String := "HexRealRoots"

/-- Encode a dyadic endpoint as `[num, exp]` with value `num · 2^(−exp)`.
`Dyadic.zero` is `[0, 0]`; `Dyadic.ofOdd n k _` is `[n, k]`. -/
private def dyadicPair : Dyadic → List Int
  | .zero => [0, 0]
  | .ofOdd n k _ => [n, k]

/-- The isolating intervals of a completed run as JSON-friendly rows
`[lo_num, lo_exp, hi_num, hi_exp]`, one per isolation. -/
private def isoRows {p : ZPoly} (res : RealRootIsolations p) : List (List Int) :=
  res.isolations.toList.map fun iso =>
    dyadicPair iso.interval.lower ++ dyadicPair iso.interval.upper

private def dmax (a b : Dyadic) : Dyadic := if a < b then b else a
private def dmin (a b : Dyadic) : Dyadic := if a < b then a else b

/-- Two half-open dyadic intervals `(a₁, b₁]` and `(a₂, b₂]` overlap
iff `max a₁ a₂ < min b₁ b₂`.  Two isolations of the same real root
always overlap (both half-open intervals contain that root), so this is
the cross-engine agreement test: the Descartes and Sturm runs isolate
the same roots in the same order exactly when their `i`-th intervals
overlap. -/
private def overlaps (i₁ i₂ : DyadicInterval) : Bool :=
  decide (dmax i₁.lower i₂.lower < dmin i₁.upper i₂.upper)

/-- The Descartes and Sturm runs agree: same number of isolations (the
`complete` invariant guarantees both equal `rootCount p`), and the
`i`-th intervals overlap, so both pin the same root at each position. -/
private def enginesAgree {p : ZPoly} (dr sr : RealRootIsolations p) : Bool :=
  let di := dr.isolations.toList.map (·.interval)
  let si := sr.isolations.toList.map (·.interval)
  di.length == si.length && (di.zip si).all fun (a, b) => overlaps a b

/-- Emit one case.  When `squarefree`, both engines must return `some`
with identical intervals; the run is emitted from the Descartes engine's
output (which, for a square-free input, equals `isolate? p`).  Otherwise
both engines must return `none` and the case is a rejection.  Any
deviation `throw`s, exiting non-zero — the Descartes-engine stand-in for
the deferred termination theorem. -/
private def emitCase (id : String) (coeffs : List Int) (squarefree : Bool) : IO Unit := do
  emitPolyFixture lib id coeffs
  let p : ZPoly := DensePoly.ofCoeffs coeffs.toArray
  let d := isolateDescartes? p
  let s := isolateSturm? p
  if squarefree then
    match d, s with
    | some dr, some sr =>
      unless enginesAgree dr sr do
        throw <| IO.userError
          s!"{lib}/{id}: Descartes and Sturm engines isolate different roots"
      emitResult lib id "root_count" (toString (rootCount p))
      emitResult lib id "isolations" (intMatrixValue (isoRows dr))
    | _, _ =>
      throw <| IO.userError
        s!"{lib}/{id}: engine fallback (descartes.isSome={d.isSome}, sturm.isSome={s.isSome})"
  else
    match d, s with
    | none, none =>
      emitResult lib id "isolate_none" "true"
    | _, _ =>
      throw <| IO.userError
        s!"{lib}/{id}: expected both engines to reject (descartes.isSome={d.isSome}, sturm.isSome={s.isSome})"

/-! ## SPEC core fixtures. -/

/-- The square-free core cases: a coefficient list (ascending degree)
and a human-readable id. -/
private def coreSquareFree : List (String × List Int) := [
  ("core/linear/x-5",        [-5, 1]),           -- x − 5
  ("core/x2-1",              [-1, 0, 1]),        -- x² − 1  (roots ±1)
  ("core/x2+1",              [1, 0, 1]),         -- x² + 1  (no real roots)
  ("core/x3-x",              [0, -1, 0, 1]),     -- x³ − x  (roots −1, 0, 1)
  ("core/x3-x-1",            [-1, -1, 0, 1]),    -- x³ − x − 1  (one real root)
  ("core/dyadic/2x-1_x-2",   [2, -5, 2]),        -- (2x − 1)(x − 2), root 1/2 hit exactly
  ("core/adjacent/x_x-1",    [0, -1, 1]),        -- x(x − 1), adjacent isolations
  ("core/chebyshev/T5",      [0, 5, 0, -20, 0, 16]),  -- T₅, five roots in [−1, 1]
  ("core/cyclotomic/Phi5",   [1, 1, 1, 1, 1])    -- Φ₅, no real roots
]

/-- The rejection cases: the zero polynomial and a non-square-free
input; both engines decline. -/
private def coreRejection : List (String × List Int) := [
  ("core/zero",              []),                -- the zero polynomial
  ("core/nonsquarefree/x-1_sq_x+1", [1, -1, -1, 1])  -- (x − 1)²(x + 1)
]

/-! ## ci tier: seeded degree-15 square-free polynomials. -/

/-- POSIX `rand` LCG step: `x ↦ (1103515245·x + 12345) mod 2^31`. -/
private def lcgStep (x : Nat) : Nat := (1103515245 * x + 12345) % 2147483648

/-- The `k`-th LCG state after `seed`. -/
private def lcgIterate (seed : Nat) : Nat → Nat
  | 0 => seed
  | k + 1 => lcgIterate (lcgStep seed) k

/-- Fold a 31-bit LCG output into a centred coefficient in `[−9, 9]`. -/
private def foldCoeff (raw : Nat) : Int := (Int.ofNat (raw % 19)) - 9

/-- The fixed seed for the ci tier (an arbitrary documented constant). -/
private def ciSeed : Nat := 20260711

/-- Coefficient list (ascending degree, length 16 ⇒ degree 15) of the
`i`-th LCG candidate. -/
private def candCoeffs (i : Nat) : List Int :=
  (List.range 16).map fun j => foldCoeff (lcgIterate ciSeed (i * 16 + j + 1))

/-- A candidate is admissible iff its leading (degree-15) coefficient is
nonzero and it is square-free over `ℚ`. -/
private def ciAcceptable (coeffs : List Int) : Bool :=
  (!(coeffs.getLast? == some (0 : Int))) &&
    decide (ZPoly.SquareFreeRat (DensePoly.ofCoeffs coeffs.toArray))

/-- The first thirty admissible candidates from the deterministic
candidate stream. -/
private def ciCases : List (List Int) :=
  ((List.range 300).map candCoeffs |>.filter ciAcceptable).take 30

end Hex.RealRootsEmit

open Hex.RealRootsEmit in
def main : IO Unit := do
  for (id, coeffs) in coreSquareFree do emitCase id coeffs true
  for (id, coeffs) in coreRejection do emitCase id coeffs false
  let cases := ciCases
  if cases.length ≠ 30 then
    throw <| IO.userError
      s!"ci tier: only {cases.length} admissible degree-15 candidates found (need 30); widen the pool"
  let mut idx := 0
  for coeffs in cases do
    let n := toString idx
    let padded := if idx < 10 then "0" ++ n else n
    emitCase s!"ci/d15/{padded}" coeffs true
    idx := idx + 1
