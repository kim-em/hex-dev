/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealRoots

/-!
Core conformance checks for `HexRealRoots`.

Oracle: core uses Lean-only checks (Sturm counts, exact dyadic evaluation, and
cross-engine agreement are their own algebraic oracle); the CI oracle profile
uses `python-flint` (`fmpz_poly` real-root isolation) via
`scripts/oracle/realroots_flint.py`, landing in the parallel oracle PR.
Mode: always for core, if_available for the `python-flint` oracle profile.

Covered operations:
- `Hex.ZPoly.evalDyadic`
- `Hex.dyadicSign`
- `Hex.signVar`
- `Hex.ZPoly.spem`
- `Hex.ZPoly.sturmChain`
- `Hex.sturmVarAt`, `Hex.sturmVarNegInf`, `Hex.sturmVarPosInf`
- `Hex.sturmCount`, `Hex.rootCount`
- `Hex.mobiusTransform`, `Hex.descartesVar`
- `Hex.twoPow`, `Hex.ceilLog2Nat`, `Hex.ceilLog2Dyadic`
- `Hex.rootBound`, `Hex.sepPrec`, `Hex.isolationDepth`
- `Hex.isolateSturm?`, `Hex.isolateDescartes?`, `Hex.isolate?`
- `Hex.RealRootIsolation.refine1`, `Hex.RealRootIsolation.refineTo`
- `Hex.RealRootIsolation.refined`
- `Hex.RefinedRealIsolation.sameRoot` (and the `Overlaps` decidability instance)
- `Hex.ZPoly.squareFreeCore` (the non-square-free fallback the drivers document)

Covered properties:
- `evalDyadic` is exact: the sign at a dyadic point matches the hand-computed
  value, hitting `0` exactly at a rational root.
- `signVar` skips zeros: the variation count of `(+, 0, −)` is `1`.
- `sturmCount` is additive across a split point:
  `count (a, c] = count (a, b] + count (b, c]`.
- `rootCount` equals the number of real roots and equals the isolation count of
  `isolate?` (completeness certificate).
- Every emitted isolation brackets a genuine sign change of `evalDyadic` (or a
  root exactly at the included upper endpoint), so a real root sits in each
  half-open interval.
- Emitted isolations are ordered and pairwise disjoint (`upperᵢ ≤ lowerᵢ₊₁`).
- The Descartes engine returns `some` and agrees with `isolate?` on the exact
  interval endpoints (the SPEC-mandated stand-in for `isolateDescartes?_isSome`,
  see the deletion note below).
- The Sturm engine returns `some` and agrees with `isolate?` on the isolation
  *count* (the intervals themselves need not coincide, and do not for
  `x³ − x − 1`).
- `mobiusTransform` produces the literal SPEC numerator on committed intervals,
  and `descartesVar` of it discards (`V = 0`) an interval with no roots.
- `spem` is the sign-managed pseudo-remainder (a positive multiple of the
  rational remainder), and `sturmChain` ends in a nonzero constant for a
  square-free positive-degree input.
- `refine1` halves the interval width and preserves the root; `refineTo`
  reaches the requested width; `refined` packages an isolation below separation
  precision; `sameRoot` identifies two isolations of the same root and
  separates isolations of distinct roots.
- The non-square-free input is rejected by both engines while its
  `squareFreeCore` isolates.

Covered edge cases:
- the zero polynomial (`isolate? = none`) and a nonzero constant
  (`isolate?` is `some` with an empty isolation array).
- a linear polynomial whose single root is captured by the whole initial
  interval without any bisection.
- a dyadic root that a bisection midpoint hits exactly (`2x² − 5x + 2`, and the
  midpoint-root refinement of `2x − 1`).
- adjacent isolations that share the endpoint `0` (`x² − x`).
- polynomials with no real roots (`x² + 1`, the cyclotomic `Φ₅`).
- roots clustering near `±1` (Chebyshev `T₅`).
- a non-square-free input rejected by both engines (`(x − 1)²(x + 1)`).
- a degree-8 fixture with eight integer roots (`∏_{k=1}^{8} (x − k)`).
-/

namespace Hex
namespace RealRootsConformance

open Hex.RealRootIsolation

/-! ### Dyadic literals used in the expected interval endpoints. -/

/-- The integer dyadic `n`. -/
private def di (n : Int) : Dyadic := Dyadic.ofInt n
/-- The dyadic `n / 2`. -/
private def half (n : Int) : Dyadic := (Dyadic.ofInt n) >>> (1 : Int)
/-- The dyadic `n / 4`. -/
private def quarter (n : Int) : Dyadic := (Dyadic.ofInt n) >>> (2 : Int)

/-! ### Committed fixtures.

Each polynomial is stored once, in ascending-degree coefficient order. The
factored form and real roots are named in the comment so the expectations below
are hand/oracle derivable, not read back off the engine. -/

/-- `x − 5`; single real root at `5`. -/
private def linear : ZPoly := DensePoly.ofCoeffs #[(-5 : Int), 1]
/-- `x² − 1`; real roots `±1`. -/
private def quadPair : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
/-- `x² + 1`; no real roots. -/
private def quadNone : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 0, 1]
/-- `x³ − x`; real roots `−1, 0, 1`. -/
private def cubicTriple : ZPoly := DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]
/-- `x³ − x − 1`; one real root near `1.3247`. -/
private def cubicSingle : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), -1, 0, 1]
/-- `(2x − 1)(x − 2) = 2x² − 5x + 2`; real roots `1/2` and `2` (the root `2` is
a bisection midpoint hit exactly). -/
private def dyadicMidpoint : ZPoly := DensePoly.ofCoeffs #[(2 : Int), -5, 2]
/-- `x(x − 1) = x² − x`; real roots `0` and `1`; the two isolations share the
endpoint `0`. -/
private def sharedEndpoint : ZPoly := DensePoly.ofCoeffs #[(0 : Int), -1, 1]
/-- Chebyshev `T₅ = 16x⁵ − 20x³ + 5x`; five real roots clustering in `[−1, 1]`. -/
private def chebyshev5 : ZPoly := DensePoly.ofCoeffs #[(0 : Int), 5, 0, -20, 0, 16]
/-- Cyclotomic `Φ₅ = x⁴ + x³ + x² + x + 1`; no real roots. -/
private def cyclotomic5 : ZPoly := DensePoly.ofCoeffs #[(1 : Int), 1, 1, 1, 1]
/-- `(x − 1)²(x + 1) = x³ − x² − x + 1`; not square-free. -/
private def nonSquareFree : ZPoly := DensePoly.ofCoeffs #[(1 : Int), -1, -1, 1]
/-- `∏_{k=1}^{8} (x − k)`; eight integer roots `1, …, 8`. The coefficients are
the signed elementary symmetric functions of `1, …, 8`. -/
private def deg8 : ZPoly :=
  DensePoly.ofCoeffs #[(40320 : Int), -109584, 118124, -67284, 22449, -4536, 546, -36, 1]
/-- The zero polynomial. -/
private def zeroPoly : ZPoly := DensePoly.ofCoeffs (#[] : Array Int)
/-- The nonzero constant `7`. -/
private def const7 : ZPoly := DensePoly.ofCoeffs #[(7 : Int)]
/-- `x² − 2`; irrational roots `±√2`, used for refinement. -/
private def quadIrr : ZPoly := DensePoly.ofCoeffs #[(-2 : Int), 0, 1]
/-- `2x − 1`; single dyadic root `1/2` at a bisection midpoint. -/
private def dyadicRoot : ZPoly := DensePoly.ofCoeffs #[(-1 : Int), 2]

/-! ### Projection and property helpers. -/

/-- The `(lower, upper]` endpoint pairs of an isolation run, so expectations are
`#guard`-comparable (`Dyadic` has `DecidableEq`). -/
private def endpoints {p : ZPoly} (o : Option (RealRootIsolations p)) :
    Option (Array (Dyadic × Dyadic)) :=
  o.map (fun rs => rs.isolations.map (fun iso => (iso.interval.lower, iso.interval.upper)))

/-- The number of emitted isolations. -/
private def isoCount {p : ZPoly} (o : Option (RealRootIsolations p)) : Option Nat :=
  o.map (·.isolations.size)

/-- A half-open interval `(a, b]` brackets a simple real root of `p` iff `p`
changes sign across it or has the root exactly at the included upper endpoint.
The intermediate-value witness that a real root sits in the interval, computed
by exact dyadic evaluation and independent of the counting engines. -/
private def brackets (p : ZPoly) (a b : Dyadic) : Bool :=
  (dyadicSign (p.evalDyadic b) == 0) ||
    (dyadicSign (p.evalDyadic a) * dyadicSign (p.evalDyadic b) < 0)

/-- Every emitted isolation brackets a genuine real root of `p`. Each isolation
is first refined tightly around its own root (`refined`), so the endpoint sign
test is not confused by a neighbouring root sitting on the excluded lower
endpoint of an unrefined interval (as happens for `x³ − x` and `x² − x`, whose
isolations share the endpoint `0`). Vacuously true for a root-free `p`. -/
private def allBracket {p : ZPoly} (o : Option (RealRootIsolations p)) : Bool :=
  match o with
  | none => false
  | some rs => rs.isolations.all fun iso =>
      match iso.refined with
      | some r => brackets p r.1.interval.lower r.1.interval.upper
      | none => false

/-- The endpoint pairs are ordered and pairwise disjoint: each upper endpoint is
at most the next lower endpoint. -/
private def sortedDisjoint (arr : Array (Dyadic × Dyadic)) : Bool :=
  (arr.toList.zip arr.toList.tail).all (fun (x, y) => decide (x.2 ≤ y.1))

/-- Refine two isolations to separation precision and compare them with
`sameRoot`, or `none` if either refinement fails. -/
private def sameRootOf {p : ZPoly} (i j : RealRootIsolation p) : Option Bool :=
  match i.refined, j.refined with
  | some a, some b => some (a.sameRoot b)
  | _, _ => none

/-- The refined interval of an isolation is at most `2^{−sepPrec p}` wide. -/
private def refinedWidthOk {p : ZPoly} (i : RealRootIsolation p) : Option Bool :=
  i.refined.map fun r =>
    decide (r.1.interval.upper - r.1.interval.lower ≤ twoPow (-(sepPrec p : Int)))

/-! ### Whole-run isolation, per fixture.

For each fixture: the exact interval endpoints of `isolate?` (a human-readable
regression pin, cross-checked against `python-flint` in the oracle PR); the
independent teeth that make the pin more than a determinism check — the emitted
count equals the mathematically known real-root count `rootCount`, every
interval brackets a real root, and the intervals are ordered and disjoint; the
mandated Descartes stand-in assertions; and the Sturm engine's count agreement.

**Descartes stand-in deletion note.** The `isolateDescartes?_isSome` /
`endpoints (isolateDescartes? p) = endpoints (isolate? p)` assertions below
stand in for the deferred companion theorem `isolateDescartes?_isSome`. The PR
that proves that theorem in `HexRealRootsMathlib` MUST delete these Descartes
assertions in the same change; from then the theorem carries the claim. -/

/-- Assert the shared per-fixture invariants, given the expected `isolate?`
endpoints and the known real-root count `n`. Bundled so each fixture is one
`#guard` block with no copy-pasted body. -/
private def isolatesAs (p : ZPoly) (expected : Array (Dyadic × Dyadic)) (n : Nat) : Bool :=
  -- `isolate?` yields the committed endpoints (oracle-verified in the oracle PR).
  (endpoints (isolate? p) == some expected) &&
  -- Completeness: one isolation per real root, matching the independent count.
  (isoCount (isolate? p) == some n) && (rootCount p == n) &&
  -- Each interval brackets a real root; the whole run is ordered and disjoint.
  allBracket (isolate? p) && ((endpoints (isolate? p)).elim false sortedDisjoint) &&
  -- Descartes stand-in: returns `some` and agrees with `isolate?` exactly.
  (isolateDescartes? p).isSome && (endpoints (isolateDescartes? p) == endpoints (isolate? p)) &&
  -- Sturm engine: returns `some` and agrees on the isolation count.
  (isolateSturm? p).isSome && (isoCount (isolateSturm? p) == some n)

#guard isolatesAs linear #[(di (-8), di 8)] 1
#guard isolatesAs quadPair #[(di (-4), di 0), (di 0, di 4)] 2
#guard isolatesAs quadNone #[] 0
#guard isolatesAs cubicTriple #[(di (-2), di (-1)), (di (-1), di 0), (di 0, di 4)] 3
#guard isolatesAs cubicSingle #[(di 0, di 4)] 1
#guard isolatesAs dyadicMidpoint #[(di 0, di 1), (di 1, di 2)] 2
#guard isolatesAs sharedEndpoint #[(di (-4), di 0), (di 0, di 4)] 2
#guard isolatesAs chebyshev5
  #[(di (-1), quarter (-3)), (quarter (-3), half (-1)), (half (-1), di 0),
    (half 1, quarter 3), (quarter 3, di 1)] 5
#guard isolatesAs cyclotomic5 #[] 0
#guard isolatesAs deg8
  #[(di 0, di 1), (di 1, di 2), (di 2, di 3), (di 3, di 4),
    (di 4, di 5), (di 5, di 6), (di 6, di 7), (di 7, di 8)] 8

-- The Sturm engine's intervals need NOT coincide with the Descartes engine's:
-- for `x³ − x − 1` the Sturm search emits the whole initial interval `(−4, 4]`
-- (the count is already `1`, so it never bisects) while the Descartes search
-- narrows to `(0, 4]`. Only the count is invariant across engines.
#guard endpoints (isolateSturm? cubicSingle) = some #[(di (-4), di 4)]
#guard endpoints (isolateDescartes? cubicSingle) = some #[(di 0, di 4)]

/-! ### Edge cases: zero, constant, non-square-free. -/

-- The zero polynomial is rejected by every engine.
#guard isolate? zeroPoly = none
#guard isolateSturm? zeroPoly = none
#guard isolateDescartes? zeroPoly = none

-- A nonzero constant isolates with zero roots (empty chain, `rootCount = 0`).
#guard (isolate? const7).isSome
#guard isoCount (isolate? const7) = some 0
#guard rootCount const7 = 0
#guard (isolateDescartes? const7).isSome
#guard (isolateSturm? const7).isSome

-- Non-square-free rejection: both engines and the driver decline, and the
-- square-free core (`x² − 1`, from `(x − 1)²(x + 1)`) isolates its two roots.
#guard isolate? nonSquareFree = none
#guard isolateSturm? nonSquareFree = none
#guard isolateDescartes? nonSquareFree = none
#guard (ZPoly.squareFreeCore nonSquareFree).toArray = #[(-1 : Int), 0, 1]
#guard isoCount (isolate? (ZPoly.squareFreeCore nonSquareFree)) = some 2
#guard allBracket (isolate? (ZPoly.squareFreeCore nonSquareFree))

/-! ### `evalDyadic`: exact Horner evaluation. -/

-- typical: `x² − 1` at `3/2` is `9/4 − 1 = 5/4`.
#guard ZPoly.evalDyadic quadPair (half 3) = quarter 5
-- edge: the zero polynomial evaluates to `0` everywhere.
#guard ZPoly.evalDyadic zeroPoly (di 5) = 0
-- adversarial: `x − 5` hits an exact `0` at its root `5`.
#guard ZPoly.evalDyadic linear (di 5) = 0

/-! ### `dyadicSign`: exact sign of a dyadic. -/

-- typical positive / negative, edge zero.
#guard dyadicSign (quarter 5) = 1
#guard dyadicSign (half (-3)) = -1
#guard dyadicSign (0 : Dyadic) = 0

/-! ### `signVar`: zero-skipping sign variations. -/

-- typical, the SPEC's `(+, 0, −)` zero-skip, an alternating adversarial list,
-- and the empty edge.
#guard signVar [1, -1] = 1
#guard signVar [1, 0, -1] = 1
#guard signVar [-1, 1, -1] = 2
#guard signVar [] = 0

/-! ### `spem`: sign-managed pseudo-remainder. -/

-- typical with a negative leading coefficient in `g`: `spem (x² + 1) (−2x + 1)`
-- is `4 · (5/4) = 5` (see `Chain.lean`).
#guard (ZPoly.spem quadNone (DensePoly.ofCoeffs #[(1 : Int), -2])).toArray = #[(5 : Int)]
-- edge: `spem f 0 = f` (the loop never starts).
#guard (ZPoly.spem quadNone zeroPoly).toArray = quadNone.toArray
-- adversarial: `g` a nonzero constant divides everything, so the remainder is `0`.
#guard (ZPoly.spem quadNone const7).toArray = (#[] : Array Int)

/-! ### `sturmChain`: the signed-remainder chain. -/

-- typical square-free quadratic: `[x² − 1, x, 1]`, ending in a nonzero constant.
#guard (ZPoly.sturmChain quadPair).map (·.toArray)
  = #[#[(-1 : Int), 0, 1], #[(0 : Int), 1], #[(1 : Int)]]
-- adversarial degree-3: `[x³ − x, 3x² − 1, x, 1]`.
#guard (ZPoly.sturmChain cubicTriple).map (·.toArray)
  = #[#[(0 : Int), -1, 0, 1], #[(-1 : Int), 0, 3], #[(0 : Int), 1], #[(1 : Int)]]
-- edge: a constant has the empty chain.
#guard (ZPoly.sturmChain const7).map (·.toArray) = (#[] : Array (Array Int))

/-! ### `sturmVarAt`, `sturmVarNegInf`, `sturmVarPosInf`. -/

-- `x² − 1` chain `[x²−1, x, 1]`: at `−2` signs `(+,−,+)` → 2, at `0` `(−,0,+)` → 1,
-- at `2` `(+,+,+)` → 0.
#guard sturmVarAt (ZPoly.sturmChain quadPair) (di (-2)) = 2
#guard sturmVarAt (ZPoly.sturmChain quadPair) (di 0) = 1
#guard sturmVarAt (ZPoly.sturmChain quadPair) (di 2) = 0
-- `±∞` counts read off leading coefficients and degree parities.
#guard sturmVarNegInf (ZPoly.sturmChain quadPair) = 2
#guard sturmVarPosInf (ZPoly.sturmChain quadPair) = 0
#guard sturmVarNegInf (ZPoly.sturmChain cubicTriple) = 3

/-! ### `sturmCount` and `rootCount`. -/

-- `x² − 1`: `(−4, 4]` counts both roots, `(0, 4]` only `1`, `(1, 2]` excludes
-- the left-endpoint root `1` (half-open) so `0`.
#guard sturmCount quadPair ⟨di (-4), di 4, by decide⟩ = 2
#guard sturmCount quadPair ⟨di 0, di 4, by decide⟩ = 1
#guard sturmCount quadPair ⟨di 1, di 2, by decide⟩ = 0
-- Additivity across the split point `0`.
#guard sturmCount quadPair ⟨di (-4), di 4, by decide⟩
  = sturmCount quadPair ⟨di (-4), di 0, by decide⟩ + sturmCount quadPair ⟨di 0, di 4, by decide⟩
-- `rootCount` on committed inputs (independently known real-root counts).
#guard rootCount quadPair = 2
#guard rootCount quadNone = 0
#guard rootCount cubicTriple = 3

/-! ### `mobiusTransform` and `descartesVar`. -/

-- `mobiusTransform` returns the literal SPEC numerator on committed intervals.
-- `x − 1` on `(0, 2]` is `x − 1`; `x² − 3` on `(1, 2]` is `x² − 2x − 2`;
-- `x − 1` on `(1, 3]` is `2x` (the boundary root at `a = 1` lands at `t = 0`).
#guard (mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 1]) ⟨di 0, di 2, by decide⟩).toArray
  = #[(-1 : Int), 1]
#guard (mobiusTransform (DensePoly.ofCoeffs #[(-3 : Int), 0, 1]) ⟨di 1, di 2, by decide⟩).toArray
  = #[(-2 : Int), -2, 1]
#guard (mobiusTransform (DensePoly.ofCoeffs #[(-1 : Int), 1]) ⟨di 1, di 3, by decide⟩).toArray
  = #[(0 : Int), 2]
-- `descartesVar` of a coefficient list (typical, no-root even count, linear).
#guard descartesVar (DensePoly.ofCoeffs #[(2 : Int), -3, 1]) = 2
#guard descartesVar (DensePoly.ofCoeffs #[(1 : Int), 0, 1]) = 0
#guard descartesVar (DensePoly.ofCoeffs #[(-1 : Int), 1]) = 1
-- The discard row of the Descartes engine: `x² + 1` on `(3, 4]`, far from `±i`,
-- has `V = 0` (no roots in the open interval).
#guard descartesVar (mobiusTransform quadNone ⟨di 3, di 4, by decide⟩) = 0

/-! ### `twoPow`, `ceilLog2Nat`, `ceilLog2Dyadic`. -/

#guard twoPow 0 = di 1
#guard twoPow 3 = di 8
#guard twoPow (-2) = quarter 1
#guard ceilLog2Nat 1 = 0
#guard ceilLog2Nat 3 = 2
#guard ceilLog2Nat 8 = 3
#guard ceilLog2Dyadic (di 1) = 0
#guard ceilLog2Dyadic (di 5) = 3
#guard ceilLog2Dyadic (quarter 1) = -2

/-! ### `rootBound`, `sepPrec`, `isolationDepth`. -/

-- `rootBound`: `x² − 3 → 2³ = 8`, `x − 1 → 2² = 4`, `2x + 1 → 2¹ = 2`.
#guard rootBound (DensePoly.ofCoeffs #[(-3 : Int), 0, 1]) = twoPow 3
#guard rootBound (DensePoly.ofCoeffs #[(-1 : Int), 1]) = twoPow 2
#guard rootBound (DensePoly.ofCoeffs #[(1 : Int), 2]) = twoPow 1
-- `sepPrec` is `0` below degree 2 (vacuous pairwise contract); positive above.
-- The degree-2 value `sepPrec (x² − 1) = 6` is the closed form
-- `((2+2)·1+1)/2 + (2−1)·ceilLog2Nat (ceilSqrt 2) + 3 = 2 + 1 + 3` with
-- `ceilLog2Nat (ceilSqrt 2) = ceilLog2Nat 2 = 1`.
#guard sepPrec const7 = 0
#guard sepPrec linear = 0
#guard sepPrec quadPair = 6
-- `isolationDepth` is the `depthSlack = 8` junk value below degree 1; positive
-- degree adds the separation and bound halvings (`x² − 1 → 17`).
#guard isolationDepth const7 = 8
#guard isolationDepth zeroPoly = 8
#guard isolationDepth quadPair = 17

/-! ### `refine1`, `refineTo`, `refined`, `sameRoot`.

Hand-built isolations (`count_one` by `decide`) exercise refinement and the root
identity, which the whole-run fixtures above do not reach directly. -/

/-- `√2 ∈ (1, 2]` for `x² − 2`. -/
private def isoSqrt2 : RealRootIsolation quadIrr := ⟨⟨di 1, di 2, by decide⟩, by decide⟩
/-- `1/2 ∈ (0, 1]` for `2x − 1`, a dyadic root at the bisection midpoint. -/
private def isoHalf : RealRootIsolation dyadicRoot := ⟨⟨di 0, di 1, by decide⟩, by decide⟩
/-- `−1 ∈ (−2, 0]` for `x² − 1`. -/
private def isoNeg1 : RealRootIsolation quadPair := ⟨⟨di (-2), di 0, by decide⟩, by decide⟩
/-- `1 ∈ (0, 2]` for `x² − 1`. -/
private def isoPos1 : RealRootIsolation quadPair := ⟨⟨di 0, di 2, by decide⟩, by decide⟩

-- `refine1` halves the width: `(1, 2] → (1, 3/2]` for `√2`.
#guard (refine1 isoSqrt2).interval.width = half 1
#guard (refine1 isoSqrt2).interval.lower = di 1
#guard (refine1 isoSqrt2).interval.upper = half 3
-- A dyadic root exactly at the midpoint lands in the left half (half-open):
-- `(0, 1] → (0, 1/2]` for `2x − 1`.
#guard (refine1 isoHalf).interval.lower = di 0
#guard (refine1 isoHalf).interval.upper = half 1
-- `refineTo` reaches the requested width `2^{−3} = 1/8` and still brackets `√2`.
#guard (refineTo isoSqrt2 3).interval.width ≤ twoPow (-3)
#guard brackets quadIrr (refineTo isoSqrt2 3).interval.lower (refineTo isoSqrt2 3).interval.upper
-- `refined` packages an isolation below separation precision.
#guard refinedWidthOk isoNeg1 = some true
#guard refinedWidthOk isoPos1 = some true
-- `sameRoot` identifies the same root and separates distinct roots. `refine1`
-- preserves the root, so a refined isolation and its refinement agree.
#guard sameRootOf isoNeg1 isoNeg1 = some true
#guard sameRootOf isoNeg1 isoPos1 = some false
#guard sameRootOf isoNeg1 (refine1 isoNeg1) = some true

end RealRootsConformance
end Hex
