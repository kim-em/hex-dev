/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries
public meta import HexTruncatedSeries.Defs
public meta import HexTruncatedSeries.Ring
public meta import HexTruncatedSeries.Classes
public meta import HexTruncatedSeries.Precision
public meta import HexTruncatedSeries.Newton
public meta import HexTruncatedSeries.Inverse
public meta import HexTruncatedSeries.Sqrt
public meta import HexTruncatedSeries.ExpLog
public meta import HexTruncatedSeries.Comp
public meta import HexTruncatedSeries.Revert

public section

/-!
# Truncated-series core conformance

Oracle: SymPy `sympy.polys.ring_series` (CI mode, fixture wiring follows in the
emitter).  This always-run core module checks the executable ring and precision
operations, Newton inverse and square root, exponential and logarithm,
Horner/Brent--Kung composition, and Newton/Lagrange reversion.

Properties covered here include bounded/full multiplication agreement,
inverse multiplication on a geometric series, the two supplied square-root
branches, `log (exp a) = a`, agreement of both composition routes, and
agreement of both reversion routes.  Edge cases cover precisions zero and one,
nonunit integer constants and linear coefficients, a wrong supplied square
root, division by an oversized power of `x`, and the documented failure of
zero extension to preserve multiplication.
-/

namespace HexTruncatedSeries.Conformance

open Hex Hex.TSeries
open scoped Hex

private def coeffList (a : TSeries R n) : List R :=
  a.coeffs.toArray.toList

private def geometric (n : Nat) : TSeries Int n := ofFn fun _ => 1

private def oneMinusX (n : Nat) : TSeries Int n :=
  ofFn fun i => if i = 0 then 1 else if i = 1 then -1 else 0

private def xPlusSq (R : Type) [Lean.Grind.CommRing R] (n : Nat) : TSeries R n :=
  ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0

/-! Ring and precision operations: typical, precision-zero, and bounded cases. -/

#guard coeffList ((ofFn fun i => i + 1 : TSeries Int 4) *
    (ofFn fun i => if i < 2 then i + 2 else 0 : TSeries Int 4)) = [2, 7, 12, 17]
#guard coeffList (0 : TSeries Int 0) = []
#guard coeffList (mulUpTo 2 (geometric 4) (geometric 4)) = [1, 2, 0, 0]
#guard coeffList ((ofFn fun i => i + 1 : TSeries Int 4).pow 3) = [1, 6, 21, 56]

#guard coeffList ((ofFn fun i => i + 1 : TSeries Int 4).truncate 2 (by omega)) = [1, 2]
#guard coeffList ((ofFn fun i => i + 1 : TSeries Int 2).extend 4 (by omega)) = [1, 2, 0, 0]
#guard coeffList ((ofFn fun i => i + 1 : TSeries Int 4).mulXPow 2) = [0, 0, 1, 2]
#guard (divXPow? (ofFn fun i => if i = 2 then 3 else if i = 3 then 4 else 0 :
    TSeries Int 4) 2).map coeffList = some [3, 4]
#guard divXPow? (ofFn fun i => i + 1 : TSeries Int 3) 5 = none
#guard (divXPow? (0 : TSeries Int 3) 5).map coeffList = some []
#guard valuation? (ofFn fun i => if i = 3 then 7 else 0 : TSeries Int 5) = some 3
#guard valuation? (0 : TSeries Int 0) = none
#guard coeffList (deriv (ofFn fun i => i + 1 : TSeries Int 4)) = [2, 6, 12]
#guard coeffList (integrate (ofFn fun _ => 3 : TSeries Int 1)) = [0, 3]

/-! Inversion and its precision-zero/nonunit behavior. -/

#guard coeffList (invOfUnit (oneMinusX 8) 1) = [1, 1, 1, 1, 1, 1, 1, 1]
#guard coeffList (oneMinusX 8 * invOfUnit (oneMinusX 8) 1) =
  coeffList (1 : TSeries Int 8)
#guard (inv? (ofFn fun i => if i = 0 then 2 else 1 : TSeries Int 0)).map coeffList =
  some []
#guard inv? (ofFn fun i => if i = 0 then 2 else 1 : TSeries Int 1) = none
#guard inv? (ofFn fun i => if i = 0 then 2 else 1 : TSeries Int 4) = none

/-! Square roots with both branches and both halves of the failure condition. -/

private def onePlusXRat (n : Nat) : TSeries Rat n :=
  ofFn fun i => if i = 0 ∨ i = 1 then 1 else 0

#guard coeffList (sqrtOfRoot (onePlusXRat 5) 1 (1 / 2)) =
  [1, 1 / 2, -1 / 8, 1 / 16, -5 / 128]
#guard coeffList (sqrtOfRoot (onePlusXRat 5) (-1) (-1 / 2)) =
  [-1, -1 / 2, 1 / 8, -1 / 16, 5 / 128]
#guard (sqrt? (ofFn fun i => if i = 0 then 4 else 1 : TSeries Int 0) 2).map coeffList =
  some []
#guard (sqrt? (ofFn fun i => if i = 0 then 4 else 1 : TSeries Int 1) 2).map coeffList =
  some [2]
#guard sqrt? (ofFn fun i => if i = 0 then 4 else 1 : TSeries Int 2) 2 = none
#guard sqrt? (onePlusXRat 4) 2 = none

/-! Exponential and logarithm. -/

private def xRat (n : Nat) : TSeries Rat n :=
  ofFn fun i => if i = 1 then 1 else 0

#guard coeffList (exp (xRat 6)) = [1, 1, 1 / 2, 1 / 6, 1 / 24, 1 / 120]
#guard coeffList (log (onePlusXRat 6)) = [0, 1, -1 / 2, 1 / 3, -1 / 4, 1 / 5]
#guard log (exp (xRat 6)) = xRat 6
#guard exp (xRat 6 + xRat 6) = exp (xRat 6) * exp (xRat 6)
#guard coeffList (exp (0 : TSeries Int 0)) = []
#guard coeffList (exp (0 : TSeries Int 1)) = [1]
#guard coeffList (log (1 : TSeries Int 1)) = [0]

/-! Composition routes and the nonzero-constant rejection. -/

private def compOuter : TSeries Int 4 := ofFn fun i => i + 1
private def compInner : TSeries Int 4 :=
  ofFn fun i => if i = 1 ∨ i = 2 then 1 else 0

#guard coeffList (comp compOuter compInner) = [1, 2, 5, 10]
#guard comp compOuter compInner = compHorner compOuter compInner
#guard comp? compOuter (C 1 : TSeries Int 4) = none
#guard (comp? (0 : TSeries Int 0) (C 1)).map coeffList = some []

/-! Newton reversion, direct Lagrange reversion, and degenerate branches. -/

#guard coeffList (revOfUnit (xPlusSq Int 6) 1) = [0, 1, -1, 2, -5, 14]
#guard coeffList (revOfUnit (xPlusSq Rat 6) 1) = [0, 1, -1, 2, -5, 14]
#guard revOfUnit (xPlusSq Rat 6) 1 = revLagrange (xPlusSq Rat 6) 1
#guard (rev? (xPlusSq Int 0)).map coeffList = some []
#guard (rev? (xPlusSq Int 1)).map coeffList = some [0]
#guard rev? (C 1 : TSeries Int 1) = none
#guard rev? (ofFn fun i => if i = 1 then 2 else if i = 2 then 1 else 0 :
    TSeries Int 4) = none

/-! Zero extension is intentionally not multiplicative. -/

private def x2 : TSeries Int 2 := X
#guard coeffList ((x2 * x2).extend 3 (by omega)) = [0, 0, 0]
#guard coeffList (x2.extend 3 (by omega) * x2.extend 3 (by omega)) = [0, 0, 1]

end HexTruncatedSeries.Conformance
