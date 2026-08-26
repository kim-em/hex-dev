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

Oracle: SymPy `sympy.polys.ring_series`, via
`scripts/oracle/series_sympy.py` on the stream from
`lake exe hextruncatedseries_emit_fixtures`.

Mode: `if_available` locally, required in release CI.

Covered operations:

- representation: `coeff`, `ofFn`, `C`, and `X`;
- ring operations: zero, one, addition, negation, subtraction,
  multiplication, `pow`, and `mulUpTo`;
- precision operations: `truncate`, `extend`, `mulXPow`, `allZeroBelow`,
  `divXPow?`, `valuation?`, `deriv`, `derivPad`, and `integrate`;
- Newton infrastructure: `steps` and `newton`;
- inverse and square root: `invUpTo`, `invOfUnit`, `inv?`, `sqrtUpTo`,
  `sqrtOfRoot`, and `sqrt?`;
- exponential and logarithm: `expUpTo`, `exp`, `logUpTo`, and `log`;
- composition: the bounded and full Horner, Brent--Kung, selected-route, and
  checked operations; and
- reversion: `revUpTo`, `revOfUnit`, `rev?`, and `revLagrange`.

Covered properties:

- coefficient formulas and the truncated commutative-ring laws;
- full/bounded multiplication and precision round trips;
- derivative/integral cancellation and padded derivative agreement;
- the Newton step-count bound;
- inverse multiplication and supplied-root square correctness;
- `log (exp a) = a`, `exp (log a) = a`, and exponential addition;
- Horner/Brent--Kung agreement and checked-composition agreement; and
- Newton/Lagrange reversion agreement and both composition identities.

Covered edge cases:

- every operation is run at precisions zero and one as well as a nontrivial
  precision;
- integer nonunits in constant and linear positions;
- an incorrect supplied square root;
- division by a power larger than the precision and division with a nonzero
  discarded prefix;
- composition with a nonzero inner constant; and
- the documented failure of zero extension to preserve multiplication.
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

/-! Three-case campaigns. Each family is evaluated at precision zero, at the
first boundary precision, and at a larger input carrying alternating or
failure-sensitive coefficients. The spot checks below retain independently
derived small expected values for review. -/

private def ringCase (n : Nat) : Bool :=
  let a : TSeries Int n :=
    ofFn fun i => if i % 2 = 0 then Int.ofNat (i + 1) else -Int.ofNat (i + 1)
  let b : TSeries Int n := ofFn fun i => if i = 0 then 2 else Int.ofNat i - 3
  let coeffOk := (List.range n).all fun i =>
    decide (a.coeff i =
      if i % 2 = 0 then Int.ofNat (i + 1) else -Int.ofNat (i + 1))
  let constOk := (List.range n).all fun i =>
    decide ((C 7 : TSeries Int n).coeff i = if i = 0 then 7 else 0)
  let xOk := (List.range n).all fun i =>
    decide ((X : TSeries Int n).coeff i = if i = 1 then 1 else 0)
  coeffOk && constOk && xOk &&
    decide (a.coeff n = 0) &&
    decide (a + 0 = a ∧ 0 + a = a) &&
    decide (a + b = b + a ∧ a + (-a) = 0) &&
    decide (a - b = a + (-b)) &&
    decide (a * b = b * a ∧ a * 1 = a) &&
    decide (a.pow 3 = (a * a) * a) &&
    decide (mulUpTo n a b = a * b)

#guard ringCase 0
#guard ringCase 1
#guard ringCase 11

private def precisionCase (n : Nat) : Bool :=
  let a : TSeries Rat n :=
    ofFn fun i => if i = 0 then 3 else if i % 2 = 0 then i else -i
  let widened := a.extend (n + 2) (by omega)
  let shifted := a.mulXPow 1
  let divided := (divXPow? shifted 1).map coeffList
  let expected := (a.truncate (n - 1) (Nat.sub_le n 1)).coeffs.toArray.toList
  decide (widened.truncate n (by omega) = a) &&
    decide (a.truncate n (Nat.le_refl n) = a) &&
    decide (a.mulXPow 0 = a) &&
    decide (divided = some expected) &&
    decide (valuation? a = if n = 0 then none else some 0) &&
    allZeroBelow (0 : TSeries Rat n) n &&
    decide (a.deriv.extend n (Nat.sub_le n 1) = a.derivPad) &&
    decide ((integrate a).deriv = a)

#guard precisionCase 0
#guard precisionCase 1
#guard precisionCase 9

private def newtonCase (n : Nat) : Bool :=
  let k := steps n
  let got : TSeries Int 1 :=
    newton (fun _ m => C (Int.ofNat m)) (C 1) k
  let expected : TSeries Int 1 :=
    if k = 0 then C 1 else C (Int.ofNat (2 ^ k))
  decide (got = expected) && decide (n ≤ 2 ^ k)

#guard newtonCase 0
#guard newtonCase 1
#guard newtonCase 37

private def inverseCase (n : Nat) : Bool :=
  let a : TSeries Rat n := ofFn fun i => if i = 0 then 1 else if i = 1 then -1 else 0
  let inverse := invOfUnit a 1
  decide (a * inverse = 1) &&
    decide (invUpTo n a 1 = inverse) &&
    decide (inv? a = some inverse)

#guard inverseCase 0
#guard inverseCase 1
#guard inverseCase 12

private def sqrtCase (n : Nat) : Bool :=
  let a : TSeries Rat n := ofFn fun i => if i = 0 ∨ i = 1 then 1 else 0
  let root := sqrtOfRoot a 1 (1 / 2)
  decide (root * root = a) &&
    decide (sqrtUpTo n a 1 (1 / 2) = root) &&
    decide (sqrt? a 1 = some root)

#guard sqrtCase 0
#guard sqrtCase 1
#guard sqrtCase 10

private def expLogCase (n : Nat) : Bool :=
  let x : TSeries Rat n := ofFn fun i => if i = 1 then 1 else 0
  let onePlusX := 1 + x
  decide (expUpTo n x = exp x) &&
    decide (logUpTo n onePlusX = log onePlusX) &&
    decide (log (exp x) = x) &&
    decide (exp (log onePlusX) = onePlusX) &&
    decide (exp (x + x) = exp x * exp x)

#guard expLogCase 0
#guard expLogCase 1
#guard expLogCase 12

private def compCase (n : Nat) : Bool :=
  let outer : TSeries Int n := ofFn fun i => if i % 2 = 0 then i + 1 else -(i + 1)
  let inner : TSeries Int n := xPlusSq Int n
  let horner := compHorner outer inner
  let brentKung := compBrentKung outer inner
  let selected := comp outer inner
  decide (compBrentKungUpTo n outer inner = brentKung) &&
    decide (horner = brentKung) &&
    decide (compUpTo n outer inner = selected) &&
    decide (comp? outer inner = some selected)

#guard compCase 0
#guard compCase 1
#guard compCase 12

private def revertCase (n : Nat) : Bool :=
  let b : TSeries Rat n := xPlusSq Rat n
  let reverted := revOfUnit b 1
  decide (revUpTo n b 1 = reverted) &&
    decide (revLagrange b 1 = reverted) &&
    decide (rev? b = some reverted) &&
    decide (comp b reverted = X) &&
    decide (comp reverted b = X)

#guard revertCase 0
#guard revertCase 1
#guard revertCase 10

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

private def expLogLaws (n : Nat) : Bool :=
  decide (log (exp (xRat n)) = xRat n ∧
    exp (xRat n + xRat n) = exp (xRat n) * exp (xRat n))

#guard expLogLaws 1
#guard expLogLaws 2
#guard expLogLaws 3
#guard expLogLaws 4
#guard expLogLaws 5
#guard expLogLaws 6
#guard expLogLaws 7
#guard expLogLaws 8
#guard expLogLaws 9
#guard expLogLaws 10
#guard expLogLaws 11
#guard expLogLaws 12
#guard expLogLaws 13
#guard expLogLaws 14
#guard expLogLaws 15
#guard expLogLaws 16

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
