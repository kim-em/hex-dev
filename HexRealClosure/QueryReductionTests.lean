/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.AlgebraicContext
public meta import HexRealClosure.AlgebraicContext

namespace Hex.RealClosure.Algebraic.QueryReductionTests

private def sample (scale cofactor : Rat) (odd : Bool := true) : Option (Array Bool) := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let head := DensePoly.scale scale
    ((x * x - DensePoly.C 2) * (x - DensePoly.C cofactor))
  let descriptor ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head, lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin descriptor (fun q => q.den == 1)
  let square := x * x
  let high := if odd then square * square * square * x else square * square * square
  let clean := scale == 1 && cofactor.den == 1
  let query := context.queryPoly high
  let stored := Element.ofPoly (context := context) high
  let multiple := head * square * square
  let unsigned := DensePoly.pseudoDiv high head
  return #[decide (query.natDegree < head.natDegree),
    decide (context.signPoly high = 1), decide (stored.sign = 1),
    decide (stored.polynomial.natDegree = if clean then 2 else if odd then 7 else 6),
    decide (context.queryPoly multiple = 0),
    decide ((Element.ofPoly (context := context) multiple) = 0),
    decide (context.queryPoly (DensePoly.C (-2)) = DensePoly.C (-2)),
    decide (context.signPoly (DensePoly.C (-2)) = -1),
    decide (context.queryPoly x = x),
    decide (context.signQuery unsigned.remainder = if scale < 0 && odd then -1 else 1),
    decide (context.canReduce = clean),
    !clean || decide (context.queryPoly stored.polynomial = stored.polynomial)]

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 3 3

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (-3) 3

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (1 / 2) 3

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 1 (1 / 2)

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (-3) 3 false

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 1 3

/-- Endpoint signs agree with the existing selected-sign producer, including
endpoint zeros, a crossing query and a canonical-zero defining equation. -/
private def endpointSample (scale : Rat) : Option (List (Option Int) × List Int × Bool) := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let head := DensePoly.scale scale (x * x - DensePoly.C 2)
  let descriptor ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head, lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin descriptor (fun q => q.den == 1)
  let queries := [x, -x, x - DensePoly.C 1, DensePoly.C 2 - x,
    x - DensePoly.C 2, DensePoly.C 1 - x, x - DensePoly.C (3 / 2), head]
  return (queries.map context.intervalSign?, queries.map context.signPoly,
    queries.all (fun p => context.signPoly p == context.signQuery (context.queryPoly p)))

#guard endpointSample 1 == some
  ([some 1, some (-1), some 1, some 1, some (-1), some (-1), none, none],
    [1, -1, 1, 1, -1, -1, -1, 0], true)
#guard endpointSample (-3) == some
  ([some 1, some (-1), some 1, some 1, some (-1), some (-1), none, none],
    [1, -1, 1, 1, -1, -1, -1, 0], true)

/-- A Thom-selected root in a two-root interval retains the BKR fallback. -/
private def manySample (chosen : Int) : Option (Bool × Int × Bool) := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let descriptor ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head := x * x - DensePoly.C 2,
      lower := .finite (-2), upper := .finite 2, indices := [1], signs := [chosen] }
  let context := Context.adjoin descriptor (fun q => q.den == 1)
  return ((context.singleSign? x).isNone, context.signPoly x,
    context.signPoly x == context.signQuery x)

#guard manySample 1 == some (true, 1, true)
#guard manySample (-1) == some (true, -1, true)

end Hex.RealClosure.Algebraic.QueryReductionTests
