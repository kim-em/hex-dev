/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.AlgebraicContext
public meta import HexRealClosure.AlgebraicContext

namespace Hex.RealClosure.Algebraic.QueryReductionTests

private def sample (scale cofactor : Rat) : Option (Array Bool) := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let head := DensePoly.scale scale
    ((x * x - DensePoly.C 2) * (x - DensePoly.C cofactor))
  let descriptor ← SignDet.Descriptor.validate Sturm.orderSign 7
    { context := 7, head, lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
  let context := Context.adjoin descriptor (fun q => q.den == 1)
  let square := x * x
  let high := square * square * square * x
  let query := context.queryPoly high
  let stored := Element.ofPoly (context := context) high
  let multiple := head * square * square
  let unsigned := DensePoly.pseudoDiv high head
  return #[decide (query.natDegree < head.natDegree),
    decide (context.signPoly high = 1), decide (stored.sign = 1),
    decide (stored.polynomial.natDegree = 7),
    decide (context.queryPoly multiple = 0),
    decide ((Element.ofPoly (context := context) multiple) = 0),
    decide (context.queryPoly (DensePoly.C (-2)) = DensePoly.C (-2)),
    decide (context.signPoly (DensePoly.C (-2)) = -1),
    decide (context.queryPoly x = x),
    decide (context.signQuery unsigned.remainder = if scale < 0 then -1 else 1)]

/-- info: some #[true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 3 3

/-- info: some #[true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (-3) 3

/-- info: some #[true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (1 / 2) 3

/-- info: some #[true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 1 (1 / 2)

end Hex.RealClosure.Algebraic.QueryReductionTests
