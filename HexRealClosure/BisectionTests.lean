/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Bisection
public meta import HexRealClosure.Bisection

namespace Hex.RealClosure.Bisection.Tests

private def sample (scale : Rat) (rootCut : Bool) : Option (Array Bool) := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let factor := x * x - DensePoly.C 2
  let head := DensePoly.scale scale (if rootCut then factor * (x - 1) else factor)
  let split ← bisect? Sturm.orderSign head 0 2
  let removed := match split.mode with | .regular _ => false | .root _ => true
  return #[decide (midpoint (0 : Rat) 2 = 1), decide (removed = rootCut),
    decide (split.mode.head = DensePoly.scale scale factor),
    decide (split.left.head = split.right.head),
    decide (Sturm.queryPrepared split.left 1 = 0),
    decide (Sturm.queryPrepared split.right 1 = 1),
    decide (split.left.upper = .finite 1), decide (split.right.lower = .finite 1),
    decide (split.mode.head.leadingCoeff = scale),
    decide ((Sturm.prepare Sturm.orderSign head (.finite 0) (.finite 1)).isNone = rootCut),
    decide ((split? Sturm.orderSign head (.finite 0) (.finite 2) 0).isNone),
    decide ((split? Sturm.orderSign head (.finite 0) (.finite 2) 2).isNone)]

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 3 true

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (-3) true

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample (1 / 2) true

/-- info: some #[true, true, true, true, true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval sample 1 false

/-- info: true -/
#guard_msgs in
#eval (bisect? Sturm.orderSign (0 : DensePoly Rat) 0 2).isNone

/-- info: true -/
#guard_msgs in
#eval (bisect? Sturm.orderSign (DensePoly.ofCoeffs #[(1 : Rat), -2, 1]) 0 2).isNone

/-- info: true -/
#guard_msgs in
#eval (bisect? Sturm.orderSign (DensePoly.ofCoeffs #[(1 : Rat), 1]) 2 0).isNone

#check_failure Split.mk

end Hex.RealClosure.Bisection.Tests
