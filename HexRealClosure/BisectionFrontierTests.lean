/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BisectionFrontier
public import HexOrderedFn.Infinitesimal
public meta import HexRealClosure.BisectionFrontier
public meta import HexOrderedFn.Infinitesimal

namespace Hex.RealClosure.Bisection.Tests

private def pending (scalar : Rat) : Option (Array Bool) := do
  let head := DensePoly.scale scalar
    (linearFactor (-3 : Rat) * linearFactor 1 * linearFactor 2 * linearFactor 3)
  let initial ← Frontier.prepare? Sturm.orderSign head (-4) 4
  let result ← initial.bisect?
  let quotient := DensePoly.scale scalar
    (linearFactor (-3 : Rat) * linearFactor 1 * linearFactor 3)
  return #[decide (result.nodes = 2), decide (result.removed = [2]),
    decide (result.head = quotient), decide (result.cells.length = 3),
    decide (result.cells.all fun cell => cell.domain.head == quotient),
    decide (result.cells.all fun cell => cell.count == 1),
    decide (result.cells.any fun cell => cell.lower == -4 && cell.upper == 0),
    decide ((select result.cells).isNone)]

/-- info: some #[true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval pending 3

/-- info: some #[true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval pending (-3)

/-- info: some #[true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval pending (1 / 2)

private def close : Option (Array Bool) := do
  let epsilon : RationalFn Rat := RationalFn.X
  let sign := OrderedFn.Infinitesimal.sign OrderedFn.orderSign
  let head := linearFactor epsilon * linearFactor (2 * epsilon)
  let initial ← Frontier.prepare? sign head 0 1
  let result ← initial.bisect?
  return #[decide (result.nodes = 6), decide (result.removed = []),
    decide (result.head = head), decide (result.cells.length = 7),
    decide (result.cells.any fun cell => cell.count == 2),
    decide ((select result.cells).isSome),
    decide (result.cells.all fun cell => cell.domain.head == head)]

/-- info: some #[true, true, true, true, true, true, true] -/
#guard_msgs in
#eval close

private def retained : Option (Array Bool) := do
  let head := linearFactor (1 : Rat)
  let initial ← Frontier.prepare? Sturm.orderSign head 0 2
  let result ← initial.bisect?
  return #[decide (result.nodes = 0), decide (result.removed = []),
    decide (result.cells.length = 1), decide (result.cells.all fun cell => cell.count == 1)]

/-- info: some #[true, true, true, true] -/
#guard_msgs in
#eval retained

end Hex.RealClosure.Bisection.Tests
