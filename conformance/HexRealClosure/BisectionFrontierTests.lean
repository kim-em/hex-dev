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
  let result ← initial.refine?
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
  let result ← initial.refine?
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
  let result ← initial.refine?
  return #[decide (result.nodes = 0), decide (result.removed = []),
    decide (result.cells.length = 1), decide (result.cells.all fun cell => cell.count == 1)]

/-- info: some #[true, true, true, true] -/
#guard_msgs in
#eval retained

private def multiple : Option (Array Bool) := do
  let head := linearFactor (0 : Rat) * linearFactor 1 * linearFactor 2 * linearFactor 3
  let initial ← Frontier.prepare? Sturm.orderSign head (-4) 4
  let result ← initial.refine?
  let active := linearFactor (1 : Rat) * linearFactor 3
  return #[decide (result.nodes = 2), decide (result.removed = [0, 2]),
    decide (result.head = active), decide (result.cells.length = 3),
    decide (result.cells.any fun cell => cell.count == 0),
    decide (result.cells.all fun cell => cell.domain.head == active),
    decide ((result.cells.map (·.count)).sum = 2), decide ((select result.cells).isNone)]

/-- info: some #[true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval multiple

private def rootFallback : Option (Array Bool) := do
  let epsilon : RationalFn Rat := RationalFn.X
  let sign := OrderedFn.Infinitesimal.sign OrderedFn.orderSign
  let active := linearFactor epsilon * linearFactor (2 * epsilon)
  let head := linearFactor (0 : RationalFn Rat) * active
  let initial ← Frontier.prepare? sign head (-1) 1
  let result ← initial.refine?
  return #[decide (result.nodes = 8), decide (result.removed = [0]),
    decide (result.head = active), decide (result.cells.length = 9),
    decide (result.cells.any fun cell => cell.count == 2),
    decide ((select result.cells).isSome),
    decide (result.cells.all fun cell => cell.domain.head == active),
    decide ((result.cells.map (·.count)).sum = 2)]

/-- info: some #[true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval rootFallback

private def pendingMultiple : Option (Array Bool) := do
  let head := linearFactor (-3 : Rat) * linearFactor (-2) * linearFactor (-1) *
    linearFactor 1 * linearFactor 2 * linearFactor 3
  let initial ← Frontier.prepare? Sturm.orderSign head (-4) 4
  let result ← initial.refine?
  let active := linearFactor (-3 : Rat) * linearFactor (-1) * linearFactor 1 * linearFactor 3
  return #[decide (result.nodes = 3), decide (result.removed = [-2, 2]),
    decide (result.head = active), decide (result.cells.length = 4),
    decide (result.cells.all fun cell => cell.domain.head == active),
    decide (result.cells.all fun cell => cell.count == 1), decide ((select result.cells).isNone)]

/-- info: some #[true, true, true, true, true, true, true] -/
#guard_msgs in
#eval pendingMultiple

end Hex.RealClosure.Bisection.Tests
