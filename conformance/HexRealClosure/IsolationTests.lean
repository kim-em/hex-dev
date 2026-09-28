/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Isolation
public import HexOrderedFn.Infinitesimal
public meta import HexRealClosure.Isolation
public meta import HexOrderedFn.Infinitesimal

namespace Hex.RealClosure.Isolation.Tests

private def bounded (scalar : Rat) : Option (Array Bool) := do
  let p := DensePoly.scale scalar (linearFactor (0 : Rat) * linearFactor 1 * linearFactor 2)
  let search ← search? Sturm.orderSign p
  match search.route with
  | .whole _ => none
  | .bounded bound frontier =>
    return #[decide (bound.value = 8), decide (frontier.nodes = 3),
      decide (frontier.removed = [0, 2]), decide (frontier.head = DensePoly.scale scalar (linearFactor 1)),
      decide ((Bisection.select frontier.cells).isNone)]

/-- info: some #[true, true, true, true, true] -/
#guard_msgs in
#eval bounded 3

/-- info: some #[true, true, true, true, true] -/
#guard_msgs in
#eval bounded (-3)

/-- info: some #[true, true, true, true, true] -/
#guard_msgs in
#eval bounded (1 / 2)

private def whole {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
    [NatCast E] [Neg E] [Inv E] (sign : E → Int) (p : DensePoly E) : Option (Array Bool) := do
  let search ← search? sign p
  match search.route with
  | .bounded _ _ => none
  | .whole whole =>
    return #[decide ((Bounds.find? sign p).isNone), decide (whole.domain.head = p),
      decide (whole.domain.lower = .negInf), decide (whole.domain.upper = .posInf),
      decide (Sturm.queryPrepared whole.domain 1 = 1)]

/-- info: some #[true, true, true, true, true] -/
#guard_msgs in
#eval whole Sturm.orderSign (linearFactor (1000 : Rat))

private def epsilon : RationalFn Rat := RationalFn.X
private def sign₁ : RationalFn Rat → Int := OrderedFn.Infinitesimal.sign Sturm.orderSign

/-- info: some #[true, true, true, true, true] -/
#guard_msgs in
#eval whole sign₁ (linearFactor epsilon⁻¹)

private def delta : RationalFn (RationalFn Rat) := RationalFn.X
private def sign₂ : RationalFn (RationalFn Rat) → Int := OrderedFn.Infinitesimal.sign sign₁

/-- info: some #[true, true, true, true, true] -/
#guard_msgs in
#eval whole sign₂ (linearFactor delta⁻¹)

/-- info: true -/
#guard_msgs in
#eval (search? Sturm.orderSign (0 : DensePoly Rat)).isNone

/-- info: true -/
#guard_msgs in
#eval (search? Sturm.orderSign (linearFactor (1 : Rat) * linearFactor 1)).isNone

end Hex.RealClosure.Isolation.Tests
