/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.IsolationRoots

public section

namespace Hex.RealClosure.Isolation

/-- Finite isolation choices. The standard policy uses the prescribed bound
search and bisection cap. The bounded policy omits bisection; the whole-line
policy omits both optimizations. Every remaining cell uses complete BKR. -/
inductive Policy where
  | standard
  | bounded
  | whole
  deriving DecidableEq, Repr

namespace Policy

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [NatCast E] [Neg E] [Inv E]

/-- Run the chosen finite policy, retaining the actual prepared domains. -/
@[expose] def dispatch? (policy : Policy) (sign : E → Int) (p : DensePoly E) :
    Option (Route sign p) :=
  match policy with
  | .standard => Isolation.dispatch? sign p
  | .whole => (Whole.prepare? sign p).map Route.whole
  | .bounded =>
    match Bounds.find? sign p with
    | none => (Whole.prepare? sign p).map Route.whole
    | some bound =>
      (Bisection.Frontier.prepare? sign p (-bound.value) bound.value).map (Route.bounded bound)

/-- Complete every retained interval by the existing descriptor producer.
The standard branch retains the original diagnostic behavior verbatim. -/
@[expose] def complete? {Ctx : Type v} [DecidableEq Ctx]
    (policy : Policy) (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Except SignDet.BuildError (Option (Output sign context)) :=
  match policy with
  | .standard => (Isolation.complete? sign context p).map (Option.map (·.roots))
  | policy =>
    match policy.dispatch? sign p with
    | none => .ok none
    | some route => (route.complete context).map some

/-- The default choice executes the original isolation operation. -/
theorem complete?_standard {Ctx : Type v} [DecidableEq Ctx]
    (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    complete? .standard sign context p =
      (Isolation.complete? sign context p).map (Option.map (·.roots)) := rfl

end Policy
end Hex.RealClosure.Isolation
