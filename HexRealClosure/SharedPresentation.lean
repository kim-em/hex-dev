/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerPresentation
public import HexRealClosure.LiveContext

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A declared base context retains that exact nominal base in its origin. -/
theorem Context.ofBase_origin_base (base : BaseContext.PackedContext registry) :
    (Context.ofBase base).origin.base = base := by
  cases base with
  | pack original =>
    change (Context.base original).origin.base = _
    rw [Context.origin_base]
    rfl

/-- Native root materialization retains the original staged base. -/
theorem Root.origin_base {parent : Context registry} (root : Root parent) :
    root.context.origin.base = parent.origin.base := by
  cases root with
  | point value => rfl
  | selected descriptor extension built =>
    cases built
    change (parent.adjoin descriptor).context.origin.base = parent.origin.base
    rw [Context.origin_adjoin, Origin.snoc_base]

/-- Retain a value's complete validated suffix over its actual original base.
Only the stored equality changes the final value's context ownership. -/
@[expose] def Origin.presentation {context : Context registry} (origin : Origin context)
    (a : context.Value) : Presentation (Context.ofBase origin.base) := by
  cases origin with
  | pack original suffix same =>
    exact ⟨suffix, _root_.cast (congrArg Context.Value same.symm) a⟩

/-- Present any computed value of the shared target over its declared base. -/
@[expose] def Shared.targetPresentation {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (a : shared.input.context.Value) : Presentation (Context.ofBase base) :=
  _root_.cast (congrArg (fun base => Presentation (Context.ofBase base)) shared.base_eq)
    (shared.input.context.origin.presentation a)

/-- Express an original owner value using its checked inclusion in the target. -/
@[expose] def Shared.presentation {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    Presentation (Context.ofBase base) :=
  shared.targetPresentation (shared.value index a)

end Hex.RealClosure.Tower
