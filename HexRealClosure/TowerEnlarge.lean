/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerSuffix

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Rebuild one packed tower over an additional positive infinitesimal. The
stored predecessor chain supplies the base and the exact validated root
suffix. Each root is revalidated in its new predecessor; failure is explicit.
The returned conversion retains the original context as its source. -/
@[expose] def Origin.enlarge? {target : Context registry} (origin : Origin target) :
    Option (Conversion target) := by
  cases origin with
  | pack base suffix target_eq =>
    exact ((Conversion.infinitesimal base).extend? suffix).map
      (fun conversion => conversion.cast target_eq)

/-- Extract the stored base and root suffix before checked enlargement. -/
@[expose] def Context.enlarge? (context : Context registry) :
    Option (Conversion context) := context.origin.enlarge?

/-- Checked enlargement is exactly the native conversion of the stored root
suffix, with source ownership aligned to the original packed context. -/
theorem Context.enlarge?_eq {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    (target_eq : suffix.context = context)
    (origin_eq : context.origin = Origin.pack base suffix target_eq) :
    context.enlarge? = ((Conversion.infinitesimal base).extend? suffix).map
      (fun conversion => conversion.cast target_eq) := by
  rw [Context.enlarge?, origin_eq]
  rfl

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_eq
