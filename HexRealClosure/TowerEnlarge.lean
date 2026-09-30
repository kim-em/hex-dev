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

private theorem Context.origin_transport {left right : Context registry}
    (h : left = right) : h ▸ left.origin = right.origin := by
  cases h
  rfl

private theorem Origin.pack_transport {left right : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    (target_eq : suffix.context = left) (h : left = right) :
    h ▸ (Origin.pack base suffix target_eq : Origin left) =
      (Origin.pack base suffix (target_eq.trans h) : Origin right) := by
  cases h
  rfl

private theorem Origin.transport_injective {left right : Context registry}
    (h : left = right) {a b : Origin left}
    (hab : h ▸ a = h ▸ b) : a = b := by
  cases h
  exact hab

/-- The stored origin of one root over a staged base is its actual descriptor. -/
theorem Context.origin_adjoin_base
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (descriptor : SignDet.Descriptor (Context.base base).Value Signature
      (Context.base base).sign (Context.base base).signature) :
    ((Context.base base).adjoin descriptor).context.origin =
      Origin.pack base (.root descriptor .nil) rfl := by
  let extension := (Context.base base).adjoin descriptor
  have hnative : extension.context =
      Context.pack (.root (.base base) descriptor extension.frame extension.encoded) :=
    (Context.adjoin_native (.base base) descriptor).1
  have hroot : (Context.pack
      (.root (.base base) descriptor extension.frame extension.encoded)).origin =
      Origin.pack base (.root descriptor .nil) hnative := by
    rfl
  apply Origin.transport_injective hnative
  rw [Context.origin_transport hnative]
  exact hroot.trans (Origin.pack_transport base (.root descriptor .nil) rfl hnative).symm

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_eq

/-- info: 'Hex.RealClosure.Tower.Context.origin_adjoin_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.origin_adjoin_base
