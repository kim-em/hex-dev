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

/-- The actual new infinitesimal with the ownership of its native base conversion. -/
@[expose] def Conversion.parameter {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign) :
    (Conversion.infinitesimal base).context.Value :=
  _root_.cast (congrArg Context.Value (Conversion.infinitesimal_spec base).1.symm)
    (BaseContext.Element.infinitesimal base)

/-- Include the new base parameter through every actual rebuilt algebraic
level, with ownership in the returned native target context. -/
@[expose] def Rebuilt.parameter {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    {suffix : Suffix (Context.base base)}
    (rebuilt : Rebuilt (Conversion.infinitesimal base) suffix) : rebuilt.result.context.Value :=
  _root_.cast (congrArg Context.Value rebuilt.context_eq)
    (rebuilt.suffix.embed (Conversion.parameter base))

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

private theorem Context.origin_transport {left right : Context registry}
    (h : left = right) : h ▸ left.origin = right.origin := by
  cases h
  rfl

private theorem Origin.transport_injective {left right : Context registry}
    (h : left = right) {a b : Origin left}
    (hab : h ▸ a = h ▸ b) : a = b := by
  cases h
  exact hab

/-- Adjoining a validated descriptor appends it to the stored origin. -/
theorem Context.origin_adjoin (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature) :
    (parent.adjoin descriptor).context.origin = parent.origin.snoc descriptor := by
  cases parent with
  | pack chain =>
    let extension := (Context.pack chain).adjoin descriptor
    have hnative : extension.context =
        Context.pack (.root chain descriptor extension.frame extension.encoded) :=
      (Context.adjoin_native chain descriptor).1
    have hroot : (Context.pack
        (.root chain descriptor extension.frame extension.encoded)).origin =
        hnative ▸ (Context.pack chain).origin.snoc descriptor := by
      rfl
    apply Origin.transport_injective hnative
    rw [Context.origin_transport hnative]
    exact hroot

/-- Append a validated suffix to an existing packed origin in predecessor
order. -/
@[expose] def Origin.extend {source : Context registry} (origin : Origin source)
    (suffix : Suffix source) : Origin suffix.context :=
  match suffix with
  | .nil => origin
  | .root descriptor rest => (origin.snoc descriptor).extend rest

/-- Appending roots to a packed origin concatenates its validated suffix. -/
private theorem Origin.extend_pack
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    {source : Context registry}
    (first : Suffix (Context.base base)) (hsource : first.context = source)
    (later : Suffix source) :
    (Origin.pack base first hsource).extend later =
      Origin.pack base (first.append (hsource.symm ▸ later))
        (first.append_cast_context hsource later) := by
  induction later generalizing first with
  | nil =>
    cases hsource
    simp only [Origin.extend, Suffix.append_nil]
    rfl
  | root descriptor rest ih =>
    cases hsource
    simp only [Origin.extend, Origin.snoc, Context.castDescriptor]
    simpa only [Suffix.append_root, Suffix.context] using
      (ih (first.snoc descriptor) (Suffix.snoc_context first descriptor))

/-- Extracting the origin after a validated suffix gives the same successive
root extensions as extracting first and appending that suffix. -/
theorem Suffix.origin {source : Context registry} (suffix : Suffix source) :
    suffix.context.origin = source.origin.extend suffix := by
  induction suffix with
  | nil => rfl
  | root descriptor rest ih =>
    rw [Origin.extend]
    rw [← Context.origin_adjoin]
    exact ih

/-- Extracting the origin of a suffix over a staged base recovers its exact
validated descriptors in the original predecessor order. -/
theorem Suffix.origin_exact
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base)) :
    suffix.context.origin = Origin.pack base suffix rfl := by
  rw [Suffix.origin, Context.origin_base]
  have h := Origin.extend_pack base (Suffix.nil : Suffix (Context.base base)) rfl suffix
  have hs : Origin.pack base ((Suffix.nil : Suffix (Context.base base)).append suffix)
      (Suffix.append_cast_context (Suffix.nil : Suffix (Context.base base)) rfl suffix) =
      Origin.pack base suffix rfl := by rfl
  exact h.trans hs

/-- Checked enlargement is exactly the native conversion of a validated
suffix, with source ownership aligned to its original packed context. -/
theorem Context.enlarge?_eq {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    (target_eq : suffix.context = context) :
    context.enlarge? = ((Conversion.infinitesimal base).extend? suffix).map
      (fun conversion => conversion.cast target_eq) := by
  cases target_eq
  rw [Context.enlarge?, Suffix.origin_exact base suffix]
  rfl

/-- The extracted base of a suffix over a staged base is that same base. -/
theorem Suffix.origin_base
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base)) :
    suffix.context.origin.base = BaseContext.PackedContext.pack base := by
  rw [Suffix.origin_exact base suffix]
  rfl

/-- The stored origin of one root over a staged base is its actual descriptor. -/
theorem Context.origin_adjoin_base
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (descriptor : SignDet.Descriptor (Context.base base).Value Signature
      (Context.base base).sign (Context.base base).signature) :
    ((Context.base base).adjoin descriptor).context.origin =
      Origin.pack base (.root descriptor .nil) rfl := by
  exact Suffix.origin_exact base (.root descriptor .nil)

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

/-- info: 'Hex.RealClosure.Tower.Context.origin_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.origin_adjoin

/-- info: 'Hex.RealClosure.Tower.Suffix.origin_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Suffix.origin_base

/-- info: 'Hex.RealClosure.Tower.Suffix.origin_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Suffix.origin_exact

/-- info: 'Hex.RealClosure.Tower.Conversion.parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.parameter

/-- info: 'Hex.RealClosure.Tower.Rebuilt.parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Rebuilt.parameter
