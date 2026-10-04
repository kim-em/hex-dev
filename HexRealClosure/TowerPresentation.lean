/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerSuffix
public import HexRealClosure.TowerRoots

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry}

/-- A stored value in a finite validated algebraic tower over a fixed native
coefficient context. The suffix retains every selected descriptor in order. -/
structure Presentation (parent : Context registry) : Type 1 where
  suffix : Suffix parent
  value : suffix.context.Value

/-- Any value in an actual root context gives a finite native presentation. -/
@[expose] def Root.presentation (root : Root parent) (a : root.context.Value) : Presentation parent := by
  cases root with
  | point value => exact ⟨.nil, a⟩
  | selected descriptor extension built =>
    cases built
    exact ⟨.root descriptor .nil, a⟩


/-- Prefix a native presentation with an earlier validated suffix. Context
casts remain inside this constructor. -/
@[expose] def Presentation.prepend (first : Suffix parent)
    (a : Presentation first.context) : Presentation parent :=
  ⟨first.append a.suffix,
    _root_.cast (congrArg Context.Value (first.append_context a.suffix).symm) a.value⟩


/-- Reencode a selected root at any position and retain every reconstructed
later level. The returned presentation includes the original preceding suffix. -/
@[expose] def Presentation.refine (first : Suffix parent)
    {descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature}
    {head : DensePoly first.context.Value} {lower upper : Endpoint first.context.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (later : Suffix (first.context.adjoin descriptor).context)
    (rebuilt : Rebuilt (Conversion.refine first.context encoding) later)
    (a : later.context.Value) : Presentation parent :=
  let same := (Conversion.refine_spec first.context encoding).1.trans
    (congrArg Extension.context (first.context.refine encoding).canonical)
  let right : Suffix first.context := .root encoding.target (same ▸ rebuilt.suffix)
  (Presentation.mk right (_root_.cast (congrArg Context.Value
    (rebuilt.context_eq.symm.trans (Suffix.cast_context same rebuilt.suffix).symm))
    (rebuilt.result.value a))).prepend first


/-- Reconstruct the requested later levels once and package the actual refined
presentation. Invalid reconstruction is reported at this checked boundary. -/
@[expose] def Presentation.refine? (first : Suffix parent)
    {descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature}
    {head : DensePoly first.context.Value} {lower upper : Endpoint first.context.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (later : Suffix (first.context.adjoin descriptor).context)
    (a : later.context.Value) : Option (Presentation parent) :=
  ((Conversion.refine first.context encoding).rebuild? later).map
    (fun rebuilt => Presentation.refine first encoding later rebuilt a)

end Hex.RealClosure.Tower
