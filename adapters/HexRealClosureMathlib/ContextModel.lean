/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseFactory

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

/-- Construct an original owner's interpretation in one fixed target field.
The target base derives every compatible coefficient interpretation; the
owner's actual stored suffix supplies all selected algebraic roots. -/
noncomputable def Context.model? (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    Option (Tower.Model context R) := by
  cases context.origin with
  | pack original suffix same =>
    exact (BaseInclusion.make? (.pack original) base).map fun inclusion =>
      let originalModel : Tower.Model (Context.base original) R :=
        (BaseInclusion.Model.derive (source := .pack original) (target := base)
          following inclusion target).source
      same ▸ originalModel.extend suffix

private theorem Context.model?_isSome_proof (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (context.model? following target).isSome = true ↔
      context.origin.base.signature.constants <+: base.signature.constants ∧
        context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  have packaged : (context.model? following target).isSome =
      (BaseInclusion.make? context.origin.base base).isSome := by
    simp only [Context.model?, Origin.base, Option.isSome_map]
  rw [packaged]
  exact BaseInclusion.make?_isSome context.origin.base base

/-- Every owner over a compatible actual staged base obtains a model in the
same target field; unrelated paths and decreasing depth are rejected. -/
theorem Context.model?_isSome (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (context.model? following target).isSome = true ↔
      context.origin.base.signature.constants <+: base.signature.constants ∧
        context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals :=
  context.model?_isSome_proof following target

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.model?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?

/-- info: 'Hex.RealClosure.Tower.Context.model?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_isSome
