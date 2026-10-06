/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ContextModel
public import HexRealClosureMathlib.TowerRoots

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {R : Type u}
variable [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A canonical owner reader retains the actual selected descriptor whenever
its context extends. Cache proofs depend on this law rather than key order. -/
structure OwnerReader (registry : BaseContext.Registry) (R : Type u)
    [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R] where
  read : (context : Context registry) → Option (Tower.Model context R)
  adjoin : ∀ context descriptor,
    read (context.adjoin descriptor).context = (read context).map (fun model => model.adjoin descriptor)

/-- The existing ordered canonical owner factory. -/
@[expose] noncomputable def OwnerReader.ordered {base : BaseContext.PackedContext registry}
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R) :
    OwnerReader registry R where
  read context := context.model? following reference
  adjoin := fun context descriptor => context.model?_adjoin following reference descriptor

/-- A canonical cached child and parent retain the exact predecessor values. -/
theorem OwnerReader.embed (reader : OwnerReader registry R) (context : Context registry)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (parent : Tower.Model context R) (child : Tower.Model (context.adjoin descriptor).context R)
    (parentProduced : reader.read context = some parent)
    (childProduced : reader.read (context.adjoin descriptor).context = some child)
    (a : context.Value) : child.value ((context.adjoin descriptor).embed a) = parent.value a := by
  have same := reader.adjoin context descriptor
  rw [parentProduced, Option.map_some, childProduced] at same
  cases Option.some.inj same
  exact parent.adjoin_embed descriptor a

/-- A retained root uses its canonical predecessor model and the actual
selected extension. This includes point roots without creating a new context. -/
theorem OwnerReader.root_model (reader : OwnerReader registry R) {parent : Context registry}
    (root : Root parent) (original : Tower.Model parent R)
    (produced : reader.read parent = some original) :
    reader.read root.context = some (root.model original) := by
  cases root with
  | point value => exact produced
  | selected descriptor extension built =>
    cases built
    change reader.read (parent.adjoin descriptor).context = some (original.adjoin descriptor)
    rw [reader.adjoin, produced, Option.map_some]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.OwnerReader.embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.OwnerReader.embed

/-- info: 'Hex.RealClosure.Tower.OwnerReader.root_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.OwnerReader.root_model
