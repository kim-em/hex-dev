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

/-- The ordered reader uses the existing canonical context factory. -/
@[simp] theorem OwnerReader.ordered_read {base : BaseContext.PackedContext registry}
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    (context : Context registry) :
    (OwnerReader.ordered following reference).read context = context.model? following reference := rfl

/-- On contexts whose origin base is `base`, the reader uses the same
selected-root interpretation as the ordered factory. Original owners may
still require provider-key reconciliation. -/
class OwnerReader.Agrees {base : BaseContext.PackedContext registry}
    (reader : OwnerReader registry R) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) : Prop where
  read_eq : ∀ context : Context registry, context.origin.base = base →
    reader.read context = context.model? following reference

instance OwnerReader.agrees_ordered {base : BaseContext.PackedContext registry} (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) :
    (OwnerReader.ordered following reference).Agrees following reference where
  read_eq := fun _ _ => rfl

/-- An ordered field embedding transports every accepted canonical owner
model from one reader to another. Refused owners need not remain refused. -/
class OwnerReader.Morphism {S : Type v}
    [Field S] [LinearOrder S] [DecidableEq S] [IsStrictOrderedRing S] [IsRealClosed S]
    (reader : OwnerReader registry R) (next : OwnerReader registry S)
    (embedding : R →+* S) (ordered : StrictMono embedding) : Prop where
  model : ∀ (context : Context registry) (original : Tower.Model context R),
    reader.read context = some original →
      next.read context = some (original.map embedding ordered)

/-- The identity reader morphism retains every accepted owner model. -/
instance OwnerReader.morphism_identity (reader : OwnerReader registry R) :
    OwnerReader.Morphism reader reader (RingHom.id R) strictMono_id where
  model context original produced := by
    rw [produced]
    apply congrArg some
    apply Tower.Model.value_ext
    intro a
    rfl

/-- A morphism over the identity embedding retains the original model itself. -/
theorem OwnerReader.Morphism.same_model {reader next : OwnerReader registry R}
    (morphism : OwnerReader.Morphism reader next (RingHom.id R) strictMono_id)
    (context : Context registry) (original : Tower.Model context R)
    (produced : reader.read context = some original) : next.read context = some original := by
  have checked := morphism.model context original produced
  have identity : original.map (RingHom.id R) strictMono_id = original := by
    apply Tower.Model.value_ext
    intro a
    rfl
  rw [identity] at checked
  exact checked

open scoped Hex.OrderedFn.Infinitesimal in
/-- The ordered owner reader transports every original selected root through
the constructed next base, using the derived constant embedding. -/
instance OwnerReader.morphism_ordered
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (following : (BaseContext.PackedContext.pack base).Realization)
    (reference : Tower.Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    OwnerReader.Morphism (OwnerReader.ordered following reference)
      (OwnerReader.ordered following.infinitesimal (Tower.Model.nextBase base reference ambient))
      (Ambient.coefficientHom ambient) (Ambient.coefficientHom_strictMono ambient) where
  model context original produced := context.model?_next base following reference ambient original produced

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

/-- info: 'Hex.RealClosure.Tower.OwnerReader.ordered_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.OwnerReader.ordered_read

/-- info: 'Hex.RealClosure.Tower.OwnerReader.morphism_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.OwnerReader.morphism_ordered

/-- info: 'Hex.RealClosure.Tower.OwnerReader.morphism_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.OwnerReader.morphism_identity

/-- info: 'Hex.RealClosure.Tower.OwnerReader.Morphism.same_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.OwnerReader.Morphism.same_model
