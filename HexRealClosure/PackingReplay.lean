/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReplayOperations
public import HexRealClosure.ValueSigns
public import HexSignDet.DagOperations
public import HexSignDet.DescriptorOperations

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable {UpperCtx : Type} [DecidableEq UpperCtx]

/-- Restore the native sign callback in erased acceptance proofs. The literal
memo entries remain reducible even when callback equality uses function extensionality. -/
@[expose] def Dag.restoreSigns (sign : Element context → Int) (same : sign = Element.sign)
    (binding : UpperCtx) (head : DensePoly (Element context))
    (lower upper : Endpoint (Element context))
    (memo : Option (Array (Dag.Checked sign binding head lower upper))) :
    Option (Array (Dag.Checked Element.sign binding head lower upper)) :=
  memo.map fun entries => entries.map fun entry =>
    ⟨entry.value, by rw [← same]; exact entry.accepted⟩

/-- Restoring an equal callback preserves the validator's complete result. -/
theorem Dag.restoreSigns_validate (sign : Element context → Int) (same : sign = Element.sign)
    (binding : UpperCtx) (head : DensePoly (Element context))
    (lower upper : Endpoint (Element context)) (graph : Dag (Element context) UpperCtx) :
    Dag.restoreSigns sign same binding head lower upper
      (graph.validate? sign binding head lower upper) =
      graph.validate? Element.sign binding head lower upper := by
  cases same
  unfold restoreSigns
  have identity : (fun entry : Dag.Checked Element.sign binding head lower upper =>
      (⟨entry.value, entry.accepted⟩ : Dag.Checked Element.sign binding head lower upper)) = id := by
    funext entry
    cases entry
    rfl
  simp only [identity, Array.map_id]
  cases graph.validate? Element.sign binding head lower upper <;> rfl

/-- Check every literal graph entry with original packing equations and cached
input-sign evidence. Missing records stop ordinary-kernel assembly at their
respective boundaries. Transport changes only erased acceptance proofs. -/
@[expose] def Dag.validatePacking? (entries : List (Packing context))
    (signs : List (ValueSign context)) (binding : UpperCtx)
    (head : DensePoly (Element context)) (lower upper : Endpoint (Element context))
    (graph : Dag (Element context) UpperCtx) :
    Option (Array (Dag.Checked Element.sign binding head lower upper)) :=
  Dag.restoreSigns (Element.replaySign signs) (funext (Element.replaySign_eq signs))
    binding head lower upper
    (@SignDet.Dag.changeOps _ _ _ _ inferInstance inferInstance inferInstance inferInstance
      inferInstance _ (Element.replayOne inferInstance rfl entries)
      (Element.replayAdd inferInstance rfl entries) (Element.replaySub inferInstance rfl entries)
      (Element.replayMul inferInstance inferInstance rfl rfl entries)
      (Element.replayNatCast inferInstance rfl entries)
      (Element.replayOne_eq inferInstance rfl entries)
      (Element.replayAdd_eq inferInstance rfl entries)
      (Element.replaySub_eq inferInstance rfl entries)
      (Element.replayMul_eq inferInstance inferInstance rfl rfl entries)
      (Element.replayNatCast_eq inferInstance rfl entries)
      (Element.replaySign signs) binding head lower upper
      (@SignDet.Dag.validate? _ _ _ _
        (Element.replayOne inferInstance rfl entries) (Element.replayAdd inferInstance rfl entries)
        (Element.replaySub inferInstance rfl entries)
        (Element.replayMul inferInstance inferInstance rfl rfl entries)
        (Element.replayNatCast inferInstance rfl entries) _
        (Element.replaySign signs) binding head lower upper graph))

/-- Acceptance, rejection and the full checked memo agree with native validation,
for every supplied inventory, without a hidden completeness premise. -/
theorem Dag.validatePacking_eq (entries : List (Packing context))
    (signs : List (ValueSign context)) (binding : UpperCtx)
    (head : DensePoly (Element context)) (lower upper : Endpoint (Element context))
    (graph : Dag (Element context) UpperCtx) :
    Dag.validatePacking? entries signs binding head lower upper graph =
      graph.validate? Element.sign binding head lower upper := by
  unfold validatePacking?
  rw [SignDet.Dag.changeOps_validate, Dag.restoreSigns_validate]

/-- Restore an equal sign callback in the descriptor's erased acceptance proof. -/
@[expose] def Descriptor.restoreSigns (sign : Element context → Int)
    (same : sign = Element.sign) (binding : UpperCtx)
    (descriptor : Descriptor (Element context) UpperCtx sign binding) :
    Descriptor (Element context) UpperCtx Element.sign binding :=
  Descriptor.ofChecked Element.sign binding descriptor.raw descriptor.evidence (by
    rw [← same]
    exact descriptor.accepted)

/-- Restoring an unchanged sign callback is the identity on full descriptors. -/
theorem Descriptor.restoreSigns_self (binding : UpperCtx)
    (descriptor : Descriptor (Element context) UpperCtx Element.sign binding) :
    Descriptor.restoreSigns Element.sign rfl binding descriptor = descriptor := by
  unfold restoreSigns
  exact Descriptor.ofChecked_eq descriptor

/-- Run the supplied descriptor reader with equal operations and callback,
transporting only its erased acceptance proof to the original immutable owner. -/
@[expose] def Descriptor.readOperations? (one : One (Element context))
    (add : Add (Element context)) (sub : Sub (Element context))
    (mul : Mul (Element context)) (natCast : NatCast (Element context))
    (ho : one = Element.instOne) (ha : add = Element.instAdd) (hs : sub = Element.instSub)
    (hm : mul = Element.instMul) (hn : natCast = Element.instNatCast)
    (sign : Element context → Int) (same : sign = Element.sign) (binding : UpperCtx)
    (raw : RawDescriptor (Element context) UpperCtx) (graph : Dag (Element context) UpperCtx) :
    Option (@SignDet.Descriptor (Element context) UpperCtx _ _
      Element.instOne Element.instAdd Element.instSub Element.instMul Element.instNatCast _
      Element.sign binding) :=
  let result := do
    let evidence ← @SignDet.Dag.replay? _ _ _ _ one add sub mul natCast _
      sign binding raw.head raw.lower raw.upper
      (@RawDescriptor.queries (Element context) UpperCtx _ _ natCast mul raw) graph
    @SignDet.Descriptor.ofReplay? _ _ _ _ one add sub mul natCast _ sign binding raw evidence
  result.map fun descriptor =>
    Descriptor.restoreSigns sign same binding
      (@SignDet.Descriptor.changeOps (Element context) UpperCtx _ _ _
        Element.instOne Element.instAdd Element.instSub Element.instMul Element.instNatCast
        one add sub mul natCast ho ha hs hm hn sign binding descriptor)

/-- Equal operations and callback preserve the complete native reader result. -/
theorem Descriptor.readOperations_eq (one : One (Element context))
    (add : Add (Element context)) (sub : Sub (Element context))
    (mul : Mul (Element context)) (natCast : NatCast (Element context))
    (ho : one = Element.instOne) (ha : add = Element.instAdd) (hs : sub = Element.instSub)
    (hm : mul = Element.instMul) (hn : natCast = Element.instNatCast)
    (sign : Element context → Int) (same : sign = Element.sign) (binding : UpperCtx)
    (raw : RawDescriptor (Element context) UpperCtx) (graph : Dag (Element context) UpperCtx) :
    Descriptor.readOperations? one add sub mul natCast ho ha hs hm hn sign same binding raw graph =
      (do
        let evidence ← @SignDet.Dag.replay? (Element context) UpperCtx _ _
          Element.instOne Element.instAdd Element.instSub Element.instMul Element.instNatCast _
          Element.sign binding raw.head raw.lower raw.upper
          (@RawDescriptor.queries (Element context) UpperCtx _ _
            Element.instNatCast Element.instMul raw) graph
        @SignDet.Descriptor.ofReplay? (Element context) UpperCtx _ _
          Element.instOne Element.instAdd Element.instSub Element.instMul Element.instNatCast _
          Element.sign binding raw evidence) := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hn
  cases same
  dsimp only [readOperations?]
  have identity : (fun descriptor : Descriptor (Element context) UpperCtx Element.sign binding =>
      Descriptor.restoreSigns Element.sign rfl binding
        (SignDet.Descriptor.changeOps Element.instOne Element.instAdd Element.instSub
          Element.instMul Element.instNatCast rfl rfl rfl rfl rfl Element.sign binding descriptor)) =
      id := by
    funext descriptor
    rw [SignDet.Descriptor.changeOps_self, Descriptor.restoreSigns_self]
    rfl
  simp only [identity, Option.map_id]
  rfl

/-- Check the supplied root graph and reconstructed descriptor with the finite
packing and input-sign inventories. Restore native operations only in proofs.
Compiled evaluation retains native fallback for absent records. -/
@[expose] def Descriptor.readPacking? (entries : List (Packing context))
    (signs : List (ValueSign context)) (binding : UpperCtx)
    (raw : RawDescriptor (Element context) UpperCtx) (graph : Dag (Element context) UpperCtx) :
    Option (Descriptor (Element context) UpperCtx Element.sign binding) :=
  Descriptor.readOperations? (Element.replayOne inferInstance rfl entries)
    (Element.replayAdd inferInstance rfl entries) (Element.replaySub inferInstance rfl entries)
    (Element.replayMul inferInstance inferInstance rfl rfl entries)
    (Element.replayNatCast inferInstance rfl entries)
    (Element.replayOne_eq inferInstance rfl entries)
    (Element.replayAdd_eq inferInstance rfl entries)
    (Element.replaySub_eq inferInstance rfl entries)
    (Element.replayMul_eq inferInstance inferInstance rfl rfl entries)
    (Element.replayNatCast_eq inferInstance rfl entries)
    (Element.replaySign signs) (funext (Element.replaySign_eq signs)) binding raw graph

/-- Complete-record descriptor assembly agrees with native validation for every
inventory, including rejection; completeness is not assumed by this equality. -/
theorem Descriptor.readPacking_eq (entries : List (Packing context))
    (signs : List (ValueSign context)) (binding : UpperCtx)
    (raw : RawDescriptor (Element context) UpperCtx) (graph : Dag (Element context) UpperCtx) :
    Descriptor.readPacking? entries signs binding raw graph = (do
      let evidence ← graph.replay? Element.sign binding raw.head raw.lower raw.upper raw.queries
      Descriptor.ofReplay? Element.sign binding raw evidence) :=
  Descriptor.readOperations_eq (Element.replayOne inferInstance rfl entries)
    (Element.replayAdd inferInstance rfl entries) (Element.replaySub inferInstance rfl entries)
    (Element.replayMul inferInstance inferInstance rfl rfl entries)
    (Element.replayNatCast inferInstance rfl entries)
    (Element.replayOne_eq inferInstance rfl entries)
    (Element.replayAdd_eq inferInstance rfl entries)
    (Element.replaySub_eq inferInstance rfl entries)
    (Element.replayMul_eq inferInstance inferInstance rfl rfl entries)
    (Element.replayNatCast_eq inferInstance rfl entries)
    (Element.replaySign signs) (funext (Element.replaySign_eq signs)) binding raw graph

/-- Successful descriptor assembly retains the supplied literal subject. -/
theorem Descriptor.readPacking_raw (entries : List (Packing context))
    (signs : List (ValueSign context)) (binding : UpperCtx)
    (raw : RawDescriptor (Element context) UpperCtx) (graph : Dag (Element context) UpperCtx)
    {root : Descriptor (Element context) UpperCtx Element.sign binding}
    (accepted : Descriptor.readPacking? entries signs binding raw graph = some root) :
    root.raw = raw := by
  rw [Descriptor.readPacking_eq] at accepted
  cases replayed : graph.replay? Element.sign binding raw.head raw.lower raw.upper raw.queries with
  | none => simp [replayed, bind, Option.bind] at accepted
  | some evidence =>
    simp only [replayed, bind, Option.bind] at accepted
    exact Descriptor.ofReplay_raw accepted

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Dag.restoreSigns_validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Dag.restoreSigns_validate

/-- info: 'Hex.RealClosure.Algebraic.Dag.validatePacking_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Dag.validatePacking_eq

/-- info: 'Hex.RealClosure.Algebraic.Descriptor.restoreSigns_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Descriptor.restoreSigns_self

/-- info: 'Hex.RealClosure.Algebraic.Descriptor.readPacking_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Descriptor.readPacking_eq

/-- info: 'Hex.RealClosure.Algebraic.Descriptor.readOperations_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Descriptor.readOperations_eq

/-- info: 'Hex.RealClosure.Algebraic.Descriptor.readPacking_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Descriptor.readPacking_raw
