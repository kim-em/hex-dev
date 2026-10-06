/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingMoment

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K]

variable [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Original packing keys and scale-sign records for one supplied indexed
positive-scaled reduction step. -/
structure ReductionStepData (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (p prev factor : Hex.DensePoly (Element context))
    (step : Hex.SignDet.ReductionStep (Element context)) : Prop where
  head : ValueSign.LeadingData records p
  identity : ProductIdentityData entries read p prev factor step.next
    step.witness.leftScale step.witness.quotient step.witness.rightScale
  left : (ValueSign.find records step.witness.leftScale).isSome = true
  right : (ValueSign.find records step.witness.rightScale).isSome = true

/-- Assemble the exact step's finite product identity, head guard and scale
signs at the common point, without rerunning division. -/
theorem lift_reductionStep (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p prev factor : Hex.DensePoly (Element context)) (step : Hex.SignDet.ReductionStep (Element context))
    (data : ReductionStepData entries records read p prev factor step) :
    Transport.ReductionStepData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p prev factor step := by
  refine ⟨ValueSign.lift_leading records p read zero unit descriptorData signData data.head,
    lift_productIdentity entries read zero _ p prev factor step.next _ _ _ ?_ data.identity,
    ValueSign.lookup_sign records _ read zero unit descriptorData signData data.left,
    ValueSign.lookup_sign records _ read zero unit descriptorData signData data.right⟩
  intro entry member
  exact (entry.atPoint read zero unit descriptorData (packingData entry member)).1

/-- The exact paired factor/step recursion and final difference key.
Unmatched lengths have no data obligations and fail the native check. -/
@[expose] def ReductionData (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (p prev : Hex.DensePoly (Element context)) :
    List (Nat × Hex.DensePoly (Element context)) → List (Hex.SignDet.ReductionStep (Element context)) →
      Hex.DensePoly (Element context) → Prop
  | [], [], result => DifferenceData entries read prev result
  | (_, factor) :: fs, step :: ss, result =>
    ReductionStepData entries records read p prev factor step ∧
      ReductionData entries records read p step.next fs ss result
  | _, _, _ => True

/-- Assemble the actual indexed reduction recursion and terminal difference
at one selected point, retaining duplicate factors and step positions. -/
theorem lift_reduction (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p prev : Hex.DensePoly (Element context)) (factors : List (Nat × Hex.DensePoly (Element context)))
    (steps : List (Hex.SignDet.ReductionStep (Element context))) (result : Hex.DensePoly (Element context))
    (data : ReductionData entries records read p prev factors steps result) :
    Transport.ReductionData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p prev factors steps result := by
  induction factors generalizing prev steps with
  | nil =>
    cases steps with
    | nil =>
      exact lift_difference entries read zero _ prev result (fun entry member =>
        (entry.atPoint read zero unit descriptorData (packingData entry member)).1) data
    | cons step steps => exact trivial
  | cons factor factors ih =>
    cases steps with
    | nil => exact trivial
    | cons step steps =>
      exact ⟨lift_reductionStep entries records read zero unit descriptorData packingData signData
        p prev factor.2 step data.1, ih step.next steps data.2⟩

/-- Retained data for the checker's exact shared query preprocessing pairs. -/
@[expose] def PreparationData (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (p : Hex.DensePoly (Element context)) :
    List (Hex.DensePoly (Element context)) → List (Hex.SignDet.ReductionStep (Element context)) → Prop
  | [], [] => True
  | q :: qs, step :: ss => ReductionStepData entries records read p 1 q step ∧
      PreparationData entries records read p qs ss
  | _, _ => True

/-- Assemble the exact shared query reductions before reconstructing a node's
moment operands, retaining their original positions. -/
theorem lift_preparation (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p : Hex.DensePoly (Element context)) (qs : List (Hex.DensePoly (Element context)))
    (steps : List (Hex.SignDet.ReductionStep (Element context)))
    (data : PreparationData entries records read p qs steps) :
    Transport.PreparationData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p qs steps := by
  induction qs generalizing steps with
  | nil => cases steps <;> exact trivial
  | cons q qs ih =>
    cases steps with
    | nil => exact trivial
    | cons step steps =>
      exact ⟨lift_reductionStep entries records read zero unit descriptorData packingData signData
        p 1 q step data.1, ih steps data.2⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_reductionStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_reductionStep

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_reduction

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_preparation
