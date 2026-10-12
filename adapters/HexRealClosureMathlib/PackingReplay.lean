/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingReduction

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Original packing keys and cached signs for every reached operation of the
actual node. Reduced moments retain their exact indexed reduction witnesses. -/
structure NodeData {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K)
    (p : Hex.DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (Hex.DensePoly (Element context))) (n : Hex.SignDet.Node (Element context) C) : Prop where
  head : ValueSign.LeadingData records p
  preparation : ∀ r, n.preparation = some r → PreparationData entries records read p qs r.steps
  products : ∀ i : Fin n.size, n.reductions[i] = none →
    MomentData entries read (Hex.SignDet.QueryReduction.operands qs n.preparation) n.system.rows[i]
  reductions : ∀ i : Fin n.size, ∀ r, n.reductions[i] = some r →
    ReductionData entries records read p 1
      (Hex.SignDet.factors (Hex.SignDet.QueryReduction.operands qs n.preparation) n.system.rows[i])
      r.steps r.result
  moments : ∀ i : Fin n.size, QueryData entries records read p
    (Hex.SignDet.queryPoly (Hex.SignDet.QueryReduction.operands qs n.preparation)
      n.system.rows[i] n.reductions[i]) a b n.moments[i]

/-- Assemble all finite node premises at the same point as the retained
packing and input-sign inventories, without recomputing a moment or reduction. -/
theorem lift_node {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p : Hex.DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (Hex.DensePoly (Element context))) (n : Hex.SignDet.Node (Element context) C)
    (data : NodeData entries records read p a b qs n) :
    Transport.Finite.NodeData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p a b qs n := by
  refine ⟨ValueSign.lift_leading records p read zero unit descriptorData signData data.head,
    ?_, ?_, ?_, ?_⟩
  · intro r accepted
    exact lift_preparation entries records read zero unit descriptorData packingData signData
      p qs r.steps (data.preparation r accepted)
  · intro i unreduced
    exact lift_moment entries read zero _ _ _ (fun entry member =>
      (entry.atPoint read zero unit descriptorData (packingData entry member)).1)
      (data.products i unreduced)
  · intro i r accepted
    exact lift_reduction entries records read zero unit descriptorData packingData signData
      p 1 _ r.steps r.result (data.reductions i r accepted)
  · intro i
    exact lift_query entries records read zero unit descriptorData packingData signData
      p _ a b n.moments[i] (data.moments i)

/-- Retained data follows the actual replay tree and its positional slices. -/
@[expose] def ReplayData {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K)
    (p : Hex.DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (Hex.DensePoly (Element context))) : Hex.SignDet.Replay (Element context) C → Prop
  | .leaf n => NodeData entries records read p a b qs n
  | .split n l r => NodeData entries records read p a b qs n ∧
      ReplayData entries records read p a b (qs.take (qs.length / 2)) l ∧
      ReplayData entries records read p a b (qs.drop (qs.length / 2)) r

/-- Assemble a full BKR replay at the common selected point, preserving both
child slices and each node's actual moment operands and reductions. -/
theorem lift_replay {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p : Hex.DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (qs : List (Hex.DensePoly (Element context))) (tree : Hex.SignDet.Replay (Element context) C)
    (data : ReplayData entries records read p a b qs tree) :
    Transport.Finite.ReplayData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p a b qs tree := by
  induction tree generalizing qs with
  | leaf n =>
    exact lift_node entries records read zero unit descriptorData packingData signData
      p a b qs n data
  | split n l r ihl ihr =>
    exact ⟨lift_node entries records read zero unit descriptorData packingData signData
      p a b qs n data.1, ihl _ data.2.1, ihr _ data.2.2⟩

/-- Original packing keys for the exact iterated derivative sequence. -/
@[expose] def DerivativeData (entries : List (Packing context)) (read : E → K)
    (p : Hex.DensePoly (Element context)) : Nat → Prop
  | 0 => True
  | n + 1 => DifferentiationData entries read p ∧ DerivativeData entries read p.derivative n

omit [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K] in
/-- Lift every reached derivative using only its recorded casts and products. -/
theorem lift_derivatives (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p : Hex.DensePoly (Element context)) (n : Nat)
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : DerivativeData entries read p n) :
    Transport.Finite.DerivativeData (fun a : Element context => eval read x a.polynomial) p n := by
  induction n generalizing p with
  | zero => exact trivial
  | succ n ih =>
    exact ⟨lift_differentiation entries read zero x p equations data.1,
      ih p.derivative data.2⟩

/-- Retained premises for a complete next-level root descriptor, including the
actual derivative queries, head guard and full selected-root replay. -/
structure DescriptorData {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K)
    (raw : Hex.SignDet.RawDescriptor (Element context) C)
    (evidence : Hex.SignDet.Replay (Element context) C) : Prop where
  derivatives : DerivativeData entries read raw.head raw.head.natDegree
  head : ValueSign.LeadingData records raw.head
  replay : ReplayData entries records read raw.head raw.lower raw.upper raw.queries evidence

/-- Assemble the next descriptor's finite premises from the predecessor's one
point and retained inventories, without assuming a globally closed reader. -/
theorem lift_descriptor {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (raw : Hex.SignDet.RawDescriptor (Element context) C)
    (evidence : Hex.SignDet.Replay (Element context) C)
    (data : DescriptorData entries records read raw evidence) :
    Transport.Finite.DescriptorData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) raw evidence := by
  exact ⟨lift_derivatives entries read zero _ raw.head raw.head.natDegree (fun entry member =>
      (entry.atPoint read zero unit descriptorData (packingData entry member)).1) data.derivatives,
    ValueSign.lift_leading records raw.head read zero unit descriptorData signData data.head,
    lift_replay entries records read zero unit descriptorData packingData signData
      raw.head raw.lower raw.upper raw.queries evidence data.replay⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_node

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_replay

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_derivatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_derivatives

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_descriptor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_descriptor
