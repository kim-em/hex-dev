/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FinitePoint

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K]

/-- Retained original packing keys and reached predecessor arithmetic of the
literal recurrence identity. No source coefficient field laws are assumed. -/
structure RecurrenceData (entries : List (Packing context)) (read : E → K)
    (a b c : Hex.DensePoly (Element context))
    (left : Element context) (quotient : Hex.DensePoly (Element context)) (right : Element context) : Prop where
  leftScale : ScalingData entries read left a
  quotientProduct : ProductData entries read quotient b
  rightScale : ScalingData entries read right c
  remainder : DifferenceData entries read (quotient * b) (Hex.DensePoly.scale right c)
  identity : DifferenceData entries read (Hex.DensePoly.scale left a) (quotient * b - Hex.DensePoly.scale right c)

/-- Lift the actual stored recurrence identity at one point using every
retained packing equation and its finite predecessor operations. -/
theorem lift_recurrence (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (a b c : Hex.DensePoly (Element context))
    (left : Element context) (quotient : Hex.DensePoly (Element context)) (right : Element context)
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : RecurrenceData entries read a b c left quotient right) :
    Transport.Recurrence (fun a : Element context => eval read x a.polynomial)
      a b c left quotient right := by
  exact ⟨lift_scaling entries read zero x left a equations data.leftScale,
    lift_product entries read zero x quotient b equations data.quotientProduct,
    lift_scaling entries read zero x right c equations data.rightScale,
    lift_difference entries read zero x (quotient * b) (Hex.DensePoly.scale right c) equations data.remainder,
    lift_difference entries read zero x (Hex.DensePoly.scale left a) (quotient * b - Hex.DensePoly.scale right c) equations data.identity⟩

/-- Retained original packing keys and reached predecessor arithmetic of the
literal initial identity. No source coefficient field laws are assumed. -/
structure InitialData (entries : List (Packing context)) (read : E → K)
    (p f c : Hex.DensePoly (Element context))
    (left : Element context) (quotient : Hex.DensePoly (Element context)) (right : Element context) : Prop where
  derivative : DifferentiationData entries read p
  inputProduct : ProductData entries read f p.derivative
  leftScale : ScalingData entries read left (f * p.derivative)
  quotientProduct : ProductData entries read quotient p
  rightScale : ScalingData entries read right c
  remainder : SumData entries read (quotient * p) (Hex.DensePoly.scale right c)
  identity : DifferenceData entries read (Hex.DensePoly.scale left (f * p.derivative)) (quotient * p + Hex.DensePoly.scale right c)

/-- Lift the actual stored initial identity at one point using every
retained packing equation and its finite predecessor operations. -/
theorem lift_initial (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p f c : Hex.DensePoly (Element context))
    (left : Element context) (quotient : Hex.DensePoly (Element context)) (right : Element context)
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : InitialData entries read p f c left quotient right) :
    Transport.Initial (fun a : Element context => eval read x a.polynomial)
      p f c left quotient right := by
  exact ⟨lift_differentiation entries read zero x p equations data.derivative,
    lift_product entries read zero x f p.derivative equations data.inputProduct,
    lift_scaling entries read zero x left (f * p.derivative) equations data.leftScale,
    lift_product entries read zero x quotient p equations data.quotientProduct,
    lift_scaling entries read zero x right c equations data.rightScale,
    lift_sum entries read zero x (quotient * p) (Hex.DensePoly.scale right c) equations data.remainder,
    lift_difference entries read zero x (Hex.DensePoly.scale left (f * p.derivative)) (quotient * p + Hex.DensePoly.scale right c) equations data.identity⟩

/-- Retained original packing keys and reached predecessor arithmetic of the
literal terminal identity. No source coefficient field laws are assumed. -/
structure TerminalData (entries : List (Packing context)) (read : E → K)
    (a b : Hex.DensePoly (Element context)) (scale : Element context)
    (quotient : Hex.DensePoly (Element context)) : Prop where
  scaling : ScalingData entries read scale a
  product : ProductData entries read quotient b
  identity : DifferenceData entries read (Hex.DensePoly.scale scale a) (quotient * b)

/-- Lift the actual stored terminal identity at one point using every
retained packing equation and its finite predecessor operations. -/
theorem lift_terminal (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (a b : Hex.DensePoly (Element context)) (scale : Element context)
    (quotient : Hex.DensePoly (Element context))
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : TerminalData entries read a b scale quotient) :
    Transport.Terminal (fun a : Element context => eval read x a.polynomial)
      a b scale quotient := by
  exact ⟨lift_scaling entries read zero x scale a equations data.scaling,
    lift_product entries read zero x quotient b equations data.product,
    lift_difference entries read zero x (Hex.DensePoly.scale scale a) (quotient * b) equations data.identity⟩

/-- Retained original packing keys and reached predecessor arithmetic of the
literal productidentity identity. No source coefficient field laws are assumed. -/
structure ProductIdentityData (entries : List (Packing context)) (read : E → K)
    (p prev factor next : Hex.DensePoly (Element context))
    (left : Element context) (quotient : Hex.DensePoly (Element context)) (right : Element context) : Prop where
  inputProduct : ProductData entries read prev factor
  leftScale : ScalingData entries read left (prev * factor)
  quotientProduct : ProductData entries read quotient p
  rightScale : ScalingData entries read right next
  remainder : SumData entries read (quotient * p) (Hex.DensePoly.scale right next)
  identity : DifferenceData entries read (Hex.DensePoly.scale left (prev * factor)) (quotient * p + Hex.DensePoly.scale right next)

/-- Lift the actual stored productidentity identity at one point using every
retained packing equation and its finite predecessor operations. -/
theorem lift_productIdentity (entries : List (Packing context)) (read : E → K)
    (zero : read 0 = 0) (x : K) (p prev factor next : Hex.DensePoly (Element context))
    (left : Element context) (quotient : Hex.DensePoly (Element context)) (right : Element context)
    (equations : ∀ entry ∈ entries,
      eval read x entry.value.polynomial = eval read x entry.original)
    (data : ProductIdentityData entries read p prev factor next left quotient right) :
    Transport.ProductIdentity (fun a : Element context => eval read x a.polynomial)
      p prev factor next left quotient right := by
  exact ⟨lift_product entries read zero x prev factor equations data.inputProduct,
    lift_scaling entries read zero x left (prev * factor) equations data.leftScale,
    lift_product entries read zero x quotient p equations data.quotientProduct,
    lift_scaling entries read zero x right next equations data.rightScale,
    lift_sum entries read zero x (quotient * p) (Hex.DensePoly.scale right next) equations data.remainder,
    lift_difference entries read zero x (Hex.DensePoly.scale left (prev * factor)) (quotient * p + Hex.DensePoly.scale right next) equations data.identity⟩

variable [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- The signed chain's exact original packing keys, cached scale/leading signs
and reached predecessor operations, retaining every positional recurrence. -/
structure ChainData (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (p f : Hex.DensePoly (Element context))
    (cert : Hex.SignedRemainderChain (Element context)) : Prop where
  head : ValueSign.LeadingData records p
  rows : ∀ r ∈ cert.chain, ValueSign.LeadingData records r
  initial : InitialData entries read p f (cert.chain.getD 1 0)
    cert.initial.leftScale cert.initial.quotient cert.initial.rightScale
  initialLeft : (ValueSign.find records cert.initial.leftScale).isSome = true
  initialRight : (ValueSign.find records cert.initial.rightScale).isSome = true
  recurrences : ∀ i < cert.steps.size,
    RecurrenceData entries read (cert.chain.getD i 0) (cert.chain.getD (i + 1) 0)
      (cert.chain.getD (i + 2) 0) (cert.steps.getD i ⟨0, 0, 0⟩).leftScale
      (cert.steps.getD i ⟨0, 0, 0⟩).quotient (cert.steps.getD i ⟨0, 0, 0⟩).rightScale
  stepLeft : ∀ i < cert.steps.size,
    (ValueSign.find records (cert.steps.getD i ⟨0, 0, 0⟩).leftScale).isSome = true
  stepRight : ∀ i < cert.steps.size,
    (ValueSign.find records (cert.steps.getD i ⟨0, 0, 0⟩).rightScale).isSome = true
  terminal : ∀ scale q, cert.terminal = some (scale, q) →
    TerminalData entries read (cert.chain.getD (cert.chain.size - 2) 0)
      (cert.chain.getD (cert.chain.size - 1) 0) scale q
  terminalSign : ∀ scale q, cert.terminal = some (scale, q) →
    (ValueSign.find records scale).isSome = true

/-- Assemble all signed-chain transport premises at the common selected point
from its retained packing/sign inventories and finite predecessor arithmetic.
No independently interpreted source chain or universal closed domain is used. -/
theorem lift_chain (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p f : Hex.DensePoly (Element context)) (cert : Hex.SignedRemainderChain (Element context))
    (data : ChainData entries records read p f cert) :
    Transport.ChainData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p f cert := by
  let x := context.finitePoint read zero unit descriptorData
  have equations (entry : Packing context) (member : entry ∈ entries) :
      eval read x entry.value.polynomial = eval read x entry.original :=
    (entry.atPoint read zero unit descriptorData (packingData entry member)).1
  refine ⟨ValueSign.lift_leading records p read zero unit descriptorData signData data.head,
    fun r member => ValueSign.lift_leading records r read zero unit descriptorData
      signData (data.rows r member),
    lift_initial entries read zero x p f _ _ _ _ equations data.initial,
    ValueSign.lookup_sign records _ read zero unit descriptorData signData data.initialLeft,
    ValueSign.lookup_sign records _ read zero unit descriptorData signData data.initialRight,
    fun i bound => lift_recurrence entries read zero x _ _ _ _ _ _ equations
      (data.recurrences i bound),
    fun i bound => ValueSign.lookup_sign records _ read zero unit descriptorData signData
      (data.stepLeft i bound),
    fun i bound => ValueSign.lookup_sign records _ read zero unit descriptorData signData
      (data.stepRight i bound),
    fun scale q produced => lift_terminal entries read zero x _ _ scale q equations
      (data.terminal scale q produced),
    fun scale q produced => ValueSign.lookup_sign records _ read zero unit descriptorData signData
      (data.terminalSign scale q produced)⟩

/-- Finite endpoint comparisons retain the original subtraction key and its
cached sign. Comparisons involving infinity perform no coefficient work. -/
@[expose] def OrderData (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) : Hex.Endpoint (Element context) → Hex.Endpoint (Element context) → Prop
  | .finite a, .finite b =>
    (Packing.find entries (a.polynomial - b.polynomial)).isSome = true ∧
      Transport.Difference read a.polynomial b.polynomial ∧
      (ValueSign.find records (a - b)).isSome = true
  | _, _ => True

/-- Lift the comparison actually reached by the interval checker at the same
point as its retained packing and sign inventories. -/
theorem lift_order (entries : List (Packing context)) (records : List (ValueSign context))
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (a b : Hex.Endpoint (Element context)) (data : OrderData entries records read a b) :
    Transport.OrderData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) a b := by
  cases a <;> cases b <;> try exact trivial
  rename_i a b
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp data.1
  refine ⟨eval_sub entry a b (Packing.find_native entries _ found).1 read zero _ data.2.1
    (entry.atPoint read zero unit descriptorData
      (packingData entry (find_mem entries _ found))).1,
    ValueSign.lookup_sign records (a - b) read zero unit descriptorData signData data.2.2⟩

/-- The exact data of both stored chains, interval comparison and every head
and recurrence endpoint of the complete Tarski query. -/
structure QueryData {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K)
    (p f : Hex.DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (cert : Hex.TarskiCertificate (Element context) (Element context) C) : Prop where
  squarefree : ChainData entries records read p 1 cert.squarefree
  remainders : ChainData entries records read p f cert.remainders
  order : OrderData entries records read a b
  lower : Packing.EndpointData entries records read p a
  upper : Packing.EndpointData entries records read p b
  lowerRows : ∀ r ∈ cert.remainders.chain, Packing.EndpointData entries records read r a
  upperRows : ∀ r ∈ cert.remainders.chain, Packing.EndpointData entries records read r b

/-- Assemble a complete query's finite premises from retained original keys,
cached signs and reached predecessor operations at one common selected point. -/
theorem lift_query {C : Type z} (entries : List (Packing context))
    (records : List (ValueSign context)) (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (signData : ∀ record ∈ records, ValueSign.Data record read)
    (p f : Hex.DensePoly (Element context)) (a b : Hex.Endpoint (Element context))
    (cert : Hex.TarskiCertificate (Element context) (Element context) C)
    (data : QueryData entries records read p f a b cert) :
    Transport.QueryData (fun a : Element context => eval read
      (context.finitePoint read zero unit descriptorData) a.polynomial)
      Element.sign (fun x : K => (SignType.sign x : Int)) p f a b cert := by
  exact ⟨lift_chain entries records read zero unit descriptorData packingData signData
      p 1 cert.squarefree data.squarefree,
    lift_chain entries records read zero unit descriptorData packingData signData
      p f cert.remainders data.remainders,
    lift_order entries records read zero unit descriptorData packingData signData a b data.order,
    Packing.lift_endpoint entries records read zero unit descriptorData packingData signData p a data.lower,
    Packing.lift_endpoint entries records read zero unit descriptorData packingData signData p b data.upper,
    fun r member => Packing.lift_endpoint entries records read zero unit descriptorData
      packingData signData r a (data.lowerRows r member),
    fun r member => Packing.lift_endpoint entries records read zero unit descriptorData
      packingData signData r b (data.upperRows r member)⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_recurrence

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_initial

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_terminal

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_productIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_productIdentity

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_chain

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_order

/-- info: 'Hex.RealClosure.Algebraic.Packing.lift_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.lift_query
