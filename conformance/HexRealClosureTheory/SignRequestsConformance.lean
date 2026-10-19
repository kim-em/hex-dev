/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.SignRequests
public meta import HexRealClosureTheory.SignRequests
public import HexRealClosureTheory.SignFactsConformance
public meta import HexRealClosureTheory.SignFactsConformance
public meta import HexSignDet.CrossCheck

public section

namespace Hex.RealClosure.Algebraic.SignRequestsConformance
open SignDet SignDet.Conformance SignDet.CrossCheck
open CoefficientSignsConformance PackingConformance SignFactsConformance

@[expose] def requests : Array (SignRequest Rat) :=
  #[⟨stored, 1, 0⟩, ⟨2 * Sturm.Fixtures.x, 1, 1⟩]

@[expose] def reader := SignRequests.codec ValueCodec.rat ValueCodec.nat source.raw

theorem roundtrip_kernel : reader.decode (reader.encode requests) = .ok requests :=
  SignRequests.codec_roundtrip _ _ _ _ (ValueCodec.nat_lawful _)
    (fun x _ => ValueCodec.rat_lawful x)
    (fun x _ => ValueCodec.rat_lawful x)
    (fun x _ => ValueCodec.rat_lawful x)
    (fun _ _ x _ => ValueCodec.rat_lawful x)

@[expose] def decode
    (memo : Array (Dag.Checked Sturm.orderSign 7 source.raw.head source.raw.lower source.raw.upper))
    (bytes : ByteArray) : Except String (Array (SignFact context)) :=
  context.decodeRequests (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
    ValueCodec.rat ValueCodec.nat memo bytes

def bytesPass : Bool :=
  (do
    let supplied ← (source.buildSigns [stored, 2 * Sturm.Fixtures.x]).toOption
    let graph := Dag.encode supplied.evidence
    let memo ← graph.validate? Sturm.orderSign 7 source.raw.head source.raw.lower source.raw.upper
    let bytes := reader.encodeBytes requests
    let facts ← (decode memo bytes).toOption
    let coefficients := Element.signCodec ValueCodec.rat facts.toList
    let a ← (coefficients.decode ((Element.codec ValueCodec.rat).encode literal)).toOption
    let b ← (coefficients.decode ((Element.codec ValueCodec.rat).encode small)).toOption
    let wrong := requests.set! 1 ⟨2 * Sturm.Fixtures.x, -1, 1⟩
    let missing := requests.set! 1 ⟨2 * Sturm.Fixtures.x, 1, 3⟩
    let changed := fun raw => (SignRequests.codec ValueCodec.rat ValueCodec.nat raw).encodeBytes requests
    let empty ← (decode memo (reader.encodeBytes #[])).toOption
    let duplicates ← (decode memo (reader.encodeBytes (requests ++ requests))).toOption
    pure (a == literal && b == small && facts.size == requests.size && duplicates.size == 4 &&
      (decode memo (reader.encodeBytes wrong)).toOption.isNone &&
      (decode memo (reader.encodeBytes missing)).toOption.isNone &&
      (decode memo (changed {source.raw with context := 8})).toOption.isNone &&
      (decode memo (changed {source.raw with head := 2 * source.raw.head})).toOption.isNone &&
      (decode memo (changed {source.raw with upper := .finite 3})).toOption.isNone &&
      (decode memo (changed {source.raw with lower := .finite (-1)})).toOption.isNone &&
      (decode memo (changed {source.raw with signs := [1]})).toOption.isNone &&
      (decode memo (changed {source.raw with indices := [1], signs := [1]})).toOption.isNone &&
      (decode memo (bytes.extract 0 (bytes.size - 2))).toOption.isNone &&
      empty.isEmpty &&
      ((Element.signCodec ValueCodec.rat empty.toList).decode
        ((Element.codec ValueCodec.rat).encode literal)).toOption.isNone)) == some true

#guard bytesPass

@[expose] def readAt (selected : Context Rat Nat Sturm.orderSign 7)
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (memo : Array (Dag.Checked Sturm.orderSign 7 head lower upper)) (request : SignRequest Rat) :
    Option (SignFact selected) :=
  selected.readRequest? (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) memo request

/-- Both roots have a derivative prefix. All signs come from the same joint
entry; its individual child entries do not contain the complete prefix. -/
def jointPass : Bool :=
  (do
    let raw := {partialRaw with lower := .negInf, upper := .posInf}
    let positive ← Descriptor.validate Sturm.orderSign 7 raw
    let negative ← Descriptor.validate Sturm.orderSign 7 {raw with signs := [-1]}
    let supplied ← (positive.buildSigns [stored, Sturm.Fixtures.x - 1]).toOption
    let graph := Dag.encode supplied.evidence
    let memo ← graph.validate? Sturm.orderSign 7 raw.head raw.lower raw.upper
    let pos := Context.adjoin positive (fun _ => true)
    let neg := Context.adjoin negative (fun _ => true)
    pure ((readAt pos memo ⟨stored, 1, graph.root⟩).isSome &&
      (readAt pos memo ⟨Sturm.Fixtures.x - 1, 0, graph.root⟩).isSome &&
      (readAt neg memo ⟨stored, -1, graph.root⟩).isSome &&
      (readAt neg memo ⟨Sturm.Fixtures.x - 1, -1, graph.root⟩).isSome &&
      (readAt pos memo ⟨stored, -1, graph.root⟩).isNone &&
      (readAt pos memo ⟨stored + 1, 1, graph.root⟩).isNone)) == some true

#guard jointPass

@[expose] def decodeUpper (value : ValueCodec (Element context))
    (memo : Array (Dag.Checked Element.sign 8 NestedSignsConformance.root.raw.head
      NestedSignsConformance.root.raw.lower NestedSignsConformance.root.raw.upper))
    (bytes : ByteArray) : Except String (Array (SignFact NestedSignsConformance.next)) :=
  NestedSignsConformance.next.decodeRequests upperEmbedding
    (Element.denote_eq_zero (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_one (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_add (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_sub (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_mul (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_nat (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.sign_spec (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_neg (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _))
    (Element.denote_inv (fun q : Rat => (q : ℝ))
      (fun _ => Rat.cast_eq_zero) (by simp) (fun _ _ => Rat.cast_add _ _)
      (fun _ _ => Rat.cast_sub _ _) (fun _ _ => Rat.cast_mul _ _)
      (fun _ => by simp) rational_sign (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _)
      (fun _ _ => Rat.cast_div _ _)) value ValueCodec.nat memo bytes

@[expose] def negOneFact : SignFact context :=
  ⟨DensePoly.C (-1), -1, by
    rw [context.signPoly_const _ (by decide +kernel)]
    decide +kernel⟩

/-- Lower requests establish the literal coefficient needed by the upper
request packet's own root binding and query. Omitting that fact rejects bytes
before an upper sign can be restored. Both graphs are produced outside replay. -/
def nestedBytesPass : Bool :=
  (do
    let lowerSigns ← (source.buildSigns [stored, 2 * Sturm.Fixtures.x]).toOption
    let lowerGraph := Dag.encode lowerSigns.evidence
    let lowerMemo ← lowerGraph.validate? Sturm.orderSign 7 source.raw.head
      source.raw.lower source.raw.upper
    let lowerFacts ← (decode lowerMemo (reader.encodeBytes requests)).toOption
    let lowerReader := Element.signCodec ValueCodec.rat
      (lowerFacts.toList ++ [SignCodecConformance.oneFact, negOneFact])
    let polynomial := DensePoly.ofCoeffs #[NestedSignsConformance.rational 0, small]
    let upperSigns ← (NestedSignsConformance.next.buildSigns [polynomial]).toOption
    let leaf ← match upperSigns.evidence with
      | .leaf node => some node
      | .split .. => none
    let graph : Dag (Element context) Nat := ⟨#[⟨leaf, none⟩], 0⟩
    let upperMemo ← graph.validate? Element.sign 8 NestedSignsConformance.root.raw.head
      NestedSignsConformance.root.raw.lower NestedSignsConformance.root.raw.upper
    let refs : Array (SignRequest (Element context)) := #[⟨polynomial, 1, 0⟩]
    let upperWire := SignRequests.codec lowerReader ValueCodec.nat NestedSignsConformance.root.raw
    let bytes := upperWire.encodeBytes refs
    let upperFacts ← (decodeUpper lowerReader upperMemo bytes).toOption
    let valueReader := Element.signCodec lowerReader upperFacts.toList
    let encoded := (Element.codec (Element.codec ValueCodec.rat)).encode
      (Element.ofPoly polynomial : Element NestedSignsConformance.next)
    let restored ← (valueReader.decode encoded).toOption
    let storedFact ← lowerFacts[0]?
    let missing := Element.signCodec ValueCodec.rat
      [storedFact, SignCodecConformance.oneFact, negOneFact]
    let wrong : Array (SignRequest (Element context)) := #[⟨polynomial, -1, 0⟩]
    pure (restored.polynomial == polynomial && Element.sign restored == 1 &&
      upperFacts.size == 1 &&
      (SignRequests.readBinding missing ValueCodec.nat NestedSignsConformance.root.raw
        (SignRequests.binding lowerReader ValueCodec.nat NestedSignsConformance.root.raw)).toOption.isSome &&
      (decodeUpper missing upperMemo bytes).toOption.isNone &&
      (decodeUpper lowerReader upperMemo (upperWire.encodeBytes wrong)).toOption.isNone)) == some true

#guard nestedBytesPass

/-- info: 'Hex.RealClosure.Algebraic.SignRequestsConformance.roundtrip_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms roundtrip_kernel

/-- info: 'Hex.RealClosure.Algebraic.SignRequestsConformance.bytesPass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bytesPass

/-- info: 'Hex.RealClosure.Algebraic.Context.readRequest?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Context.readRequest?

/-- info: 'Hex.RealClosure.Algebraic.Context.decodeRequests_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Context.decodeRequests_evidence

/-- info: 'Hex.RealClosure.Algebraic.Context.readRequests_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Context.readRequests_fields

/-- info: 'Hex.RealClosure.Algebraic.SignRequests.codec_bytes_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignRequests.codec_bytes_roundtrip

/-- info: 'Hex.RealClosure.Algebraic.SignRequestsConformance.nestedBytesPass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nestedBytesPass

end Hex.RealClosure.Algebraic.SignRequestsConformance
