/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FactReplay
public meta import HexRealClosureMathlib.FactReplay
public import HexSignDet.DependenciesCodec
public meta import HexSignDet.DependenciesCodec
public import HexRealClosureMathlib.SignEvidenceConformance
public meta import HexRealClosureMathlib.SignEvidenceConformance

public section

namespace Hex.RealClosure.Algebraic.DependenciesConformance
open SignDet CoefficientSignsConformance SignEvidenceConformance SignFactsConformance

/-- Actual proved scalar facts in the two distinct coefficient fields. -/
inductive Result (entry : Dependencies.Entry) where
  | lower (level : entry.level = 0) (facts : List (SignFact context))
  | upper (level : entry.level = 1) (facts : List (SignFact NestedSignsConformance.next))

def signs {entry : Dependencies.Entry} : Result entry → List Int
  | .lower _ facts => facts.map SignFact.sign
  | .upper _ facts => facts.map SignFact.sign

/-- Bind the selected root and the exact ordered polynomial requests. -/
def subject {E : Type} [Zero E] [DecidableEq E] (value : ValueCodec E)
    (raw : RawDescriptor E Nat) (queries : List (DensePoly E)) : Codec.Json :=
  .arr #[SignRequests.binding value ValueCodec.nat raw, Codec.list (Codec.poly value) queries]

/-- This reader keeps the native upper context while using only its declared
lower child's facts for coefficient decoding and supplies them to arithmetic.
Compiled arithmetic retains its native fallback. -/
def decodeUpperWith (facts : List (SignFact context)) (value : ValueCodec (Element context))
    (required : List (DensePoly (Element context))) (bytes : ByteArray) :=
  NestedSignsConformance.next.decodeEvidenceWith upperEmbedding
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
      (fun _ _ => Rat.cast_div _ _))
    (Element.cachedOne PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedNeg PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedInv PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedDiv PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedNatCast PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedOne_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedAdd_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedNeg_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedSub_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedMul_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedInv_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedDiv_eq PackingConformance.reduction PackingConformance.reduction_eq facts)
    (Element.cachedNatCast_eq PackingConformance.reduction PackingConformance.reduction_eq facts) value ValueCodec.nat required bytes

/-- The existing mathematical readers check each local graph. The upper
coefficient reader uses only the declared lower packet's proved facts. -/
def read (lowerRequests : List (Codec.Json × List (DensePoly Rat)))
    (upperSubject₁ upperSubject₂ : Codec.Json)
    (queries₁ queries₂ : List (DensePoly (Element context)))
    (entry : Dependencies.Entry) (children : Array (Dependencies.Checked Result)) :
    Option (Result entry) := do
  if level : entry.level = 0 then
    if !children.isEmpty then none else
      let request ← lowerRequests.find? (fun request => entry.subject == request.1)
      let facts ← (decode ValueCodec.rat request.2 entry.payload.writeBytes).toOption
      return .lower level facts.toList
  else if level : entry.level = 1 then
    if children.size != 1 then none else
      let child ← children[0]?
      match child.value with
      | .upper _ _ => none
      | .lower _ facts =>
        let reader := Element.signCodec ValueCodec.rat facts
        let queries ← if entry.subject == upperSubject₁ then some queries₁
          else if entry.subject == upperSubject₂ then some queries₂ else none
        let facts ← (decodeUpperWith facts reader queries entry.payload.writeBytes).toOption
        return .upper level facts.toList
  else none

/-- Separately produced upper packets share one checked lower packet.
All three pass the outer byte reader and the existing mathematical readers.
Contexts are already validated; equal supplied-fact operations preserve
ordinary arithmetic, including its compiled native fallback. -/
def checks : Option (List (String × Bool)) := do
  let qs₁ := [NestedSignsConformance.unitPoly, NestedSignsConformance.nextQuery,
    0, NestedSignsConformance.unitPoly]
  let qs₂ := [NestedSignsConformance.nextQuery]
  let signs₁ ← (NestedSignsConformance.next.buildSigns qs₁).toOption
  let signs₂ ← (NestedSignsConformance.next.buildSigns qs₂).toOption
  let packet₁ := SignEvidence.ofSigns signs₁
  let packet₂ := SignEvidence.ofSigns signs₂
  let coefficients := SignEvidence.coefficients NestedSignsConformance.next.root.raw packet₁ ++
    SignEvidence.coefficients NestedSignsConformance.next.root.raw packet₂
  let keys := Element.signKeys coefficients
  let lower ← (context.buildEvidence keys).toOption
  let lowerCodec := SignEvidence.codec ValueCodec.rat ValueCodec.nat source.raw
  let lowerFacts ← (decode ValueCodec.rat keys (lowerCodec.encodeBytes lower)).toOption
  let reader := Element.signCodec ValueCodec.rat lowerFacts.toList
  let upperCodec := SignEvidence.codec reader ValueCodec.nat NestedSignsConformance.next.root.raw
  let subject₀ := subject ValueCodec.rat source.raw keys
  let subject₁ := subject reader NestedSignsConformance.next.root.raw qs₁
  let subject₂ := subject reader NestedSignsConformance.next.root.raw qs₂
  let ref₀ : Dependencies.Reference := ⟨0, 0, subject₀⟩
  let ref₁ : Dependencies.Reference := ⟨1, 1, subject₁⟩
  let ref₂ : Dependencies.Reference := ⟨2, 1, subject₂⟩
  let entry₀ : Dependencies.Entry := ⟨0, subject₀, lowerCodec.encode lower, #[]⟩
  let entry₁ : Dependencies.Entry := ⟨1, subject₁, upperCodec.encode packet₁, #[ref₀]⟩
  let entry₂ : Dependencies.Entry := ⟨1, subject₂, upperCodec.encode packet₂, #[ref₀]⟩
  let graph : Dependencies.Graph := ⟨#[entry₀, entry₁, entry₂], #[ref₁, ref₁, ref₂]⟩
  let required := graph.roots.map fun root => (root.level, root.subject)
  let incompleteKeys := keys.filter (· != stored)
  let incompleteSubject := subject ValueCodec.rat source.raw incompleteKeys
  let localReader := read [(subject₀, keys), (incompleteSubject, incompleteKeys)]
    subject₁ subject₂ qs₁ qs₂
  let decodeGraph := fun graph => Dependencies.Graph.decode localReader required
    (Dependencies.Graph.codec.encodeBytes graph)
  let decoded ← (decodeGraph graph).toOption
  let memo := decoded.memo
  let bad := {lower with values := lower.values.map (· + 1)}
  let falseEntry := {entry₀ with payload := lowerCodec.encode bad}
  let falseLower := {graph with entries := graph.entries.set! 0 falseEntry}
  let falseUnused := {graph with entries := graph.entries.push falseEntry}
  let incomplete ← (context.buildEvidence incompleteKeys).toOption
  let incompleteEntry : Dependencies.Entry := ⟨0, incompleteSubject, lowerCodec.encode incomplete, #[]⟩
  let incompleteRef : Dependencies.Reference := ⟨0, 0, incompleteSubject⟩
  let incompleteUpper₁ := {entry₁ with children := #[incompleteRef]}
  let incompleteUpper₂ := {entry₂ with children := #[incompleteRef]}
  let incompleteChild := {graph with entries :=
    #[incompleteEntry, incompleteUpper₁, incompleteUpper₂]}
  let standalone : Dependencies.Graph := ⟨#[incompleteEntry], #[incompleteRef]⟩
  let childAccepted := (Dependencies.Graph.decode localReader #[(0, incompleteSubject)]
    (Dependencies.Graph.codec.encodeBytes standalone)).toOption.isSome
  let foreignCodec := SignEvidence.codec ValueCodec.rat ValueCodec.nat
    {source.raw with context := 9}
  let foreignEntry := {entry₀ with payload := foreignCodec.encode lower}
  let foreignChild := {graph with entries := graph.entries.set! 0 foreignEntry}
  let missing := {graph with entries := graph.entries.set! 1 ({entry₁ with children := #[]})}
  let forwardEntry := {entry₁ with children := #[⟨2, 0, subject₀⟩]}
  let cycleEntry := {entry₁ with children := #[⟨1, 0, subject₀⟩]}
  let levelEntry := {entry₁ with children := #[⟨0, 1, subject₀⟩]}
  let staleEntry := {entry₁ with children := #[{ref₀ with subject := .null}]}
  let forward := {graph with entries := graph.entries.set! 1 forwardEntry}
  let cycle := {graph with entries := graph.entries.set! 1 cycleEntry}
  let sameLevel := {graph with entries := graph.entries.set! 1 levelEntry}
  let stale := {graph with entries := graph.entries.set! 1 staleEntry}
  let truncated := {graph with entries := #[entry₁, entry₂]}
  let changedRoot := {graph with roots := #[{ref₁ with subject := .null}, ref₁, ref₂]}
  let bytes := Dependencies.Graph.codec.encodeBytes graph
  let fields ← (Dependencies.Graph.codec.encode graph).getArr?.toOption
  let unknownVersion := Codec.Json.arr (fields.set! 0 (Codec.Json.of (2 : Nat)))
  return [
    ("proved signs", memo.toList.map (fun result => signs result.value) ==
      [lowerFacts.toList.map SignFact.sign, [1, 1, 0, 1], [1]]),
    ("shared packets and results", memo.size == 3 && graph.roots.size == 3),
    ("exact literals", memo.map Dependencies.Checked.entry == graph.entries),
    ("selected shared results", decoded.results.toList.map (fun result => signs result.value) ==
      [[1, 1, 0, 1], [1, 1, 0, 1], [1]]),
    ("false child", (decodeGraph falseLower).toOption.isNone),
    ("false unused packet", falseUnused.check && (decodeGraph falseUnused).toOption.isNone),
    ("independently valid incomplete child", keys.contains stored && stored != 0 &&
      childAccepted && incompleteChild.check && (decodeGraph incompleteChild).toOption.isNone),
    ("foreign payload context", foreignChild.check && (decodeGraph foreignChild).toOption.isNone),
    ("missing child", missing.check && (decodeGraph missing).toOption.isNone),
    ("forward reference", !forward.check && (decodeGraph forward).toOption.isNone),
    ("cycle", !cycle.check && (decodeGraph cycle).toOption.isNone),
    ("same level", !sameLevel.check && (decodeGraph sameLevel).toOption.isNone),
    ("stale binding", !stale.check && (decodeGraph stale).toOption.isNone),
    ("truncated graph", (decodeGraph truncated).toOption.isNone),
    ("changed root binding", (decodeGraph changedRoot).toOption.isNone),
    ("ordered caller subjects", (Dependencies.Graph.decode localReader required.reverse
      bytes).toOption.isNone),
    ("unknown byte version", (Dependencies.Graph.decode localReader required
      unknownVersion.writeBytes).toOption.isNone),
    ("truncated outer bytes", (Dependencies.Graph.decode localReader required
      (bytes.extract 0 (bytes.size - 2))).toOption.isNone)]

def passes : Bool := checks.map (fun results => results.all (·.2)) == some true

#guard passes

/-- Reader results may inhabit a larger universe than the serialized data. -/
example (required : Array (Nat × Codec.Json)) (bytes : ByteArray) :
    Except String (Dependencies.Decoded (fun _ => ULift.{1} Unit) required) :=
  Dependencies.Graph.decode (fun _ _ => some ⟨()⟩) required bytes

end Hex.RealClosure.Algebraic.DependenciesConformance
