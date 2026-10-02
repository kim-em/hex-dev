/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.DagSelectedSigns
public import HexSignDet.CrossCheck
public import HexSignDet.Codec
public meta import HexSignDet.Codec
public meta import HexSignDet.DagSelectedSigns
public meta import HexSignDet.CrossCheck
public meta import HexSignDet.DagEncode

public section

/-! Selected-root signs from supplied graphs. Computational conformance owner:
`HexSignDet`. Ordinary-kernel probes use literal query and matrix evidence. -/
namespace Hex.SignDetMathlib.GraphSignsConformance

open Hex Hex.SignDet Hex.SignDet.Conformance Hex.SignDet.CrossCheck

/-- A count-one source descriptor from the existing literal kernel replay. -/
@[expose] def source : Descriptor Rat Nat Sturm.orderSign 7 := by
  have h := RawDescriptor.check_eq selected_kernel.1
  have hc : (Replay.leaf singletonNode).check Sturm.orderSign 7 singletonRaw.head
      singletonRaw.lower singletonRaw.upper singletonRaw.queries = true := by
    obtain ⟨hc, _⟩ := h.2.2
    exact hc
  exact Descriptor.ofTable singletonRaw (.leaf singletonNode) h.1 h.2.1 hc (by
    obtain ⟨_, hone⟩ := h.2.2
    exact hone)

theorem source_raw : source.raw = singletonRaw := by
  simp only [source, Descriptor.ofTable_raw]

@[expose] def emptyGraph : Dag Rat Nat := ⟨#[⟨singletonNode, none⟩], 0⟩

@[expose] def invalidNode : Node Rat Nat :=
  {derivativeNode with system := {derivativeNode.system with denominator := 0}}

@[expose] def invalidExtra : Dag Rat Nat :=
  {full with entries := full.entries.push ⟨invalidNode, none⟩}

set_option maxRecDepth 32768 in
/-- Empty queries and two different queries accept; the repeated query graph
reuses one child at both parent edges. All three replay in the ordinary kernel. -/
theorem graph_kernel :
    (emptyGraph.selectedSigns? source [] #v[]).isSome = true ∧
    (full.selectedSigns? source fullNode.queries #v[1, 1]).isSome = true ∧
    (shared.selectedSigns? source sharedParent.queries #v[1, 1]).isSome = true := by
  simp only [Dag.selectedSigns?, source_raw,
    Dag.replay_eq, Dag.step_eq, emptyGraph, full, shared,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Wrong sign claims, reordered queries, foreign contexts, forward references
and false unreachable evidence reject in the ordinary kernel. -/
theorem rejected_kernel :
    (full.selectedSigns? source fullNode.queries #v[0, 1]).isSome = false ∧
    (full.selectedSigns? source fullNode.queries.reverse #v[1, 1]).isSome = false ∧
    (({full with entries := full.entries.map fun (e : Dag.Entry Rat Nat) =>
      {e with node := {e.node with context := 8}}}).selectedSigns?
      source fullNode.queries #v[1, 1]).isSome = false ∧
    (({full with entries := full.entries.set! 2 (⟨fullNode, some (0, 2)⟩)}).selectedSigns?
      source fullNode.queries #v[1, 1]).isSome = false ∧
    (invalidExtra.selectedSigns? source fullNode.queries #v[1, 1]).isSome = false := by
  simp only [Dag.selectedSigns?, source_raw,
    Dag.replay_eq, Dag.step_eq, full, invalidExtra, invalidNode,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Exact encoders share equal subtrees and recover every input tree. -/
private def sameEvidence (left right : Replay Rat Nat) : Bool :=
  let l := Dag.encode left
  let r := Dag.encode right
  l.entries == r.entries && l.root == r.root

/-- Native byte decoding retains supplied signs and literal checked replay;
wrong values and truncated bytes fail without rerunning a producer. -/
def bytesPass : Bool :=
  let bytes := full.encodeBytes ValueCodec.rat ValueCodec.nat
  match full.selectedSigns? source fullNode.queries #v[1, 1],
      Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries #v[1, 1] bytes with
  | some expected, .ok actual =>
    actual.values == #v[1, 1] && sameEvidence actual.evidence expected.evidence &&
      (Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries
        #v[0, 1] bytes).toOption.isNone &&
      (Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries #v[1, 1]
        (bytes.extract 0 (bytes.size - 1))).toOption.isNone
  | _, _ => false

#guard bytesPass

/-- A finite sign cache validates the source descriptor separately, then checks
all selected-query graph entries. Its arbitrary fallback is never required. -/
def cachedPass : Bool :=
  let keys := full.signOperands singletonRaw.head singletonRaw.lower singletonRaw.upper ++
    (Replay.leaf singletonNode).signOperands singletonRaw.head
      singletonRaw.lower singletonRaw.upper
  match Descriptor.ofReplay? (cachedSign keys) 7 singletonRaw (.leaf singletonNode) with
  | none => false
  | some d =>
    match full.selectedSigns? d fullNode.queries #v[1, 1] with
    | none => false
    | some s => s.values == #v[1, 1]

#guard cachedPass

/-- Supplied graph replay agrees with the producer on exact small inputs,
including zero signs and an empty query list. Expected signs are evaluations
at the selected root 1 of x²−1 in (0,2). -/
def producedPass (qs : List (DensePoly Rat)) (expected : List Int) : Bool :=
  match source.buildSigns qs with
  | .error _ => false
  | .ok original =>
    let graph := Dag.encode original.evidence
    match graph.selectedSigns? source qs original.values with
    | none => false
    | some replayed => replayed.values.toList == expected &&
      sameEvidence replayed.evidence original.evidence

#guard producedPass [] []
#guard producedPass [Sturm.Fixtures.x, Sturm.Fixtures.p, 0, 1, -1] [1, 0, 0, 1, -1]

/-- info: 'Hex.SignDetMathlib.GraphSignsConformance.graph_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms graph_kernel
/-- info: 'Hex.SignDetMathlib.GraphSignsConformance.rejected_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rejected_kernel
/-- info: 'Hex.SignDet.Dag.selectedSigns_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_evidence
/-- info: 'Hex.SignDet.Dag.selectedSigns_sign_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_sign_congr
/-- info: 'Hex.SignDet.Dag.decodeSigns_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.decodeSigns_evidence
/-- info: 'Hex.SignDet.Dag.selectedSigns_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_values

end Hex.SignDetMathlib.GraphSignsConformance
