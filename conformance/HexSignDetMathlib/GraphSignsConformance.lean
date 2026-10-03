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

import all HexSignDet.Descriptor

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

@[expose] def partialRaw : RawDescriptor Rat Nat :=
  {singletonRaw with indices := [1], signs := [1]}

set_option maxRecDepth 32768 in
theorem partial_checked : partialRaw.check Sturm.orderSign 7 (.leaf firstNode) = true := by
  simp only [RawDescriptor.check, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- The first derivative sign selects the positive root. -/
@[expose] def prefixed : Descriptor Rat Nat Sturm.orderSign 7 := by
  have h := RawDescriptor.check_eq partial_checked
  have hc : (Replay.leaf firstNode).check Sturm.orderSign 7 partialRaw.head
      partialRaw.lower partialRaw.upper partialRaw.queries = true := by
    obtain ⟨hc, _⟩ := h.2.2
    exact hc
  exact Descriptor.ofTable partialRaw (.leaf firstNode) h.1 h.2.1 hc (by
    obtain ⟨_, hone⟩ := h.2.2
    exact hone)

theorem prefixed_raw : prefixed.raw = partialRaw := by
  simp only [prefixed, Descriptor.ofTable_raw]

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

/-- One graph check supplies two different singleton queries and their joint
query. Selecting a memo entry never starts another graph check. -/
@[expose] def memoPass : Bool :=
  match full.validate? Sturm.orderSign 7 source.raw.head source.raw.lower source.raw.upper with
  | none => false
  | some memo =>
    (SelectedSigns.ofMemo? source firstNode.queries #v[1] memo 0).isSome &&
    (SelectedSigns.ofMemo? source derivativeNode.queries #v[1] memo 1).isSome &&
    (SelectedSigns.ofMemo? source fullNode.queries #v[1, 1] memo 2).isSome &&
    (SelectedSigns.ofMemo? source firstNode.queries #v[-1] memo 0).isNone &&
    (SelectedSigns.ofMemo? source derivativeNode.queries #v[1] memo 0).isNone &&
    (SelectedSigns.ofMemo? source firstNode.queries #v[1] memo 3).isNone &&
    (SelectedSigns.readMemo? prefixed [DensePoly.C 2] #v[1] memo 2).isSome &&
    (SelectedSigns.readMemo? prefixed [DensePoly.C 2] #v[-1] memo 2).isNone &&
    (SelectedSigns.readMemo? prefixed [DensePoly.C 2] #v[1] memo 1).isNone &&
    (Dag.bindDomain? Sturm.orderSign 7 memo (DensePoly.C 2) source.raw.lower source.raw.upper).isNone &&
    (Dag.bindDomain? Sturm.orderSign 7 memo source.raw.head .negInf source.raw.upper).isNone &&
    (Dag.bindDomain? Sturm.orderSign 7 memo source.raw.head source.raw.lower (.finite 3)).isNone

set_option maxRecDepth 32768 in
theorem memo_kernel : memoPass = true := by
  simp only [memoPass, SelectedSigns.readMemo?, SelectedSigns.ofMemo?, Dag.bindDomain?,
    Dag.select?, Dag.validate?, source, prefixed, Descriptor.ofTable, Dag.step_eq, full,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

#guard memoPass

set_option maxRecDepth 32768 in
/-- Memo creation rejects wrong fixed bindings, cyclic children and false
unreachable evidence before any result can be extracted. -/
theorem memo_rejected :
    (full.validate? Sturm.orderSign 8 singletonRaw.head singletonRaw.lower singletonRaw.upper).isNone = true ∧
    (full.validate? Sturm.orderSign 7 (DensePoly.C 2) singletonRaw.lower singletonRaw.upper).isNone = true ∧
    (full.validate? Sturm.orderSign 7 singletonRaw.head .negInf singletonRaw.upper).isNone = true ∧
    (full.validate? Sturm.orderSign 7 singletonRaw.head singletonRaw.lower (.finite 3)).isNone = true ∧
    (({full with entries := full.entries.set! 0 (⟨firstNode, some (1, 1)⟩)}).validate?
      Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper).isNone = true ∧
    (invalidExtra.validate? Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper).isNone = true := by
  simp only [Dag.validate?, Dag.step_eq, full, invalidExtra, invalidNode,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Wrong sign claims, reordered queries, foreign contexts, forward/self
references and false unreachable evidence reject in the ordinary kernel. -/
theorem rejected_kernel :
    (full.selectedSigns? source fullNode.queries #v[0, 1]).isSome = false ∧
    (full.selectedSigns? source fullNode.queries.reverse #v[1, 1]).isSome = false ∧
    (({full with entries := full.entries.map fun (e : Dag.Entry Rat Nat) =>
      {e with node := {e.node with context := 8}}}).selectedSigns?
      source fullNode.queries #v[1, 1]).isSome = false ∧
    (({full with entries := full.entries.set! 2 (⟨fullNode, some (0, 2)⟩)}).selectedSigns?
      source fullNode.queries #v[1, 1]).isSome = false ∧
    (({full with entries := full.entries.set! 0 (⟨firstNode, some (1, 1)⟩)}).selectedSigns?
      source fullNode.queries #v[1, 1]).isSome = false ∧
    (invalidExtra.selectedSigns? source fullNode.queries #v[1, 1]).isSome = false := by
  simp only [Dag.selectedSigns?, source_raw,
    Dag.replay_eq, Dag.step_eq, full, invalidExtra, invalidNode,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

@[expose] def equivalentPrefix : Dag Rat Nat :=
  let replacement : Dag.Entry Rat Nat :=
    ⟨{fullNode with queries := [Sturm.Fixtures.x, DensePoly.C 2]}, some (0, 1)⟩
  {full with entries := full.entries.set! 2 replacement}

set_option maxRecDepth 32768 in
/-- Nonempty descriptor prefixes must be present literally. A graph for only
the added query, or a sign-equivalent replacement derivative, is insufficient. -/
theorem prefix_kernel :
    (full.selectedSigns? prefixed [DensePoly.C 2] #v[1]).isSome = true ∧
    ((⟨#[⟨derivativeNode, none⟩], 0⟩ : Dag Rat Nat).selectedSigns?
      prefixed [DensePoly.C 2] #v[1]).isSome = false ∧
    (equivalentPrefix.selectedSigns? prefixed [DensePoly.C 2] #v[1]).isSome = false := by
  simp only [Dag.selectedSigns?, prefixed_raw,
    Dag.replay_eq, Dag.step_eq, full, equivalentPrefix,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Both signs of X occur in the whole-line table for X²−1. The first derivative
prefix selects +1; claiming the negative root's row must reject. -/
def wholeLinePass : Bool :=
  match Descriptor.validate Sturm.orderSign 7
      {partialRaw with lower := .negInf, upper := .posInf} with
  | none => false
  | some d =>
    match d.buildSigns [Sturm.Fixtures.x] with
    | .error _ => false
    | .ok s =>
      let graph := Dag.encode s.evidence
      let bytes := graph.encodeBytes ValueCodec.rat ValueCodec.nat
      (graph.selectedSigns? d [Sturm.Fixtures.x] #v[1]).isSome &&
        (graph.selectedSigns? d [Sturm.Fixtures.x] #v[-1]).isNone &&
        (Dag.decodeSigns ValueCodec.rat ValueCodec.nat d [Sturm.Fixtures.x]
          #v[1] bytes).toOption.isSome &&
        (Dag.decodeSigns ValueCodec.rat ValueCodec.nat d [Sturm.Fixtures.x]
          #v[-1] bytes).toOption.isNone &&
        s.evidence.node.system.tableRows.toList.any (fun row => row.1 == [-1, -1])

#guard wholeLinePass

/-- Compare literal trees through their injective shared encoding. -/
private def sameEvidence (left right : Replay Rat Nat) : Bool :=
  let l := Dag.encode left
  let r := Dag.encode right
  l.entries == r.entries && l.root == r.root

/-- Byte decoding retains supplied signs and literal checked replay;
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
        (bytes.extract 0 (bytes.size - 2))).toOption.isNone &&
      (match Dag.decodeSigns ValueCodec.rat ValueCodec.nat source fullNode.queries #v[1, 1]
          (bytes.extract 0 (bytes.size - 1)) with
        | .ok shortened => shortened.values == actual.values &&
          sameEvidence shortened.evidence actual.evidence
        | .error _ => false)
  | _, _ => false

#guard bytesPass

@[expose] def keys : List Rat :=
  full.signOperands source.raw.head source.raw.lower source.raw.upper ++
    source.evidence.signOperands source.raw.head source.raw.lower source.raw.upper

/-- Source validation is also transferred using its own finite dependencies. -/
@[expose] def cachedSource : Descriptor Rat Nat (cachedSign keys) 7 := by
  have he := source.evidence.check_sign_congr (cachedSign keys) Sturm.orderSign 7
    source.raw.head source.raw.lower source.raw.upper source.raw.queries
    (fun x hx => cachedSign_agrees keys x (by simp only [keys, List.mem_append]; exact Or.inr hx))
  have hc : source.raw.check (cachedSign keys) 7 source.evidence = true := by
    simpa only [RawDescriptor.check, he] using source.accepted
  have h := RawDescriptor.check_eq hc
  have ht : source.evidence.check (cachedSign keys) 7 source.raw.head
      source.raw.lower source.raw.upper source.raw.queries = true := by
    obtain ⟨ht, _⟩ := h.2.2
    exact ht
  exact Descriptor.ofTable source.raw source.evidence h.1 h.2.1 ht (by
    obtain ⟨_, hone⟩ := h.2.2
    exact hone)

theorem cachedSource_raw : cachedSource.raw = source.raw := by
  simp only [cachedSource, Descriptor.ofTable_raw]

/-- Finite agreement transfers selected-query acceptance in the ordinary kernel
without assuming a lawful sign function outside the source and graph keys. -/
theorem cached_kernel :
    (full.selectedSigns? cachedSource fullNode.queries #v[1, 1]).isSome = true := by
  have he := full.selectedSigns_sign_congr (cachedSign keys) Sturm.orderSign 7
    cachedSource source cachedSource_raw.symm fullNode.queries #v[1, 1]
    (fun x hx => cachedSign_agrees keys x (by
      simp only [keys, List.mem_append]
      exact Or.inl (by simpa only [cachedSource_raw] using hx)))
  have hs := congrArg Option.isSome he
  simp only [Option.isSome_map] at hs
  rw [hs]
  exact graph_kernel.2.1

/-- A finite sign cache validates the source descriptor separately, then checks
all selected-query graph entries. Outside-key behavior is not assumed lawful. -/
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
/-- info: 'Hex.SignDetMathlib.GraphSignsConformance.prefix_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prefix_kernel
/-- info: 'Hex.SignDetMathlib.GraphSignsConformance.cached_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cached_kernel
/-- info: 'Hex.SignDet.Dag.selectedSigns_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_checked
/-- info: 'Hex.SignDet.Dag.selectedSigns_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_replay
/-- info: 'Hex.SignDet.Dag.selectedSigns_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_encode
/-- info: 'Hex.SignDet.Dag.selectedSigns_encode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.selectedSigns_encode_eq
/-- info: 'Hex.SignDet.Dag.decodeSigns_sign_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Dag.decodeSigns_sign_congr
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

/-- info: 'Hex.SignDet.Dag.memo_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.memo_values

/-- info: 'Hex.SignDet.Dag.readMemo_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dag.readMemo_values

/-- info: 'Hex.SignDetMathlib.GraphSignsConformance.memo_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDetMathlib.GraphSignsConformance.memo_kernel

/-- info: 'Hex.SignDetMathlib.GraphSignsConformance.memo_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDetMathlib.GraphSignsConformance.memo_rejected
