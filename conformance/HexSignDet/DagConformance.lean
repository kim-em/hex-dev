/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Conformance
public meta import HexSignDet.Dag
public meta import HexSignDet.Conformance

public section

/-! Literal graph replay and rejection tests. Computational conformance owner:
`HexSignDet`. The successful probes run through the ordinary kernel. -/
namespace Hex.SignDet.DagConformance
open Hex.SignDet.Conformance

@[expose] def full : Dag Rat Nat :=
  ⟨#[⟨firstNode, none⟩, ⟨derivativeNode, none⟩, ⟨fullNode, some (0, 1)⟩], 2⟩

@[expose] def sharedParent : Node Rat Nat :=
  {fullNode with queries := [DensePoly.C 2, DensePoly.C 2]}

@[expose] def shared : Dag Rat Nat :=
  ⟨#[⟨derivativeNode, none⟩, ⟨sharedParent, some (0, 0)⟩], 1⟩

@[expose] def check (dag : Dag Rat Nat) (qs : List (DensePoly Rat)) : Bool :=
  dag.check Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper qs

set_option maxRecDepth 32768 in
/-- Both full derivative slots are bound by graph replay in the ordinary kernel. -/
theorem full_kernel : check full (singletonRaw.full []).queries = true := by
  simp only [check, Dag.check, Dag.replay?, Dag.step, full,
    Replay.check, Node.check, checkMoment, queryPoly, Sturm.check,
    TarskiCertificate.check, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Two logical child slots share one accepted leaf; its certificate is supplied
once, while both ordered parent edges remain checked. -/
theorem shared_kernel : check shared sharedParent.queries = true := by
  simp only [check, Dag.check, Dag.replay?, Dag.step, shared,
    Replay.check, Node.check, checkMoment, queryPoly, Sturm.check,
    TarskiCertificate.check, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Missing roots and cyclic references are rejected in the ordinary kernel,
including a truncated graph whose remaining leaves themselves are valid. -/
theorem rejected_kernel :
    check ⟨#[⟨fullNode, some (0, 0)⟩], 0⟩ fullNode.queries = false ∧
    check {full with entries := full.entries.pop} fullNode.queries = false := by
  simp only [check, Dag.check, Dag.replay?, Dag.step, full,
    Replay.check, Node.check, checkMoment, queryPoly, Sturm.check,
    TarskiCertificate.check, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Checked graph evidence feeds the selected-root interface without invoking
any producer or substituting a compiled truth value for kernel replay. -/
theorem descriptor_kernel :
    (full.descriptor? Sturm.orderSign 7 (singletonRaw.full [1, 1])).isSome = true := by
  simp only [Dag.descriptor?, Dag.replay?, Dag.step, full, Replay.table_lookup,
    Replay.check, Node.check, checkMoment, queryPoly, Sturm.check,
    TarskiCertificate.check, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

#guard !check ⟨#[], 0⟩ []
#guard !check {full with root := 3} (singletonRaw.full []).queries
#guard !check {full with entries := full.entries.pop} (singletonRaw.full []).queries
#guard !check ⟨#[⟨fullNode, some (0, 0)⟩], 0⟩ fullNode.queries
#guard !check ⟨#[⟨fullNode, some (1, 2)⟩, ⟨firstNode, none⟩,
  ⟨derivativeNode, none⟩], 0⟩ fullNode.queries
#guard !check ⟨#[⟨firstNode, none⟩, ⟨derivativeNode, none⟩,
  ⟨fullNode, some (1, 0)⟩], 2⟩ fullNode.queries
#guard !check ⟨#[⟨firstNode, none⟩, ⟨derivativeNode, none⟩,
  ⟨fullNode, some (0, 0)⟩], 2⟩ fullNode.queries
#guard !check ⟨#[⟨firstNode, none⟩, ⟨derivativeNode, none⟩,
  ⟨fullNode, none⟩], 2⟩ fullNode.queries
#guard !check ⟨#[⟨{firstNode with context := 8}, none⟩,
  ⟨derivativeNode, none⟩, ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries
#guard !check ⟨#[⟨{firstNode with lower := .finite (-2)}, none⟩,
  ⟨derivativeNode, none⟩, ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries
#guard !check ⟨#[⟨{firstNode with head := -firstNode.head}, none⟩,
  ⟨derivativeNode, none⟩, ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries
#guard !check full [0, 0]
#guard !full.check Sturm.orderSign 8 singletonRaw.head singletonRaw.lower
  singletonRaw.upper fullNode.queries
/- Invalid unreachable entries are still rejected. -/
#guard !check {full with entries := full.entries.push ⟨fullNode, some (3, 3)⟩} fullNode.queries

#guard match full.descriptor? Sturm.orderSign 7 (singletonRaw.full [1, 1]) with
  | none => false
  | some d => d.raw.context == 7 && d.raw.indices == [1, 2] && d.raw.signs == [1, 1] &&
      d.raw.check Sturm.orderSign 7 d.evidence
#guard (full.descriptor? Sturm.orderSign 8 (singletonRaw.full [1, 1])).isNone
#guard (full.descriptor? Sturm.orderSign 7 (singletonRaw.full [-1, 1])).isNone
#guard (full.descriptor? Sturm.orderSign 7
  {singletonRaw.full [1, 1] with indices := [2, 2]}).isNone

/-- info: 'Hex.SignDet.Dag.check_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.check_replay
/-- info: 'Hex.SignDet.DagConformance.full_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms full_kernel
/-- info: 'Hex.SignDet.DagConformance.shared_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shared_kernel

/-- info: 'Hex.SignDet.Dag.descriptor_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.descriptor_raw
/-- info: 'Hex.SignDet.DagConformance.rejected_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejected_kernel
/-- info: 'Hex.SignDet.DagConformance.descriptor_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descriptor_kernel

end Hex.SignDet.DagConformance
