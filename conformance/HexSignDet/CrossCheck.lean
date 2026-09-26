/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Conformance
public meta import HexSignDet.Dag
public meta import HexSignDet.DagEncode
public meta import HexSignDet.DagReplay
public meta import HexSignDet.DagExpand
public meta import HexSignDet.Conformance

public section

/-! Literal graph replay and rejection tests. Computational conformance owner:
`HexSignDet`. The successful probes run through the ordinary kernel. -/
namespace Hex.SignDet.CrossCheck
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
  simp only [check, Dag.check, Dag.replay_eq, Dag.step_eq, full,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Two logical child slots share one accepted leaf; its certificate is supplied
once, while both ordered parent edges remain checked. -/
theorem shared_kernel : check shared sharedParent.queries = true := by
  simp only [check, Dag.check, Dag.replay_eq, Dag.step_eq, shared,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Missing roots and cyclic references are rejected in the ordinary kernel,
including a truncated graph whose remaining leaves themselves are valid. -/
theorem rejected_kernel :
    check ⟨#[⟨fullNode, some (0, 0)⟩], 0⟩ fullNode.queries = false ∧
    check {full with entries := full.entries.pop} fullNode.queries = false := by
  simp only [check, Dag.check, Dag.replay_eq, Dag.step_eq, full,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Checked graph evidence feeds the selected-root interface without invoking
any producer or substituting a compiled truth value for kernel replay. -/
theorem descriptor_kernel :
    (full.descriptor? Sturm.orderSign 7 (singletonRaw.full [1, 1])).isSome = true := by
  simp only [Dag.descriptor?, Dag.replay_eq, Dag.step_eq, full, Replay.table_lookup,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

-- The first query supplies a valid shared domain. Later queries with distinct
-- valid witnesses fall back to full replay; invalid witnesses are rejected.
#guard let alternate := {constantQuery 2 with squarefree :=
    {Sturm.Fixtures.literalChain with initial := ⟨2, 0, 4⟩}}
  let valid := {derivativeNode with
    moments := #v[singletonQuery, alternate, constantQuery 4]}
  let invalid := {valid with moments := #v[singletonQuery,
    {alternate with squarefree := {alternate.squarefree with terminal := none}}, constantQuery 4]}
  check ⟨#[⟨valid, none⟩], 0⟩ valid.queries &&
    !check ⟨#[⟨invalid, none⟩], 0⟩ invalid.queries

/-- info: 'Hex.SignDet.checkMoment_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkMoment_eq
/-- info: 'Hex.SignDet.Node.check_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Node.check_eq

#guard !check ⟨#[], 0⟩ []

-- Encoding preserves first-occurrence order and shares the repeated leaf.
#guard let encoded := Dag.encode (.split fullNode (.leaf firstNode) (.leaf derivativeNode))
  encoded.entries == full.entries && encoded.root == full.root && check encoded fullNode.queries
#guard let encoded := Dag.encode (.split sharedParent (.leaf derivativeNode) (.leaf derivativeNode))
  encoded.entries == shared.entries && encoded.root == shared.root && check encoded sharedParent.queries

-- These entries collide under the encoder hash but have distinct literal
-- inverse witnesses. Deduplication must not replace the bad child with the good
-- one, even though their queries, columns and claimed counts are identical.
@[expose] def badDenominator : Node Rat Nat :=
  {derivativeNode with system :=
    {derivativeNode.system with denominator := derivativeNode.system.denominator + 1}}

set_option maxRecDepth 32768 in
/-- The general encoding theorem also preserves rejection of a literal forged
inverse witness. The tree rejection is checked by the ordinary kernel. -/
theorem encoded_rejected_kernel :
    check (Dag.encode (.split sharedParent (.leaf derivativeNode) (.leaf badDenominator)))
      sharedParent.queries = false := by
  unfold check
  rw [Dag.check_encode_eq]
  simp only [Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- Structural expansion retains the forged witness, without assuming that
its replay is accepted or evaluating any coefficient-sign callback. -/
theorem invalid_roundtrip :
    Dag.expand? (Dag.encode (.leaf badDenominator)) = some (.leaf badDenominator) :=
  Dag.expand_encode _

set_option maxRecDepth 32768 in
/-- Upstream literal certificate equality reduces in the ordinary kernel,
including complete query chains and rank witnesses. -/
theorem equality_kernel :
    decide (singletonQuery = singletonQuery) = true ∧
    decide (singletonQuery = constantQuery 2) = false ∧
    decide (derivativeNode.basis = derivativeNode.basis) = true ∧
    decide (derivativeNode.basis = {derivativeNode.basis with denom := 0}) = false ∧
    decide (derivativeNode.system = derivativeNode.system) = true ∧
    decide (derivativeNode.moments = derivativeNode.moments) = true ∧
    decide (derivativeNode.reductions = derivativeNode.reductions) = true ∧
    decide (derivativeNode = derivativeNode) = true ∧
    decide (derivativeNode = badDenominator) = false := by
  decide +kernel

@[expose] def constantStep (q : DensePoly Rat) : ReductionStep Rat :=
  ⟨0, q, ⟨1, 0, 1⟩⟩

@[expose] def reductionNode : Node Rat Nat :=
  {derivativeNode with
    preparation := some ⟨[constantStep 2]⟩
    reductions := #v[some ⟨[], 1⟩, some ⟨[constantStep 2], 2⟩,
      some ⟨[constantStep 2, constantStep 4], 4⟩]}

set_option maxRecDepth 32768 in
/-- Nonempty reduction and preparation records reach every inner equality
instance. The complete literal node also passes ordinary-kernel replay. -/
theorem reduction_kernel :
    decide (reductionNode = reductionNode) = true ∧
    decide (reductionNode = {reductionNode with preparation := some ⟨[constantStep 4]⟩}) = false ∧
    (Replay.leaf reductionNode).check Sturm.orderSign 7 singletonRaw.head
      singletonRaw.lower singletonRaw.upper reductionNode.queries = true := by
  simp only [Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

-- Run the structural expander itself, including invalid unreachable entries.
#guard match full.expand? with
  | some (.split n (.leaf l) (.leaf r)) => n == fullNode && l == firstNode && r == derivativeNode
  | _ => false
#guard match shared.expand? with
  | some (.split n (.leaf l) (.leaf r)) => n == sharedParent && l == derivativeNode && r == derivativeNode
  | _ => false
#guard (Dag.expand? (⟨#[⟨fullNode, some (0, 0)⟩], 0⟩ : Dag Rat Nat)).isNone
#guard (Dag.expand? (⟨#[⟨fullNode, some (1, 2)⟩, ⟨firstNode, none⟩,
  ⟨derivativeNode, none⟩], 0⟩ : Dag Rat Nat)).isNone
#guard ({full with root := 3} : Dag Rat Nat).expand?.isNone
#guard ({full with entries := full.entries.push ⟨fullNode, some (3, 3)⟩} : Dag Rat Nat).expand?.isNone
#guard ({full with entries := full.entries.push ⟨badDenominator, none⟩} : Dag Rat Nat).expand?.isSome
#guard check {full with entries := full.entries.push ⟨derivativeNode, none⟩} fullNode.queries
#guard !check {full with entries := full.entries.push ⟨badDenominator, none⟩} fullNode.queries
#guard !check {full with entries := full.entries.push ⟨derivativeNode, some (0, 1)⟩} fullNode.queries

#guard hash (⟨derivativeNode, none⟩ : Dag.Entry Rat Nat) ==
  hash (⟨badDenominator, none⟩ : Dag.Entry Rat Nat)
#guard (⟨derivativeNode, none⟩ : Dag.Entry Rat Nat) != ⟨badDenominator, none⟩
#guard let encoded := Dag.encode (.split sharedParent (.leaf derivativeNode) (.leaf badDenominator))
  encoded.entries.size == 3 && encoded.root == 2 && !check encoded sharedParent.queries
#guard let encoded := Dag.encode (.split sharedParent
    (.leaf derivativeNode) (.leaf {derivativeNode with context := 8}))
  encoded.entries.size == 3 && !check encoded sharedParent.queries

/-- The second node has a different valid squarefree witness from the domain
shared by the first node. Every one of its query certificates retains it. -/
@[expose] def alternateCert (cert : TarskiCertificate Rat Rat Nat) : TarskiCertificate Rat Rat Nat :=
  {cert with squarefree := {cert.squarefree with initial := ⟨2, 0, 4⟩}}

@[expose] def alternate : Node Rat Nat :=
  {derivativeNode with moments := #v[alternateCert singletonQuery,
    alternateCert (constantQuery 2), alternateCert (constantQuery 4)]}

@[expose] def corruptCert (cert : TarskiCertificate Rat Rat Nat) : TarskiCertificate Rat Rat Nat :=
  {cert with squarefree := {cert.squarefree with terminal := none}}

@[expose] def corrupt : Node Rat Nat :=
  {alternate with moments := #v[corruptCert singletonQuery,
    corruptCert (constantQuery 2), corruptCert (constantQuery 4)]}

-- A graph cache miss selects the node's own valid domain, rather than replaying
-- that same witness separately for every moment in the node.
#guard let shared := singletonQuery.domain.replay? Sturm.orderSign (EndpointSigns.ofSign Sturm.orderSign)
  shared.isSome &&
    (alternate.cache Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper shared).any
    (fun d => d.data.squarefree == (alternateCert singletonQuery).squarefree)
#guard (fullNode.cache Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper none).isNone
#guard let shared := singletonQuery.domain.replay? Sturm.orderSign (EndpointSigns.ofSign Sturm.orderSign)
  shared.isSome &&
    (fullNode.cache Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper shared).isSome
#guard let invalid := {derivativeNode with moments :=
    #v[corruptCert singletonQuery, constantQuery 2, constantQuery 4]}
  (invalid.cache Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper none).isNone &&
    !(Replay.leaf invalid).check Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper
      invalid.queries

set_option maxRecDepth 32768 in
/-- Cross-node reuse accepts a different valid witness through full replay,
and rejects a malformed later witness despite the valid shared domain. -/
theorem domain_kernel :
    check ⟨#[⟨firstNode, none⟩, ⟨alternate, none⟩,
      ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries = true ∧
    check ⟨#[⟨firstNode, none⟩, ⟨corrupt, none⟩,
      ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries = false := by
  simp only [check, Dag.check, Dag.replay_eq, Dag.step_eq,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

#guard check ⟨#[⟨firstNode, none⟩, ⟨alternate, none⟩,
  ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries
#guard !check ⟨#[⟨firstNode, none⟩, ⟨corrupt, none⟩,
  ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries
#guard let stale := {derivativeNode with moments := derivativeNode.moments.map fun cert =>
    {cert with context := 8}}
  !check ⟨#[⟨firstNode, none⟩, ⟨stale, none⟩,
    ⟨fullNode, some (0, 1)⟩], 2⟩ fullNode.queries

/-- info: 'Hex.SignDet.Node.check_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Node.check_cache
/-- info: 'Hex.SignDet.Dag.step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.step_eq
/-- info: 'Hex.SignDet.Dag.step_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.step_cache
/-- info: 'Hex.SignDet.Dag.replay_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.replay_eq
/-- info: 'Hex.SignDet.CrossCheck.domain_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms domain_kernel

-- A produced four-query tree has seven occurrences but four distinct entries,
-- including two different leaves and one repeated internal subtree.
#guard match Sturm.prepare Sturm.orderSign singletonRaw.head singletonRaw.lower singletonRaw.upper with
  | none => false
  | some domain =>
    let qs := [DensePoly.ofCoeffs #[0, 1], 0, DensePoly.ofCoeffs #[0, 1], 0]
    match buildPrepared (7 : Nat) domain qs with
    | .error _ => false
    | .ok tree =>
      let encoded := Dag.encode tree.val
      match encoded.replay? Sturm.orderSign 7 singletonRaw.head
          singletonRaw.lower singletonRaw.upper qs with
      | none => false
      | some replay => encoded.entries.size == 4 && encoded.root == 3 &&
          replay.val.node == tree.val.node

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

/-- info: 'Hex.SignDet.CrossCheck.equality_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equality_kernel

/-- info: 'Hex.SignDet.CrossCheck.reduction_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reduction_kernel
/-- info: 'Hex.SignDet.Dag.descriptor_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.descriptor_replay
/-- info: 'Hex.SignDet.Descriptor.ofReplay_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.ofReplay_none

/-- info: 'Hex.SignDet.Descriptor.build_ok_ofPrepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.build_ok_ofPrepared

/-- info: 'Hex.SignDet.Descriptor.build_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.build_raw

/-- info: 'Hex.SignDet.Descriptor.build_ofCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.build_ofCount

/-- info: 'Hex.SignDet.Descriptor.build_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.build_context

/-- info: 'Hex.SignDet.Descriptor.build_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.build_domain

/-- info: 'Hex.SignDet.Descriptor.build_malformed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Descriptor.build_malformed

/-- info: 'Hex.SignDet.Dag.check_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.check_replay
/-- info: 'Hex.SignDet.CrossCheck.full_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms full_kernel
/-- info: 'Hex.SignDet.CrossCheck.shared_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shared_kernel

/-- info: 'Hex.SignDet.Dag.descriptor_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.descriptor_raw
/-- info: 'Hex.SignDet.CrossCheck.rejected_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rejected_kernel
/-- info: 'Hex.SignDet.CrossCheck.descriptor_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descriptor_kernel

/-- info: 'Hex.SignDet.Dag.Encoder.insert_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.Encoder.insert_valid
/-- info: 'Hex.SignDet.Dag.encodeFrom_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.encodeFrom_checks
/-- info: 'Hex.SignDet.Dag.replay_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.replay_encode
/-- info: 'Hex.SignDet.Dag.check_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.check_encode

/-- info: 'Hex.SignDet.Dag.expand_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.expand_encode
/-- info: 'Hex.SignDet.Dag.replay_expands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.replay_expands
/-- info: 'Hex.SignDet.Dag.check_encode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dag.check_encode_eq
/-- info: 'Hex.SignDet.CrossCheck.encoded_rejected_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encoded_rejected_kernel
/-- info: 'Hex.SignDet.CrossCheck.invalid_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invalid_roundtrip

end Hex.SignDet.CrossCheck

/-- info: 'Hex.SignDet.Dag.descriptor_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Dag.descriptor_encode
