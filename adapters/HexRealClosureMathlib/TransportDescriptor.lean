/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportSample
public import HexSignDet.Descriptor

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} {C : Type w} {D : Type z}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [CommRing K] [DecidableEq K]

namespace Finite

/-- Finite cast/product obligations for each derivative actually constructed. -/
@[expose] def DerivativeData (read : E → K) (p : Hex.DensePoly E) : Nat → Prop
  | 0 => True
  | n + 1 => Differentiation read p ∧ DerivativeData read p.derivative n

/-- A closed domain supplies the finite derivative sequence. -/
theorem DerivativeData.of_closed (read : E → K) (S : E → Prop) (closed : Closed read S)
    (p : Hex.DensePoly E) (n : Nat) (members : ∀ i < p.size, S (p.coeff i)) :
    DerivativeData read p n := by
  induction n generalizing p with
  | zero => exact trivial
  | succ n ih =>
    exact ⟨Differentiation.of_closed read S closed p members,
      ih p.derivative (fun i _ => closed.coeff_derivative read S p members i)⟩

/-- Transport the reached derivatives without a universally closed domain. -/
theorem derivativesFrom_polynomial (read : E → K) (zero : read 0 = 0)
    (p : Hex.DensePoly E) (n : Nat) (data : DerivativeData read p n) :
    (Hex.SignDet.derivativesFrom p n).map (polynomial read) =
      Hex.SignDet.derivativesFrom (polynomial read p) n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [DerivativeData] at data
    simp only [Hex.SignDet.derivativesFrom, List.map_cons]
    rw [ih p.derivative data.2, Ring.polynomial_derivative read zero p data.1.products]

/-- Leading reflection fixes the length; finite derivative data fixes every row. -/
theorem derivatives_polynomial (read : E → K) (zero : read 0 = 0)
    (p : Hex.DensePoly E) (data : DerivativeData read p p.natDegree) (head : Leading read p) :
    (Hex.SignDet.derivatives p).map (polynomial read) =
      Hex.SignDet.derivatives (polynomial read p) := by
  rw [Hex.SignDet.derivatives, Hex.SignDet.derivatives, polynomial_degree read zero p head]
  exact derivativesFrom_polynomial read zero p p.natDegree data

end Finite

/-- The actual iterated derivatives commute using only original coefficient
memberships; no intermediate degree preservation is required. -/
theorem derivativesFrom_polynomial (read : E → K) (S : E → Prop) (closed : Closed read S)
    (p : Hex.DensePoly E) (n : Nat) (members : ∀ i < p.size, S (p.coeff i)) :
    (Hex.SignDet.derivativesFrom p n).map (polynomial read) =
      Hex.SignDet.derivativesFrom (polynomial read p) n := by
  exact Finite.derivativesFrom_polynomial read closed.read_zero p n
    (Finite.DerivativeData.of_closed read S closed p n members)

/-- The degree used to choose the derivative sequence is retained by the
original head's leading guard alone. -/
theorem derivatives_polynomial (read : E → K) (S : E → Prop) (closed : Closed read S)
    (p : Hex.DensePoly E) (members : ∀ i < p.size, S (p.coeff i)) (head : Leading read p) :
    (Hex.SignDet.derivatives p).map (polynomial read) =
      Hex.SignDet.derivatives (polynomial read p) := by
  exact Finite.derivatives_polynomial read closed.read_zero p
    (Finite.DerivativeData.of_closed read S closed p p.natDegree members) head

/-- Interpret raw descriptor inputs, retaining derivative indices and signs.
The target queries are reconstructed from the interpreted head. -/
@[expose] def descriptor (read : E → K) (contextMap : C → D) (raw : Hex.SignDet.RawDescriptor E C) :
    Hex.SignDet.RawDescriptor K D :=
  { context := contextMap raw.context
    head := polynomial read raw.head
    lower := endpoint read raw.lower
    upper := endpoint read raw.upper
    indices := raw.indices
    signs := raw.signs }

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] in
/-- The same literal derivative indices remain well formed after transport. -/
theorem descriptor_wellFormed (read : E → K) (zero : read 0 = 0) (contextMap : C → D)
    (raw : Hex.SignDet.RawDescriptor E C) (head : Leading read raw.head) :
    (descriptor read contextMap raw).wellFormed = raw.wellFormed := by
  simp only [Hex.SignDet.RawDescriptor.wellFormed, descriptor, polynomial_degree read zero raw.head head]
  rfl

namespace Finite

/-- Reconstructed target derivative queries equal the interpreted original
queries, including implicit zero reads at invalid indices. -/
theorem descriptor_queries (read : E → K) (zero : read 0 = 0)
    (contextMap : C → D) (raw : Hex.SignDet.RawDescriptor E C)
    (derivatives : DerivativeData read raw.head raw.head.natDegree) (head : Leading read raw.head) :
    (descriptor read contextMap raw).queries = raw.queries.map (polynomial read) := by
  simp only [Hex.SignDet.RawDescriptor.queries, descriptor, List.map_map]
  rw [← derivatives_polynomial read zero raw.head derivatives head]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, List.getElem?_map]
  cases h : (Hex.SignDet.derivatives raw.head)[i - 1]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact (polynomial_zero read zero 0 (by simp) |>.mpr rfl).symm
  | some q => simp only [Option.map_some, Option.getD_some]

/-- The complete descriptor check transports the actual reconstructed
derivatives, literal context binding and unchanged count-one replay. -/
theorem descriptor_check [DecidableEq C] [DecidableEq D]
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (raw : Hex.SignDet.RawDescriptor E C) (evidence : Hex.SignDet.Replay E C)
    (derivatives : DerivativeData read raw.head raw.head.natDegree) (head : Leading read raw.head)
    (data : ReplayData read sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence)
    (accepted : raw.check sourceSign context evidence = true) :
    (descriptor read contextMap raw).check targetSign (contextMap context)
      (replay read contextMap evidence) = true := by
  obtain ⟨wellFormed, binding, checked, one⟩ := Hex.SignDet.RawDescriptor.check_eq accepted
  have transported := replay_check read zero unit contextMap sourceSign targetSign context
    raw.head raw.lower raw.upper raw.queries evidence data checked
  simp only [Hex.SignDet.RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨(descriptor_wellFormed read zero contextMap raw head).trans wellFormed,
    congrArg contextMap binding⟩, ?_⟩, ?_⟩
  · rw [descriptor_queries read zero contextMap raw derivatives head]
    exact transported
  · rw [replay_node]
    change evidence.node.system.count raw.signs = 1
    exact (evidence.table_lookup checked raw.signs).symm.trans one

end Finite

/-- Reconstructed target derivative queries equal the interpreted original
queries, including implicit zero reads at invalid indices. -/
theorem descriptor_queries (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (raw : Hex.SignDet.RawDescriptor E C)
    (members : ∀ i < raw.head.size, S (raw.head.coeff i)) (head : Leading read raw.head) :
    (descriptor read contextMap raw).queries = raw.queries.map (polynomial read) := by
  exact Finite.descriptor_queries read closed.read_zero contextMap raw
    (Finite.DerivativeData.of_closed read S closed raw.head raw.head.natDegree members) head

/-- The complete descriptor check transports the actual reconstructed
derivatives, literal context binding and unchanged count-one replay. -/
theorem descriptor_check [DecidableEq C] [DecidableEq D]
    (read : E → K) (S : E → Prop) (closed : Closed read S) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (raw : Hex.SignDet.RawDescriptor E C) (evidence : Hex.SignDet.Replay E C)
    (members : ∀ i < raw.head.size, S (raw.head.coeff i)) (head : Leading read raw.head)
    (data : ReplayData read S sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence)
    (accepted : raw.check sourceSign context evidence = true) :
    (descriptor read contextMap raw).check targetSign (contextMap context)
      (replay read contextMap evidence) = true := by
  exact Finite.descriptor_check read closed.read_zero closed.read_one contextMap
    sourceSign targetSign context raw evidence
    (Finite.DerivativeData.of_closed read S closed raw.head raw.head.natDegree members) head
    (Finite.ReplayData.of_closed read S closed sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence data) accepted

variable [DecidableEq C] [DecidableEq D]

/-- Finite premises for transporting an accepted descriptor. Membership
derives the complete derivative arithmetic from the original head alone. -/
structure DescriptorData (read : E → K) (S : E → Prop) (sourceSign : E → Int)
    (targetSign : K → Int) (raw : Hex.SignDet.RawDescriptor E C)
    (evidence : Hex.SignDet.Replay E C) : Prop where
  members : ∀ i < raw.head.size, S (raw.head.coeff i)
  head : Leading read raw.head
  replay : ReplayData read S sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence

namespace Finite

/-- Finite premises for the actual derivative reconstruction and retained replay. -/
structure DescriptorData (read : E → K) (sourceSign : E → Int)
    (targetSign : K → Int) (raw : Hex.SignDet.RawDescriptor E C)
    (evidence : Hex.SignDet.Replay E C) : Prop where
  derivatives : DerivativeData read raw.head raw.head.natDegree
  head : Leading read raw.head
  replay : ReplayData read sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence

/-- Closed descriptor data implies its finite arithmetic obligations. -/
theorem DescriptorData.of_closed (read : E → K) (S : E → Prop) (closed : Closed read S)
    (sourceSign : E → Int) (targetSign : K → Int) (raw : Hex.SignDet.RawDescriptor E C)
    (evidence : Hex.SignDet.Replay E C)
    (data : Hex.RealClosure.Transport.DescriptorData read S sourceSign targetSign raw evidence) :
    DescriptorData read sourceSign targetSign raw evidence :=
  ⟨DerivativeData.of_closed read S closed raw.head raw.head.natDegree data.members, data.head,
    ReplayData.of_closed read S closed sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence data.replay⟩

/-- Reuse the literal mapped replay to construct a checked target descriptor
with its own reconstructed derivative queries and immutable context. -/
@[expose] def checkedDescriptor (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read sourceSign targetSign d.raw d.evidence) :
    Hex.SignDet.Descriptor K D targetSign (contextMap context) := by
  have accepted := descriptor_check read zero unit contextMap sourceSign targetSign context
    d.raw d.evidence data.derivatives data.head data.replay d.accepted
  simp only [Hex.SignDet.RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact Hex.SignDet.Descriptor.ofTable _ _ accepted.1.1.1 accepted.1.1.2 accepted.1.2
    (((replay read contextMap d.evidence).table_lookup accepted.1.2
      (descriptor read contextMap d.raw).signs).trans accepted.2)

/-- The validated descriptor retains its literal mapped raw input. -/
theorem checkedDescriptor_raw (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read sourceSign targetSign d.raw d.evidence) :
    (checkedDescriptor read zero unit contextMap sourceSign targetSign context d data).raw =
      descriptor read contextMap d.raw := by
  simp only [checkedDescriptor, Hex.SignDet.Descriptor.ofTable_raw]

/-- Checking the exact interpreted raw descriptor and replay returns the
constructed target descriptor, with no new sign determination. -/
theorem checkedDescriptor_checked (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read sourceSign targetSign d.raw d.evidence) :
    Hex.SignDet.Descriptor.ofReplay? targetSign (contextMap context)
      (descriptor read contextMap d.raw) (replay read contextMap d.evidence) =
        some (checkedDescriptor read zero unit contextMap sourceSign targetSign context d data) := by
  simp only [checkedDescriptor]
  apply Hex.SignDet.Descriptor.ofReplay_ofTable

/-- The result retains the whole literal replay, including every descendant,
moment, reduction, preprocessing entry and rank witness. -/
theorem checkedDescriptor_evidence (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read sourceSign targetSign d.raw d.evidence) :
    (checkedDescriptor read zero unit contextMap sourceSign targetSign context d data).evidence =
      replay read contextMap d.evidence := by
  have accepted := descriptor_check read zero unit contextMap sourceSign targetSign context
    d.raw d.evidence data.derivatives data.head data.replay d.accepted
  have fields := Hex.SignDet.Descriptor.ofReplay_data targetSign (contextMap context)
    (descriptor read contextMap d.raw) (replay read contextMap d.evidence)
  rw [checkedDescriptor_checked read zero unit contextMap sourceSign targetSign context d data,
    Option.map_some, ite_eq_left accepted] at fields
  exact (Prod.mk.inj (Option.some.inj fields)).2

end Finite

/-- Reuse the literal mapped replay to construct a checked target descriptor
with its own reconstructed derivative queries and immutable context. -/
@[expose] def checkedDescriptor (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read S sourceSign targetSign d.raw d.evidence) :
    Hex.SignDet.Descriptor K D targetSign (contextMap context) := by
  have accepted := descriptor_check read S closed contextMap sourceSign targetSign context
    d.raw d.evidence data.members data.head data.replay d.accepted
  simp only [Hex.SignDet.RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact Hex.SignDet.Descriptor.ofTable _ _ accepted.1.1.1 accepted.1.1.2 accepted.1.2
    (((replay read contextMap d.evidence).table_lookup accepted.1.2
      (descriptor read contextMap d.raw).signs).trans accepted.2)

/-- The validated descriptor retains its literal mapped raw input. -/
theorem checkedDescriptor_raw (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read S sourceSign targetSign d.raw d.evidence) :
    (checkedDescriptor read S closed contextMap sourceSign targetSign context d data).raw =
      descriptor read contextMap d.raw := by
  simp only [checkedDescriptor, Hex.SignDet.Descriptor.ofTable_raw]

/-- Checking the exact interpreted raw descriptor and replay returns the
constructed target descriptor, with no new sign determination. -/
theorem checkedDescriptor_checked (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read S sourceSign targetSign d.raw d.evidence) :
    Hex.SignDet.Descriptor.ofReplay? targetSign (contextMap context)
      (descriptor read contextMap d.raw) (replay read contextMap d.evidence) =
        some (checkedDescriptor read S closed contextMap sourceSign targetSign context d data) := by
  simp only [checkedDescriptor]
  apply Hex.SignDet.Descriptor.ofReplay_ofTable

/-- The result retains the whole literal replay, including every descendant,
moment, reduction, preprocessing entry and rank witness. -/
theorem checkedDescriptor_evidence (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (d : Hex.SignDet.Descriptor E C sourceSign context)
    (data : DescriptorData read S sourceSign targetSign d.raw d.evidence) :
    (checkedDescriptor read S closed contextMap sourceSign targetSign context d data).evidence =
      replay read contextMap d.evidence := by
  have accepted := descriptor_check read S closed contextMap sourceSign targetSign context
    d.raw d.evidence data.members data.head data.replay d.accepted
  have fields := Hex.SignDet.Descriptor.ofReplay_data targetSign (contextMap context)
    (descriptor read contextMap d.raw) (replay read contextMap d.evidence)
  rw [checkedDescriptor_checked read S closed contextMap sourceSign targetSign context d data,
    Option.map_some, ite_eq_left accepted] at fields
  exact (Prod.mk.inj (Option.some.inj fields)).2

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.derivativesFrom_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.derivativesFrom_polynomial

/-- info: 'Hex.RealClosure.Transport.derivatives_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.derivatives_polynomial

/-- info: 'Hex.RealClosure.Transport.descriptor_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.descriptor_wellFormed

/-- info: 'Hex.RealClosure.Transport.descriptor_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.descriptor_queries

/-- info: 'Hex.RealClosure.Transport.descriptor_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.descriptor_check

/-- info: 'Hex.RealClosure.Transport.checkedDescriptor_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.checkedDescriptor_raw

/-- info: 'Hex.RealClosure.Transport.checkedDescriptor_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.checkedDescriptor_checked

/-- info: 'Hex.RealClosure.Transport.checkedDescriptor_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.checkedDescriptor_evidence

/-- info: 'Hex.RealClosure.Transport.Finite.DerivativeData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.DerivativeData.of_closed

/-- info: 'Hex.RealClosure.Transport.Finite.derivativesFrom_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.derivativesFrom_polynomial

/-- info: 'Hex.RealClosure.Transport.Finite.derivatives_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.derivatives_polynomial

/-- info: 'Hex.RealClosure.Transport.Finite.descriptor_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.descriptor_queries

/-- info: 'Hex.RealClosure.Transport.Finite.descriptor_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.descriptor_check

/-- info: 'Hex.RealClosure.Transport.Finite.DescriptorData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.DescriptorData.of_closed

/-- info: 'Hex.RealClosure.Transport.Finite.checkedDescriptor_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.checkedDescriptor_raw

/-- info: 'Hex.RealClosure.Transport.Finite.checkedDescriptor_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.checkedDescriptor_checked

/-- info: 'Hex.RealClosure.Transport.Finite.checkedDescriptor_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.checkedDescriptor_evidence
