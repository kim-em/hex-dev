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

/-- The actual iterated derivatives commute using only original coefficient
memberships; no intermediate degree preservation is required. -/
theorem derivativesFrom_polynomial (read : E → K) (S : E → Prop) (closed : Closed read S)
    (p : Hex.DensePoly E) (n : Nat) (members : ∀ i < p.size, S (p.coeff i)) :
    (Hex.SignDet.derivativesFrom p n).map (polynomial read) =
      Hex.SignDet.derivativesFrom (polynomial read p) n := by
  have derivative (q : Hex.DensePoly E) (coefficients : ∀ i < q.size, S (q.coeff i)) :=
    Ring.polynomial_derivative read closed.read_zero q
      (Differentiation.of_closed read S closed q coefficients).products
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [Hex.SignDet.derivativesFrom, List.map_cons]
    rw [ih p.derivative (fun i _ => closed.coeff_derivative read S p members i), derivative p members]

/-- The degree used to choose the derivative sequence is retained by the
original head's leading guard alone. -/
theorem derivatives_polynomial (read : E → K) (S : E → Prop) (closed : Closed read S)
    (p : Hex.DensePoly E) (members : ∀ i < p.size, S (p.coeff i)) (head : Leading read p) :
    (Hex.SignDet.derivatives p).map (polynomial read) =
      Hex.SignDet.derivatives (polynomial read p) := by
  rw [Hex.SignDet.derivatives, Hex.SignDet.derivatives,
    polynomial_degree read closed.read_zero p head]
  exact derivativesFrom_polynomial read S closed p p.natDegree members

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

/-- Reconstructed target derivative queries equal the interpreted original
queries, including implicit zero reads at invalid indices. -/
theorem descriptor_queries (read : E → K) (S : E → Prop) (closed : Closed read S)
    (contextMap : C → D) (raw : Hex.SignDet.RawDescriptor E C)
    (members : ∀ i < raw.head.size, S (raw.head.coeff i)) (head : Leading read raw.head) :
    (descriptor read contextMap raw).queries = raw.queries.map (polynomial read) := by
  simp only [Hex.SignDet.RawDescriptor.queries, descriptor, List.map_map]
  rw [← derivatives_polynomial read S closed raw.head members head]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, List.getElem?_map]
  cases h : (Hex.SignDet.derivatives raw.head)[i - 1]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact (polynomial_zero read closed.read_zero 0 (by simp) |>.mpr rfl).symm
  | some q => simp only [Option.map_some, Option.getD_some]

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
  obtain ⟨wellFormed, binding, checked, one⟩ := Hex.SignDet.RawDescriptor.check_eq accepted
  have transported := replay_check read S closed contextMap sourceSign targetSign context
    raw.head raw.lower raw.upper raw.queries evidence data checked
  simp only [Hex.SignDet.RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨(descriptor_wellFormed read closed.read_zero contextMap raw head).trans wellFormed,
    congrArg contextMap binding⟩, ?_⟩, ?_⟩
  · rw [descriptor_queries read S closed contextMap raw members head]
    exact transported
  · rw [replay_node]
    change evidence.node.system.count raw.signs = 1
    exact (evidence.table_lookup checked raw.signs).symm.trans one

variable [DecidableEq C] [DecidableEq D]

/-- Finite premises for transporting an accepted descriptor. Membership
derives the complete derivative arithmetic from the original head alone. -/
structure DescriptorData (read : E → K) (S : E → Prop) (sourceSign : E → Int)
    (targetSign : K → Int) (raw : Hex.SignDet.RawDescriptor E C)
    (evidence : Hex.SignDet.Replay E C) : Prop where
  members : ∀ i < raw.head.size, S (raw.head.coeff i)
  head : Leading read raw.head
  replay : ReplayData read S sourceSign targetSign raw.head raw.lower raw.upper raw.queries evidence

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
