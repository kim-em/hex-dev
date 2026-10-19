/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportDescriptor

public section

namespace Hex.RealClosure.Transport.Inventory

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [CommRing K] [DecidableEq K]

/-- The stored coefficient positions of a native polynomial. No field laws on
native expressions are needed to enumerate its finite support. -/
@[expose] def coefficients (p : Hex.DensePoly E) : List E :=
  (List.range p.size).map p.coeff

/-- Domain membership, queried signs and zero reflection on one finite list.
For a native model, sign agreement supplies zero reflection. -/
@[expose] def Agreement (read : E → K) (S : E → Prop) (sourceSign : E → Int)
    (targetSign : K → Int) (xs : List E) : Prop :=
  ∀ x ∈ xs, S x ∧ targetSign (read x) = sourceSign x ∧ (read x = 0 ↔ x = 0)

omit [DecidableEq E] [DecidableEq K] in
theorem Agreement.mono {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} {xs ys : List E}
    (data : Agreement read S sourceSign targetSign ys) (subset : ∀ x ∈ xs, x ∈ ys) :
    Agreement read S sourceSign targetSign xs := fun x member => data x (subset x member)

omit [DecidableEq E] [DecidableEq K] in
theorem Agreement.append {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} {xs ys : List E}
    (data : Agreement read S sourceSign targetSign (xs ++ ys)) :
    Agreement read S sourceSign targetSign xs ∧ Agreement read S sourceSign targetSign ys :=
  ⟨data.mono (fun _ h => List.mem_append_left _ h),
    data.mono (fun _ h => List.mem_append_right _ h)⟩

theorem coefficient_mem (p : Hex.DensePoly E) (i : Nat) (bound : i < p.size) :
    p.coeff i ∈ coefficients p := by
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr bound, rfl⟩

omit [DecidableEq K] in
theorem Agreement.members {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} {p : Hex.DensePoly E}
    (data : Agreement read S sourceSign targetSign (coefficients p)) :
    ∀ i < p.size, S (p.coeff i) :=
  fun i bound => (data _ (coefficient_mem p i bound)).1

omit [DecidableEq K] in
theorem Agreement.leading {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} {p : Hex.DensePoly E}
    (data : Agreement read S sourceSign targetSign (coefficients p)) : Leading read p := by
  intro positive zero
  have reflected := (data _ (coefficient_mem p (p.size - 1) (by omega))).2.2.mp zero
  exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size p positive reflected

/-- Literal coefficients and scales in one stored preprocessing/reduction step. -/
@[expose] def reduction (s : Hex.SignDet.ReductionStep E) : List E :=
  coefficients s.next ++ [s.witness.leftScale, s.witness.rightScale] ++
    coefficients s.witness.quotient

omit [DecidableEq K] in
theorem reduction_data {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} (s : Hex.SignDet.ReductionStep E)
    (data : Agreement read S sourceSign targetSign (reduction s)) :
    ReductionDomain S s ∧ ReductionSigns read sourceSign targetSign s := by
  have next := data.mono (fun x h => by simp only [reduction, List.mem_append]; exact Or.inl (Or.inl h))
  have quotient := data.mono (fun x h => by simp only [reduction, List.mem_append]; exact Or.inr h)
  have left := data s.witness.leftScale (by simp [reduction])
  have right := data s.witness.rightScale (by simp [reduction])
  exact ⟨⟨next.members, left.1, right.1, quotient.members⟩, ⟨left.2.1, right.2.1⟩⟩

omit [DecidableEq E] [DecidableEq K] in
theorem Agreement.flatMap {A : Type w} {read : E → K} {S : E → Prop}
    {sourceSign : E → Int} {targetSign : K → Int} {xs : List A} {f : A → List E}
    (data : Agreement read S sourceSign targetSign (xs.flatMap f))
    (a : A) (member : a ∈ xs) : Agreement read S sourceSign targetSign (f a) :=
  data.mono (fun _ h => List.mem_flatMap.mpr ⟨a, member, h⟩)

/-- The literal scales and quotient of one remainder-chain witness. -/
@[expose] def witness (left right : E) (q : Hex.DensePoly E) : List E :=
  [left, right] ++ coefficients q

/-- Every stored remainder-chain row and witness, including terminal data.
The index schedule is the checker's original schedule, with the same defaults. -/
@[expose] def chain (cert : Hex.SignedRemainderChain E) : List E :=
  cert.chain.toList.flatMap coefficients ++
    (witness cert.initial.leftScale cert.initial.rightScale cert.initial.quotient ++
      ((List.range cert.steps.size).flatMap (fun i =>
        let step := cert.steps.getD i ⟨0, 0, 0⟩
        witness step.leftScale step.rightScale step.quotient) ++
      cert.terminal.toList.flatMap (fun pair => pair.1 :: coefficients pair.2)))

theorem chain_data {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} (cert : Hex.SignedRemainderChain E)
    (data : Agreement read S sourceSign targetSign (chain cert)) :
    ChainDomain S cert ∧ ChainSigns read sourceSign targetSign cert ∧
      (∀ p ∈ cert.chain, Leading read p) := by
  have rows := data.append.1
  have initial := data.append.2.append.1
  have steps := data.append.2.append.2.append.1
  have terminal := data.append.2.append.2.append.2
  have row (p : Hex.DensePoly E) (member : p ∈ cert.chain) :=
    rows.flatMap p (by simpa using member)
  have step (i : Nat) (bound : i < cert.steps.size) :=
    steps.flatMap i (List.mem_range.mpr bound)
  have finish (scale : E) (q : Hex.DensePoly E) (pair : cert.terminal = some (scale, q)) :=
    terminal.flatMap (scale, q) (by simp [pair])
  have initialLeft := initial cert.initial.leftScale (by simp [witness])
  have initialRight := initial cert.initial.rightScale (by simp [witness])
  have stepLeft (i : Nat) (bound : i < cert.steps.size) :=
    step i bound (cert.steps.getD i ⟨0, 0, 0⟩).leftScale (by simp [witness])
  have stepRight (i : Nat) (bound : i < cert.steps.size) :=
    step i bound (cert.steps.getD i ⟨0, 0, 0⟩).rightScale (by simp [witness])
  have finalScale (scale : E) (q : Hex.DensePoly E) (pair : cert.terminal = some (scale, q)) :=
    finish scale q pair scale (by simp)
  refine ⟨⟨?_, initialLeft.1, initialRight.1, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨initialLeft.2.1, initialRight.2.1, ?_, ?_, ?_⟩, ?_⟩
  · exact fun p member => (row p member).members
  · exact initial.append.2.members
  · exact fun i bound => (stepLeft i bound).1
  · exact fun i bound => (stepRight i bound).1
  · exact fun i bound => (step i bound).append.2.members
  · exact fun scale q pair => (finalScale scale q pair).1
  · intro scale q pair
    exact (finish scale q pair |>.mono (fun x h => List.mem_cons_of_mem scale h)).members
  · exact fun i bound => (stepLeft i bound).2.1
  · exact fun i bound => (stepRight i bound).2.1
  · exact fun scale q pair => (finalScale scale q pair).2.1
  · exact fun p member => (row p member).leading

variable [Add E] [Sub E] [Mul E] [One E] [NatCast E]

/-- The literal finite endpoint and the value whose sign is queried there. -/
@[expose] def endpointValues (p : Hex.DensePoly E) : Hex.Endpoint E → List E
  | .finite x => [x, p.eval x]
  | _ => [p.leadingCoeff]

/-- The finite comparison queried when both interval endpoints are finite. -/
@[expose] def intervalValues : Hex.Endpoint E → Hex.Endpoint E → List E
  | .finite x, .finite y => [x - y]
  | _, _ => []

/-- All native data needed by the exact stored Tarski certificate. Endpoint
values are taken from the original head and original remainder rows. -/
@[expose] def query {C : Type w} (p f : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (cert : Hex.TarskiCertificate E E C) : List E :=
  coefficients p ++ (coefficients f ++ (chain cert.squarefree ++ (chain cert.remainders ++
    (intervalValues a b ++ (endpointValues p a ++ (endpointValues p b ++
      cert.remainders.chain.toList.flatMap (fun r => endpointValues r a ++ endpointValues r b)))))))

omit [DecidableEq K] [Sub E] [One E] [NatCast E] in
theorem endpoint_data {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} (p : Hex.DensePoly E) (a : Hex.Endpoint E)
    (data : Agreement read S sourceSign targetSign (endpointValues p a)) :
    EndpointDomain S a ∧ EndpointAgreement read sourceSign targetSign p a := by
  cases a with
  | finite x => exact ⟨(data x (by simp [endpointValues])).1,
      (data (p.eval x) (by simp [endpointValues])).2.1⟩
  | negInf => exact ⟨trivial, (data p.leadingCoeff (by simp [endpointValues])).2.1⟩
  | posInf => exact ⟨trivial, (data p.leadingCoeff (by simp [endpointValues])).2.1⟩

theorem query_data {C : Type w} {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} (closed : Closed read S) (p f : Hex.DensePoly E)
    (a b : Hex.Endpoint E) (cert : Hex.TarskiCertificate E E C)
    (data : Agreement read S sourceSign targetSign (query p f a b cert)) :
    QueryData read sourceSign targetSign p f a b cert := by
  have hp := data.append.1
  have hf := data.append.2.append.1
  have squarefree := chain_data cert.squarefree data.append.2.append.2.append.1
  have remainders := chain_data cert.remainders data.append.2.append.2.append.2.append.1
  have interval := data.append.2.append.2.append.2.append.2.append.1
  have lower := endpoint_data p a data.append.2.append.2.append.2.append.2.append.2.append.1
  have upper := endpoint_data p b data.append.2.append.2.append.2.append.2.append.2.append.2.append.1
  have rows := data.append.2.append.2.append.2.append.2.append.2.append.2.append.2
  have row (r : Hex.DensePoly E) (member : r ∈ cert.remainders.chain) :=
    rows.flatMap r (by simpa using member)
  refine QueryData.of_closed read S closed sourceSign targetSign p f a b cert hp.members hf.members
    squarefree.1 remainders.1 hp.leading squarefree.2.2 remainders.2.2
    squarefree.2.1 remainders.2.1 lower.1 upper.1 ?_ lower.2 upper.2 ?_ ?_
  · intro x y left right
    subst a b
    exact (interval (x - y) (by simp [intervalValues])).2.1
  · exact fun r member => (endpoint_data r a (row r member).append.1).2
  · exact fun r member => (endpoint_data r b (row r member).append.2).2

/-- Stored product-reduction data at one moment position. -/
@[expose] def reductionValues (r : Option (Hex.SignDet.Reduction E)) : List E :=
  match r with
  | none => []
  | some r => r.steps.flatMap reduction ++ coefficients r.result

/-- The node inventory follows its actual preprocessing choice and each
retained row's actual reduction and Tarski certificate. -/
@[expose] def node {C : Type w} (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) (n : Hex.SignDet.Node E C) : List E :=
  coefficients p ++ (qs.flatMap coefficients ++
    ((Hex.SignDet.QueryReduction.operands qs n.preparation).flatMap coefficients ++
      ((match n.preparation with
        | none => []
        | some r => r.steps.flatMap reduction) ++
      (List.finRange n.size).flatMap (fun i => reductionValues n.reductions[i] ++
        query p (Hex.SignDet.queryPoly (Hex.SignDet.QueryReduction.operands qs n.preparation)
          n.system.rows[i] n.reductions[i]) a b n.moments[i]))))

theorem node_data {C : Type w} {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} (closed : Closed read S) (p : Hex.DensePoly E)
    (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E)) (n : Hex.SignDet.Node E C)
    (data : Agreement read S sourceSign targetSign (node p a b qs n)) :
    NodeData read S sourceSign targetSign p a b qs n := by
  have hp := data.append.1
  have hqs := data.append.2.append.1
  have operands := data.append.2.append.2.append.1
  have prepared := data.append.2.append.2.append.2.append.1
  have moments := data.append.2.append.2.append.2.append.2
  have operand (q : Hex.DensePoly E) (member : q ∈ Hex.SignDet.QueryReduction.operands qs n.preparation) :=
    operands.flatMap q member
  have position (i : Fin n.size) := moments.flatMap i (by simp)
  refine ⟨hp.leading, fun q member => (operand q member).members, ?_, ?_, ?_⟩
  · intro r equal
    have steps : Agreement read S sourceSign targetSign (r.steps.flatMap reduction) := by
      simpa only [equal] using prepared
    exact PreparationData.of_closed read S closed sourceSign targetSign p qs r.steps
      hp.leading hp.members (fun q member => (hqs.flatMap q member).members)
      (fun s member => (reduction_data s (steps.flatMap s member)).1)
      (fun s member => (reduction_data s (steps.flatMap s member)).2)
  · intro i r equal
    have reduced : Agreement read S sourceSign targetSign
        (r.steps.flatMap reduction ++ coefficients r.result) := by
      simpa only [equal, reductionValues] using (position i).append.1
    exact ReductionData.of_closed read S closed sourceSign targetSign p 1
      (Hex.SignDet.factors (Hex.SignDet.QueryReduction.operands qs n.preparation) n.system.rows[i])
      r.steps r.result hp.leading hp.members (fun j _ => closed.coeff_one read S j)
      (factors_closed S _ _ (fun q member => (operand q member).members))
      (fun s member => (reduction_data s (reduced.append.1.flatMap s member)).1)
      (fun s member => (reduction_data s (reduced.append.1.flatMap s member)).2)
      reduced.append.2.members
  · intro i
    exact query_data closed _ _ a b n.moments[i] (position i).append.2

/-- Traverse every actual node with the checker's positional query slices. -/
@[expose] def replay {C : Type w} (p : Hex.DensePoly E) (a b : Hex.Endpoint E)
    (qs : List (Hex.DensePoly E)) : Hex.SignDet.Replay E C → List E
  | .leaf n => node p a b qs n
  | .split n l r => node p a b qs n ++
      (replay p a b (qs.take (qs.length / 2)) l ++
        replay p a b (qs.drop (qs.length / 2)) r)

theorem replay_data {C : Type w} {read : E → K} {S : E → Prop} {sourceSign : E → Int}
    {targetSign : K → Int} (closed : Closed read S) (p : Hex.DensePoly E)
    (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E)) (t : Hex.SignDet.Replay E C)
    (data : Agreement read S sourceSign targetSign (replay p a b qs t)) :
    ReplayData read S sourceSign targetSign p a b qs t := by
  induction t generalizing qs with
  | leaf n => exact node_data closed p a b qs n data
  | split n l r ihl ihr =>
    exact ⟨node_data closed p a b qs n data.append.1,
      ihl _ data.append.2.append.1, ihr _ data.append.2.append.2⟩

/-- The original descriptor and every descendant of its retained replay. -/
@[expose] def descriptor {C : Type w} (raw : Hex.SignDet.RawDescriptor E C)
    (evidence : Hex.SignDet.Replay E C) : List E :=
  coefficients raw.head ++ replay raw.head raw.lower raw.upper raw.queries evidence

theorem descriptor_data {C : Type w} [DecidableEq C] {read : E → K} {S : E → Prop}
    {sourceSign : E → Int} {targetSign : K → Int} (closed : Closed read S)
    (raw : Hex.SignDet.RawDescriptor E C) (evidence : Hex.SignDet.Replay E C)
    (data : Agreement read S sourceSign targetSign (descriptor raw evidence)) :
    DescriptorData read S sourceSign targetSign raw evidence :=
  ⟨data.append.1.members, data.append.1.leading,
    replay_data closed raw.head raw.lower raw.upper raw.queries evidence data.append.2⟩

end Hex.RealClosure.Transport.Inventory

/-- info: 'Hex.RealClosure.Transport.Inventory.chain_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Inventory.chain_data

/-- info: 'Hex.RealClosure.Transport.Inventory.query_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Inventory.query_data

/-- info: 'Hex.RealClosure.Transport.Inventory.node_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Inventory.node_data

/-- info: 'Hex.RealClosure.Transport.Inventory.replay_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Inventory.replay_data

/-- info: 'Hex.RealClosure.Transport.Inventory.descriptor_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Inventory.descriptor_data
