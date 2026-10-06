/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec
public import HexSignDet.Codec.NodeLaws
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Bytes

public section

namespace Hex.SignDet.Codec

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- The node decoder's structural bounds. These do not assert any arithmetic,
rank, support-completeness or root-count identity. -/
structure Shape (n : Node E Ctx) : Prop where
  rows : ∀ x ∈ n.system.rows.toList, x.length = n.queries.length
  columns : ∀ x ∈ n.system.columns.toList, x.length = n.queries.length
  rankRows : n.basis.rank ≤ n.size
  rankCols : n.basis.rank ≤ n.system.positive.length
  reductions : ∀ r ∈ n.reductions.toList, ∀ t ∈ r, ∀ s ∈ t.steps,
    s.index < n.queries.length
  preparation : ∀ t ∈ n.preparation, ∀ s ∈ t.steps, s.index < n.queries.length

theorem Shape.read_node (h : Shape n) (value : ValueCodec E) (context : ValueCodec Ctx)
    (hv : value.Lawful) (hc : context.Lawful) :
    readNode value context (node value context n) = .ok n :=
  Codec.read_node value context hv hc n h.rows h.columns h.rankRows h.rankCols
    h.reductions h.preparation

section Check
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]

omit [NatCast E] in
private theorem query_indices {sign : E → Int} {p : DensePoly E}
    {qs : List (DensePoly E)} {ss : List (ReductionStep E)} {i : Nat}
    (h : QueryReduction.checkFrom sign p i qs ss = true) :
    ∀ s ∈ ss, s.index < i + qs.length := by
  induction qs generalizing ss i with
  | nil => cases ss <;> simp_all [QueryReduction.checkFrom]
  | cons q qs ih =>
    cases ss with
    | nil => simp [QueryReduction.checkFrom] at h
    | cons s ss =>
      simp only [QueryReduction.checkFrom, Bool.and_eq_true] at h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · have := (ReductionStep.check_eq h.1).1
        simp only [List.length_cons]
        omega
      · have := ih h.2 t ht
        simp only [List.length_cons]
        omega

omit [One E] [Add E] [Sub E] [Mul E] [NatCast E] in
private theorem factor_indices (qs : List (DensePoly E)) (es : List Nat) :
    ∀ f ∈ factors qs es, f.1 < qs.length := by
  intro f hf
  obtain ⟨⟨⟨q, k⟩, i⟩, hi, hf⟩ := List.mem_flatMap.mp hf
  have same := List.eq_of_mem_replicate hf
  have bound := (List.mem_zipIdx' hi).1
  simp only [List.length_zip] at bound
  simpa only [same] using Nat.lt_of_lt_of_le bound (Nat.min_le_left _ _)

omit [One E] [NatCast E] in
private theorem reduction_indices {sign : E → Int} {p prev result : DensePoly E}
    {fs : List (Nat × DensePoly E)} {ss : List (ReductionStep E)} {arity : Nat}
    (h : Reduction.checkFrom sign p prev fs ss result = true)
    (bounds : ∀ f ∈ fs, f.1 < arity) : ∀ s ∈ ss, s.index < arity := by
  induction fs generalizing prev ss with
  | nil => cases ss <;> simp_all [Reduction.checkFrom]
  | cons f fs ih =>
    cases ss with
    | nil => simp [Reduction.checkFrom] at h
    | cons s ss =>
      simp only [Reduction.checkFrom, Bool.and_eq_true] at h
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · rw [(ReductionStep.check_eq h.1).1]
        exact bounds f (by simp)
      · exact ih h.2 (fun f hf => bounds f (by simp [hf])) t ht

variable [DecidableEq Ctx]

/-- Every accepted node meets the decoder's dimension and index bounds.
These follow from the existing checker; callers need no additional shape
certificate or coefficient interpretation. -/
theorem Shape.of_check {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {lo hi : Endpoint E} {qs : List (DensePoly E)} {n : Node E Ctx}
    (h : n.check sign context p lo hi qs = true) : Shape n := by
  obtain ⟨binding, system⟩ := Node.check_bindings h
  have rank : n.basis.rank = n.system.positive.length := by
    simp only [Node.check_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2
  have prep := Node.check_preparation h
  have length : (QueryReduction.operands qs n.preparation).length = qs.length := by
    cases hp : n.preparation with
    | none => rfl
    | some r =>
      simp only [hp] at prep
      exact (QueryReduction.check_bounds prep).1
  refine ⟨?_, ?_, ?_, Nat.le_of_eq rank, ?_, ?_⟩
  · simp only [System.check, Bool.and_eq_true] at system
    intro x hx
    have checked := List.all_eq_true.mp system.1.1.1.1.1 x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.trans (congrArg List.length binding.2.2.2.2).symm
  · simp only [System.check, Bool.and_eq_true] at system
    intro x hx
    have checked := List.all_eq_true.mp system.1.1.1.1.2 x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.trans (congrArg List.length binding.2.2.2.2).symm
  · rw [rank]
    have := List.length_filter_le (fun i : Fin n.size => decide (n.system.counts[i] > 0))
      (List.finRange n.size)
    simpa only [System.positive, List.length_finRange] using this
  · intro r hr t ht s hs
    obtain ⟨i, hi, same⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hr)
    have checked := Node.check_moment h ⟨i, hi⟩
    change checkMoment sign context p lo _ (QueryReduction.operands qs n.preparation)
      n.system.rows[i] n.system.values[i] n.moments[i] n.reductions[i] = true at checked
    have some : n.reductions[i] = Option.some t := same.trans (Option.mem_def.mp ht)
    rw [some] at checked
    have reduced := checkMoment_reduction checked
    simp only [Reduction.check, Bool.and_eq_true] at reduced
    have bound := reduction_indices reduced.2
      (factor_indices (QueryReduction.operands qs n.preparation) n.system.rows[i]) s hs
    rw [length, ← binding.2.2.2.2] at bound
    exact bound
  · intro r hr s hs
    have some := Option.mem_def.mp hr
    rw [some] at prep
    simp only [QueryReduction.check, Bool.and_eq_true] at prep
    have bound := query_indices prep.2 s hs
    simpa only [Nat.zero_add, ← binding.2.2.2.2] using bound

/-- Validation establishes parser bounds for every serialized entry,
including entries not reachable from the selected root. -/
theorem Shape.of_validate {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {lo hi : Endpoint E} {d : Dag E Ctx}
    {memo : Array (Dag.Checked sign context p lo hi)}
    (h : d.validate? sign context p lo hi = some memo) :
    ∀ e ∈ d.entries, Shape e.node := by
  intro e he
  have nodes := Dag.validate_nodes sign context p lo hi d memo h
  have member : e.node ∈ d.entries.map Dag.Entry.node :=
    Array.mem_map.mpr ⟨e, he, rfl⟩
  rw [← nodes] at member
  obtain ⟨checked, _, same⟩ := Array.mem_map.mp member
  rw [← same]
  exact Shape.of_check (Replay.check_node checked.accepted)

/-- info: 'Hex.SignDet.Codec.Shape.of_validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Shape.of_validate

end Check

/-- Earlier child indices roundtrip without changing their left/right order. -/
theorem read_children (children : Option (Nat × Nat))
    (bounds : ∀ pair ∈ children, pair.1 < earlier ∧ pair.2 < earlier) :
    readChildren earlier (option (fun (i, j) => Json.arr #[Json.of i, Json.of j]) children) =
      .ok children := by
  unfold readChildren
  apply read_option_of
  intro pair hp
  obtain ⟨left, right⟩ := pair
  obtain ⟨hl, hr⟩ := bounds (left, right) hp
  simp [tuple, Json.getArr_arr, index, hl, hr, bind, Except.bind, pure, Except.pure]

variable [DecidableEq Ctx]

/-- Entry roundtrips retain the complete literal node and both references. -/
theorem read_entry (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (e : Dag.Entry E Ctx)
    (shape : Shape e.node) (subject : bindings context p lo hi e.node = true)
    (bounds : ∀ pair ∈ e.children, pair.1 < earlier ∧ pair.2 < earlier) :
    readEntry value ctx context p lo hi earlier (entry value ctx e) = .ok e := by
  simp [readEntry, entry, tuple, Json.getArr_arr, bind, Except.bind, pure, Except.pure,
    read_children e.children bounds, shape.read_node value ctx hv hc, subject]

/-- The actual left fold reconstructs every entry in order, including entries
unreachable from the requested root. -/
theorem read_entries (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (entries : Array (Dag.Entry E Ctx))
    (shape : ∀ e ∈ entries, Shape e.node)
    (subjects : ∀ e ∈ entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < entries.size), ∀ pair ∈ entries[i].children,
      pair.1 < i ∧ pair.2 < i) :
    (entries.map (entry value ctx)).foldlM
      (fun earlier j => do
        return earlier.push (← readEntry value ctx context p lo hi earlier.size j)) #[] =
      .ok entries := by
  have array_induction {α : Type} (P : Array α → Prop) (empty : P #[])
      (push : ∀ xs x, P xs → P (xs.push x)) (xs : Array α) : P xs := by
    have aux (ys : List α) : P ys.reverse.toArray := by
      induction ys with
      | nil => exact empty
      | cons y ys ih => simpa using push ys.reverse.toArray y ih
    simpa using aux xs.toList.reverse
  induction entries using array_induction with
  | empty => simp [pure, Except.pure]
  | @push entries e ih =>
    have he := shape e (by simp)
    have hs := subjects e (by simp)
    have hb : ∀ pair ∈ e.children, pair.1 < entries.size ∧ pair.2 < entries.size := by
      simpa using bounds entries.size (by simp)
    have hp := ih (fun x hx => shape x (by simp [hx]))
      (fun x hx => subjects x (by simp [hx]))
      (fun i hi => by simpa [Array.getElem_push_lt hi] using bounds i (by simpa using Nat.lt_succ_of_lt hi))
    rw [Array.map_push, Array.foldlM_push, hp]
    simp [bind, Except.bind, pure, Except.pure, read_entry value ctx hv hc context p lo hi e he hs hb]

/-- Structured graph encoding and decoding preserve every supplied literal
field. The hypotheses are exactly structural bounds and literal bindings;
independent arithmetic replay may still reject the decoded graph. -/
theorem read_graph (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (d : Dag E Ctx)
    (root : d.root < d.entries.size)
    (shape : ∀ e ∈ d.entries, Shape e.node)
    (subjects : ∀ e ∈ d.entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < d.entries.size), ∀ pair ∈ d.entries[i].children,
      pair.1 < i ∧ pair.2 < i) :
    readGraph value ctx context p lo hi (graph value ctx d) = .ok d := by
  have he := read_entries value ctx hv hc context p lo hi d.entries shape subjects bounds
  simp only [Array.size_map, bind, Except.bind, pure, Except.pure] at he
  simp [readGraph, graph, tuple, array, Json.getArr_arr, bind, Except.bind, pure, Except.pure,
    Nat.not_le.mpr root, he]

omit [DecidableEq Ctx] in
/-- The actual byte encoding preserves all supplied JSON fields, without
any structural, arithmetic or parser-success hypothesis. -/
theorem encoded_graph (value : ValueCodec E) (ctx : ValueCodec Ctx) (d : Dag E Ctx) :
    Json.readBytes (d.encodeBytes value ctx) = some (graph value ctx d) :=
  Json.readBytes_write _

/-- The actual graph byte encoder and decoder preserve the entire supplied
graph, including false arithmetic evidence and unreachable entries. -/
theorem decode_graph (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (hv : value.Lawful) (hc : ctx.Lawful) (context : Ctx)
    (p : DensePoly E) (lo hi : Endpoint E) (d : Dag E Ctx) (limits : Limits)
    (root : d.root < d.entries.size)
    (shape : ∀ e ∈ d.entries, Shape e.node)
    (subjects : ∀ e ∈ d.entries, bindings context p lo hi e.node = true)
    (bounds : ∀ (i : Nat) (h : i < d.entries.size), ∀ pair ∈ d.entries[i].children,
      pair.1 < i ∧ pair.2 < i)
    (bytes : checkBytes limits (d.encodeBytes value ctx) = .ok ()) :
    decodeGraph value ctx context p lo hi (d.encodeBytes value ctx) limits = .ok d := by
  unfold decodeGraph Dag.encodeBytes at *
  rw [parse_write _ _ bytes]
  simp only [bind, Except.bind]
  exact read_graph value ctx hv hc context p lo hi d root shape subjects bounds

/-- info: 'Hex.SignDet.Codec.decode_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decode_graph

end Hex.SignDet.Codec
