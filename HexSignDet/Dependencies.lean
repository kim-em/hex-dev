/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Basic

public section

namespace Hex.SignDet.Dependencies

open Codec (Json)

/-- A reference includes the full literal subject, not only a context hash.
The local packet reader interprets that subject and checks its mathematical
binding; this layer checks that the referenced entry has exactly that subject. -/
structure Reference where
  index : Nat
  level : Nat
  subject : Json
  deriving DecidableEq, Repr

/-- One coefficient-level packet. Same-level table recursion remains inside
the payload's existing BKR graph. Every dependency is strictly lower level. -/
structure Entry where
  level : Nat
  subject : Json
  payload : Json
  children : Array Reference
  deriving DecidableEq, Repr

/-- Several results may refer to one stored packet. Entry order is the
checking order, and all entries are checked, including unreachable ones. -/
structure Graph where
  entries : Array Entry
  roots : Array Reference
  deriving DecidableEq, Repr

@[expose] def Reference.matches (reference : Reference) (entry : Entry) : Bool :=
  decide (reference.level = entry.level ∧ reference.subject = entry.subject)

/-- Check the declared result binding before interpreting its packet. -/
@[expose] def Reference.check (reference : Reference) (entries : Array Entry) : Bool :=
  match entries[reference.index]? with
  | none => false
  | some entry => reference.matches entry

/-- Structural checking never interprets a coefficient or executes a sign
query. Arithmetic and sign validity belong to the supplied local reader. -/
@[expose] def Graph.check (graph : Graph) : Bool :=
  graph.roots.all (fun root => root.check graph.entries) &&
    graph.entries.toList.zipIdx.all (fun (entry, index) =>
      entry.children.all fun child =>
        decide (child.index < index ∧ child.level < entry.level) &&
          child.check graph.entries)

/-- A memo retains the literal packet next to its reader's typed result.
The result type may depend on the whole packet and its coefficient context. -/
structure Checked (Result : Entry → Type u) where
  entry : Entry
  value : Result entry

variable {Result : Entry → Type u}

/-- Read declared children from the accepted prefix. Both subject and level
checks precede the local reader; missing evidence never invokes that reader. -/
@[expose] def children? (entry : Entry) (memo : Array (Checked Result)) :
    Option (Array (Checked Result)) :=
  entry.children.mapM fun reference => do
    let child ← memo[reference.index]?
    if reference.matches child.entry && decide (child.entry.level < entry.level) then
      some child
    else none

/-- Run the local packet reader exactly once, using only its declared,
already checked lower-level results. The reader still owns complete coverage
of every coefficient fact needed to validate its payload. -/
@[expose] def step (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (memo : Array (Checked Result)) (entry : Entry) : Option (Checked Result) := do
  let children ← children? entry memo
  let value ← read entry children
  return ⟨entry, value⟩

/-- Validate the finite envelope, then check each packet once. This does not
replace the local BKR or coefficient reader with a structural soundness claim. -/
@[expose] def Graph.validate?
    (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (graph : Graph) : Option (Array (Checked Result)) :=
  if graph.check then
    graph.entries.foldlM (init := #[]) fun memo entry => do
      let next ← step read memo entry
      return memo.push next
  else none

/-- Successful structural reference checking establishes literal binding
and a valid array index. -/
theorem Reference.check_eq (reference : Reference) (entries : Array Entry) :
    reference.check entries = true ↔
      ∃ bound : reference.index < entries.size,
        reference.level = entries[reference.index].level ∧
        reference.subject = entries[reference.index].subject := by
  unfold check
  cases h : entries[reference.index]? with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨bound, _, _⟩
    simp only [Array.getElem?_eq_getElem bound] at h
    contradiction
  | some entry =>
    obtain ⟨bound, same⟩ := Array.getElem?_eq_some_iff.mp h
    simp only [Reference.matches, decide_eq_true_eq, ← same]
    exact ⟨fun accepted => ⟨bound, accepted⟩, fun ⟨_, accepted⟩ => accepted⟩

/-- Every accepted dependency points strictly backward, decreases level and
retains the exact referenced subject. This includes unreachable entries. -/
theorem Graph.check_children (graph : Graph) (accepted : graph.check = true)
    (index : Nat) (bound : index < graph.entries.size)
    (child : Reference) (member : child ∈ graph.entries[index].children) :
    child.index < index ∧ child.level < graph.entries[index].level ∧
      ∃ bound : child.index < graph.entries.size,
        child.level = graph.entries[child.index].level ∧
        child.subject = graph.entries[child.index].subject := by
  simp only [Graph.check, Bool.and_eq_true] at accepted
  have checked := accepted.2
  have entry := List.all_eq_true.mp checked (graph.entries[index], index)
    (by
      apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp only [List.getElem?_eq_getElem
        (show index < graph.entries.toList.length from bound), Array.getElem_toList])
  have edge := Array.all_eq_true_iff_forall_mem.mp entry child member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at edge
  exact ⟨edge.1.1, edge.1.2, (Reference.check_eq child graph.entries).mp edge.2⟩

/-- Every declared result references an existing entry with the requested
coefficient level and exact subject. -/
theorem Graph.check_roots (graph : Graph) (accepted : graph.check = true)
    (root : Reference) (member : root ∈ graph.roots) :
    ∃ bound : root.index < graph.entries.size,
      root.level = graph.entries[root.index].level ∧
      root.subject = graph.entries[root.index].subject := by
  simp only [Graph.check, Bool.and_eq_true] at accepted
  exact (Reference.check_eq root graph.entries).mp
    (Array.all_eq_true_iff_forall_mem.mp accepted.1 root member)

/-- A successful local reader retains the exact supplied entry. -/
theorem step_entry (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (memo : Array (Checked Result)) (entry : Entry) (next : Checked Result)
    (accepted : step read memo entry = some next) : next.entry = entry := by
  unfold step at accepted
  cases children : children? entry memo with
  | none => simp [children, bind, Option.bind] at accepted
  | some inputs =>
    cases value : read entry inputs with
    | none => simp [children, value, bind, Option.bind] at accepted
    | some result =>
      simp only [children, value, bind, Option.bind, pure, Option.some.injEq] at accepted
      subst next
      rfl

private theorem fold_entries
    (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (entries : List Entry) (memo result : Array (Checked Result))
    (accepted : entries.foldlM (fun memo entry => do
      let next ← step read memo entry
      return memo.push next) memo = some result) :
    result.toList.map Checked.entry = memo.toList.map Checked.entry ++ entries := by
  induction entries generalizing memo result with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at accepted
    subst result
    simp
  | cons entry entries ih =>
    simp only [List.foldlM_cons] at accepted
    cases h : step read memo entry with
    | none => simp [h, bind, Option.bind] at accepted
    | some next =>
      simp only [h, bind, Option.bind, pure] at accepted
      have same := step_entry read memo entry next h
      simpa only [Array.toList_push, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, same] using ih (memo.push next) result accepted

/-- Every stored packet is checked, in wire order. Returned memo entries
retain the exact original subjects, payloads and child references. -/
theorem Graph.validate_entries
    (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (graph : Graph) (memo : Array (Checked Result))
    (accepted : graph.validate? read = some memo) : memo.map Checked.entry = graph.entries := by
  unfold validate? at accepted
  split at accepted
  · rw [← Array.foldlM_toList] at accepted
    have entries := fold_entries read graph.entries.toList #[] memo accepted
    apply Array.toList_inj.mp
    simpa only [Array.toList_map, Array.toList_empty, List.map_nil, List.nil_append]
      using entries
  · contradiction

/-- Structural validity follows from actual typed packet acceptance. -/
theorem Graph.validate_check
    (read : (entry : Entry) → Array (Checked Result) → Option (Result entry))
    (graph : Graph) (memo : Array (Checked Result))
    (accepted : graph.validate? read = some memo) : graph.check = true := by
  unfold validate? at accepted
  split at accepted
  · assumption
  · contradiction

end Hex.SignDet.Dependencies

/-- info: 'Hex.SignDet.Dependencies.Graph.check_children' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dependencies.Graph.check_children
/-- info: 'Hex.SignDet.Dependencies.Graph.validate_entries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dependencies.Graph.validate_entries
/-- info: 'Hex.SignDet.Dependencies.Graph.validate_check' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Dependencies.Graph.validate_check
