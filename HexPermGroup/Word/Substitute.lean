/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word.Compose
public import HexPermGroup.Check

public section

namespace Hex.PermGroup.Program

theorem evalNodes_generators {S : Array (Perm n)} {nodes : List Node}
    {values result : Array {p : Perm n // Generated S p}}
    (h : evalNodes S nodes values = some result) {i : Nat}
    (hi : Node.generator i ∈ nodes) : i < S.size := by
  induction nodes generalizing values with
  | nil => simp at hi
  | cons node nodes ih =>
    simp only [evalNodes] at h
    cases he : evalNode S values node with
    | none => simp [he] at h
    | some p =>
      rcases List.mem_cons.mp hi with hn | hi
      · subst node
        by_cases hi : i < S.size
        · exact hi
        · simp [evalNode, hi] at he
      · exact ih (by simpa [he] using h) hi

theorem generator_bound {S : Array (Perm n)} {w : Program} {p : Perm n}
    (h : w.eval S = some p) {i : Nat} (hi : Node.generator i ∈ w.nodes) : i < S.size := by
  obtain ⟨values, hv, _⟩ := eval_values h
  exact evalNodes_generators hv (by simpa using hi)

/-- A shared prefix containing replacement programs for the first `k` generators.
The first node is identity, used to redirect generator nodes through products.
Semantic caches occur only in erased proofs, not in the runtime prefix. -/
structure Substitution (S T : Array (Perm n)) (k : Nat) where
  nodes : Array Node
  roots : Vector Nat k
  size : k ≤ T.size
  valid : ∃ values : Array {p : Perm n // Generated S p},
    evalNodes S nodes.toList #[] = some values ∧
    (∃ h : 0 < values.size, values[0].val = Perm.id n) ∧
    ∀ j : Fin k, ∃ h : roots[j.val] < values.size, values[roots[j.val]].val = T[j.val]

namespace Substitution

variable {n : Nat} {S T : Array (Perm n)} {k : Nat}

@[expose] def empty (S T : Array (Perm n)) : Substitution S T 0 where
  nodes := #[.id]
  roots := #v[]
  size := Nat.zero_le _
  valid := ⟨#[⟨Perm.id n, .id⟩], rfl, ⟨by simp, rfl⟩, fun j => nomatch j⟩

/-- Append one replacement program once, preserving all earlier roots. -/
@[expose] def push (c : Substitution S T k) (hk : k < T.size) (w : Program)
    (hw : checkWord S T[k] w = true) : Substitution S T (k + 1) where
  nodes := c.nodes ++ w.nodes.map (shift c.nodes.size)
  roots := c.roots.push (c.nodes.size + w.root)
  size := hk
  valid := by
    obtain ⟨pre, hp, ⟨hz, hid⟩, hr⟩ := c.valid
    obtain ⟨values, hv, hwroot, hwval⟩ := eval_values (of_decide_eq_true hw)
    have hs : pre.size = c.nodes.size := by simpa using evalNodes_size hp
    have he : evalNodes S (w.nodes.toList.map (shift c.nodes.size)) pre = some (pre ++ values) := by
      simpa [hs, hv] using evalNodes_shift S w.nodes.toList pre #[]
    refine ⟨pre ++ values, ?_, ?_, ?_⟩
    · simp [evalNodes_append, hp, he]
    · exact ⟨by simp; omega, by simpa [Array.getElem_append_left hz] using hid⟩
    · intro ⟨j, hj⟩
      by_cases hlt : j < k
      · obtain ⟨hbound, hval⟩ := hr ⟨j, hlt⟩
        change c.roots[j] < pre.size at hbound
        refine ⟨by simp [Vector.getElem_push_lt hlt]; omega, ?_⟩
        simpa [Vector.getElem_push_lt hlt, Array.getElem_append_left hbound] using hval
      · have hjk : j = k := by omega
        subst j
        refine ⟨by simp [← hs]; omega, ?_⟩
        simpa [← hs, Array.getElem_append_right] using hwval

@[expose] def finish {k : Nat} (c : Substitution S T k) (words : Vector Program T.size)
    (hw : checkWords S T words = true) : Substitution S T T.size :=
  if hk : k < T.size then
    finish (c.push hk words[k] ((of_decide_eq_true hw) ⟨k, hk⟩)) words hw
  else cast (congrArg (Substitution S T) (Nat.le_antisymm c.size (Nat.le_of_not_gt hk))) c
termination_by T.size - k

theorem finish_size {k : Nat} (c : Substitution S T k) (words : Vector Program T.size)
    (hw : checkWords S T words = true) :
    (c.finish words hw).nodes.size = c.nodes.size +
      ((words.toList.drop k).map fun w => w.nodes.size).sum := by
  rw [finish]
  split
  · rename_i hk
    rw [finish_size]
    have hl : k < words.toList.length := by simpa using hk
    rw [List.drop_eq_getElem_cons hl]
    simp [push, Nat.add_assoc]
  · rename_i hk
    have he : k = T.size := Nat.le_antisymm c.size (Nat.le_of_not_gt hk)
    subst k
    have hd : words.toList.drop T.size = [] := List.drop_eq_nil_of_le (by simp)
    simp only [cast_eq, hd, List.map_nil, List.sum_nil, Nat.add_zero]
termination_by T.size - k

theorem generated (c : Substitution S T T.size) {p : Perm n} (hp : Generated T p) : Generated S p := by
  apply hp.mono
  intro q hq
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hq
  obtain ⟨values, _, _, hr⟩ := c.valid
  obtain ⟨hi, he⟩ := hr ⟨j, hj⟩
  exact he ▸ values[c.roots[j]].property

/-- Convert cached source values in proofs of substitution correctness. -/
@[expose] def lift (c : Substitution S T T.size) (p : {p : Perm n // Generated T p}) :
    {p : Perm n // Generated S p} := ⟨p.val, c.generated p.property⟩

/-- Translate one node with a fixed offset. A generator becomes a reference to
its shared replacement root multiplied by the prefix's identity node. -/
@[expose] def node (c : Substitution S T T.size) (source : Node)
    (h : ∀ i, source = .generator i → i < T.size) : Node :=
  match source with
  | .id => .id
  | .generator i => .comp (c.roots[i]'(h i rfl)) 0
  | .inv i => .inv (c.nodes.size + i)
  | .comp i j => .comp (c.nodes.size + i) (c.nodes.size + j)

@[expose] def translate (c : Substitution S T T.size) :
    (nodes : List Node) → (∀ i, Node.generator i ∈ nodes → i < T.size) → List Node
  | [], _ => []
  | source :: nodes, h =>
    c.node source (fun i hi => h i (hi ▸ List.mem_cons_self ..)) ::
      c.translate nodes (fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem translate_length (c : Substitution S T T.size) (nodes : List Node)
    (h : ∀ i, Node.generator i ∈ nodes → i < T.size) :
    (c.translate nodes h).length = nodes.length := by
  induction nodes with
  | nil => rfl
  | cons source nodes ih => simp only [translate, List.length_cons, ih]

theorem evalNode_node (c : Substitution S T T.size)
    (pre : Array {p : Perm n // Generated S p}) (hs : pre.size = c.nodes.size)
    (hz : 0 < pre.size) (hid : pre[0].val = Perm.id n)
    (hr : ∀ j : Fin T.size, ∃ h : c.roots[j.val] < pre.size, pre[c.roots[j.val]].val = T[j.val])
    (values : Array {p : Perm n // Generated T p}) (source : Node)
    (hbound : ∀ i, source = .generator i → i < T.size)
    (p : {p : Perm n // Generated T p}) (h : evalNode T values source = some p) :
    evalNode S (pre ++ values.map c.lift) (c.node source hbound) = some (c.lift p) := by
  cases source with
  | id =>
    simp only [evalNode, Option.some.injEq] at h
    subst p
    rfl
  | generator i =>
    have hi := hbound i rfl
    obtain ⟨hj, he⟩ := hr ⟨i, hi⟩
    change c.roots[i] < pre.size at hj
    simp only [evalNode, dite_eq_left hi, Option.some.injEq] at h
    subst p
    simp [node, evalNode, Array.getElem?_append_left hj, Array.getElem?_append_left hz,
      hj, hz, he, hid, lift]
  | inv i =>
    by_cases hi : i < values.size
    · simp [evalNode, hi] at h
      subst p
      simp [node, evalNode, ← hs, hi, lift]
    · simp [evalNode, Array.getElem?_eq_none (Nat.le_of_not_gt hi)] at h
  | comp i j =>
    by_cases hi : i < values.size
    · by_cases hj : j < values.size
      · simp [evalNode, hi, hj] at h
        subst p
        simp [node, evalNode, ← hs, hi, hj, lift]
      · simp [evalNode, Array.getElem?_eq_none (Nat.le_of_not_gt hj)] at h
    · simp [evalNode, Array.getElem?_eq_none (Nat.le_of_not_gt hi)] at h

theorem evalNodes_translate (c : Substitution S T T.size)
    (pre : Array {p : Perm n // Generated S p}) (hs : pre.size = c.nodes.size)
    (hz : 0 < pre.size) (hid : pre[0].val = Perm.id n)
    (hr : ∀ j : Fin T.size, ∃ h : c.roots[j.val] < pre.size, pre[c.roots[j.val]].val = T[j.val])
    (nodes : List Node) (hbound : ∀ i, Node.generator i ∈ nodes → i < T.size)
    (values result : Array {p : Perm n // Generated T p}) (h : evalNodes T nodes values = some result) :
    evalNodes S (c.translate nodes hbound) (pre ++ values.map c.lift) =
      some (pre ++ result.map c.lift) := by
  induction nodes generalizing values with
  | nil =>
    simp only [evalNodes, Option.some.injEq] at h
    subst result
    rfl
  | cons source nodes ih =>
    simp only [evalNodes] at h
    cases he : evalNode T values source with
    | none => simp [he] at h
    | some p =>
      have hn := c.evalNode_node pre hs hz hid hr values source
        (fun i hi => hbound i (hi ▸ List.mem_cons_self ..)) p he
      have ht := ih (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) (values.push p)
        (by simpa [he] using h)
      simpa [translate, evalNodes, hn] using ht

/-- Substitute a checked program, adding its nodes once after the shared prefix. -/
@[expose] def program (c : Substitution S T T.size) (w : Program) {p : Perm n}
    (hw : checkWord T p w = true) : Program :=
  ⟨c.nodes ++ (c.translate w.nodes.toList (fun i hi => generator_bound
      (of_decide_eq_true hw) (by simpa using hi))).toArray,
    c.nodes.size + w.root⟩

theorem program_size (c : Substitution S T T.size) (w : Program) {p : Perm n}
    (hw : checkWord T p w = true) :
    (c.program w hw).nodes.size = c.nodes.size + w.nodes.size := by
  simp [program, translate_length]

theorem check_program (c : Substitution S T T.size) (w : Program) {p : Perm n}
    (hw : checkWord T p w = true) : checkWord S p (c.program w hw) = true := by
  obtain ⟨pre, hp, ⟨hz, hid⟩, hr⟩ := c.valid
  obtain ⟨values, hv, hi, he⟩ := eval_values (of_decide_eq_true hw)
  have hs : pre.size = c.nodes.size := by simpa using evalNodes_size hp
  have ht := c.evalNodes_translate pre hs hz hid hr w.nodes.toList
    (fun i hi => generator_bound (of_decide_eq_true hw) (by simpa using hi)) #[] values hv
  simp only [Array.map_empty, Array.append_empty] at ht
  apply decide_eq_true
  simp [program, eval, evalCertified, evalNodes_append, hp, ht,
    ← hs, hi, lift, he]

end Substitution

/-- Substitute replacement programs once per input generator, then redirect all
references to their shared roots. This does not expand a program into a word. -/
@[expose] def substitute (S T : Array (Perm n)) (words : Vector Program T.size)
    (hwords : checkWords S T words = true) (w : Program) {p : Perm n}
    (hw : checkWord T p w = true) : Program :=
  ((Substitution.empty S T).finish words hwords).program w hw

theorem check_substitute (S T : Array (Perm n)) (words : Vector Program T.size)
    (hwords : checkWords S T words = true) (w : Program) {p : Perm n}
    (hw : checkWord T p w = true) : checkWord S p (substitute S T words hwords w hw) = true :=
  Substitution.check_program ..

/-- Each replacement and each source node is stored exactly once, with one
additional identity node. Repeated references do not increase this bound. -/
theorem substitute_size (S T : Array (Perm n)) (words : Vector Program T.size)
    (hwords : checkWords S T words = true) (w : Program) {p : Perm n}
    (hw : checkWord T p w = true) :
    (substitute S T words hwords w hw).nodes.size =
      1 + (words.toList.map fun w => w.nodes.size).sum + w.nodes.size := by
  simp [substitute, Substitution.program_size, Substitution.finish_size, Substitution.empty]

end Hex.PermGroup.Program
