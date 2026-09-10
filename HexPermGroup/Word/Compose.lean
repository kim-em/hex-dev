/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word.Build

public section

namespace Hex.PermGroup.Program

/-- Relocate node references when appending an independent program. Generator
indices address the same input array and are left unchanged. -/
@[expose] def shift (offset : Nat) : Node → Node
  | .id => .id
  | .generator i => .generator i
  | .inv i => .inv (offset + i)
  | .comp i j => .comp (offset + i) (offset + j)

theorem evalNode_shift (S : Array (Perm n))
    (pre values : Array {p : Perm n // Generated S p}) (node : Node) :
    evalNode S (pre ++ values) (shift pre.size node) = evalNode S values node := by
  cases node <;> simp [shift, evalNode, Array.getElem?_append_right]

theorem evalNodes_shift (S : Array (Perm n)) (nodes : List Node)
    (pre values : Array {p : Perm n // Generated S p}) :
    evalNodes S (nodes.map (shift pre.size)) (pre ++ values) =
      (evalNodes S nodes values).map (pre ++ ·) := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node nodes ih =>
    simp only [List.map_cons, evalNodes, evalNode_shift]
    cases he : evalNode S values node with
    | none => rfl
    | some p =>
      simpa using ih (values.push p)

/-- Every prefix of a successful evaluation retains its cached values. -/
theorem evalNodes_get {S : Array (Perm n)} {nodes : List Node}
    {values result : Array {p : Perm n // Generated S p}}
    (h : evalNodes S nodes values = some result) (i : Fin values.size) :
    result[i.val]? = some values[i.val] := by
  induction nodes generalizing values with
  | nil =>
    simp only [evalNodes, Option.some.injEq] at h
    subst result
    simp
  | cons node nodes ih =>
    simp only [evalNodes] at h
    cases he : evalNode S values node with
    | none => simp [he] at h
    | some p =>
      simp only [he] at h
      simpa [Array.getElem_push_lt i.isLt] using ih h ⟨i.val, by simp; omega⟩

theorem eval_values {S : Array (Perm n)} {w : Program} {p : Perm n}
    (h : w.eval S = some p) :
    ∃ values : Array {p : Perm n // Generated S p},
      evalNodes S w.nodes.toList #[] = some values ∧
      ∃ hi : w.root < values.size, values[w.root].val = p := by
  unfold eval evalCertified at h
  cases he : evalNodes S w.nodes.toList #[] with
  | none => simp [he] at h
  | some values =>
    simp only [he] at h
    by_cases hi : w.root < values.size
    · exact ⟨values, rfl, hi, by simpa [hi] using h⟩
    · simp [Array.getElem?_eq_none (Nat.le_of_not_gt hi)] at h

/-- Append an inverse node without expanding the program's expression. -/
@[expose] protected def inv (w : Program) : Program :=
  ⟨w.nodes.push (.inv w.root), w.nodes.size⟩

theorem eval_inv {S : Array (Perm n)} {w : Program} {p : Perm n}
    (h : w.eval S = some p) : w.inv.eval S = some p.inv := by
  obtain ⟨values, hv, hi, he⟩ := eval_values h
  have hs : values.size = w.nodes.size := by simpa using evalNodes_size hv
  simp [Program.inv, eval, evalCertified, evalNodes_append, hv, evalNodes, evalNode,
    hi, ← hs, he]

/-- Compose programs by relocating the right program, then adding one product
node. Each input DAG is copied once; its internal shared references stay shared. -/
@[expose] protected def comp (u v : Program) : Program :=
  ⟨(u.nodes ++ v.nodes.map (shift u.nodes.size)).push (.comp u.root (u.nodes.size + v.root)),
    u.nodes.size + v.nodes.size⟩

theorem eval_comp {S : Array (Perm n)} {u v : Program} {p q : Perm n}
    (hu : u.eval S = some p) (hv : v.eval S = some q) :
    (u.comp v).eval S = some (p.comp q) := by
  obtain ⟨us, hus, hi, he⟩ := eval_values hu
  obtain ⟨vs, hvs, hj, hf⟩ := eval_values hv
  have hs : us.size = u.nodes.size := by simpa using evalNodes_size hus
  have ht : vs.size = v.nodes.size := by simpa using evalNodes_size hvs
  have hjoin : evalNodes S (v.nodes.toList.map (shift us.size)) us = some (us ++ vs) := by
    simpa [hvs] using evalNodes_shift S v.nodes.toList us #[]
  simp [Program.comp, eval, evalCertified, evalNodes_append, hus, hjoin, evalNodes, evalNode,
    Array.getElem?_append_left hi, ← hs, ← ht, hi, hj, he, hf]

end Hex.PermGroup.Program
