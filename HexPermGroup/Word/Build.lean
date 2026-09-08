/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Word

public section

namespace Hex.PermGroup.Program

/-- Evaluation of a concatenated program continues from the first prefix's values. -/
theorem evalNodes_append (S : Array (Perm n)) (xs ys : List Node)
    (values : Array {p : Perm n // Generated S p}) :
    evalNodes S (xs ++ ys) values =
      (evalNodes S xs values).bind (evalNodes S ys) := by
  induction xs generalizing values with
  | nil => rfl
  | cons node xs ih => simp [evalNodes, ih, Option.bind_assoc]

/-- Every accepted node contributes exactly one value. -/
theorem evalNodes_size {S : Array (Perm n)} {nodes : List Node}
    {values result : Array {p : Perm n // Generated S p}}
    (h : evalNodes S nodes values = some result) : result.size = values.size + nodes.length := by
  induction nodes generalizing values with
  | nil =>
    simp only [evalNodes, Option.some.injEq] at h
    subst result
    rfl
  | cons node nodes ih =>
    simp only [evalNodes] at h
    cases hn : evalNode S values node with
    | none => simp [hn] at h
    | some p =>
      simp only [hn] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih h

/-- An append-only program under construction, with cached values and checked
provenance. References share earlier nodes instead of expanding earlier words.
The invariant proof is erased during compilation. -/
structure Builder (S : Array (Perm n)) where
  nodes : Array Node
  values : Array {p : Perm n // Generated S p}
  valid : evalNodes S nodes.toList #[] = some values

namespace Builder

variable {n : Nat} {S : Array (Perm n)}

/-- The empty program, before a root is chosen. -/
@[expose] def empty (S : Array (Perm n)) : Builder S := ⟨#[], #[], rfl⟩

theorem size_eq (b : Builder S) : b.values.size = b.nodes.size := by
  simpa using evalNodes_size b.valid

/-- Append one node and its known value. The proof only relates this node to
cached earlier values; it never re-evaluates the preceding program at runtime. -/
@[expose] def push (b : Builder S) (node : Node) (p : {p : Perm n // Generated S p})
    (h : evalNode S b.values node = some p) : Builder S where
  nodes := b.nodes.push node
  values := b.values.push p
  valid := by
    simp only [Array.toList_push, evalNodes_append, b.valid, Option.bind_some,
      evalNodes, h]
    rfl

/-- The root added by a push; earlier roots remain valid after the append. -/
@[expose] def root (b : Builder S) (node : Node) (p : {p : Perm n // Generated S p})
    (h : evalNode S b.values node = some p) : Fin (b.push node p h).values.size :=
  ⟨b.values.size, by simp [push]⟩

@[expose] protected def id (b : Builder S) : Builder S :=
  b.push .id ⟨Perm.id n, .id⟩ rfl

@[expose] def generator (b : Builder S) (i : Fin S.size) : Builder S :=
  b.push (.generator i.val) ⟨S[i.val], .generator (Array.getElem_mem i.isLt)⟩
    (by simp [evalNode, i.isLt])

@[expose] def inv (b : Builder S) (i : Fin b.values.size) : Builder S :=
  b.push (.inv i.val) ⟨b.values[i.val].val.inv, .inv b.values[i.val].property⟩
    (by simp [evalNode])

@[expose] def comp (b : Builder S) (i j : Fin b.values.size) : Builder S :=
  b.push (.comp i.val j.val)
    ⟨b.values[i.val].val.comp b.values[j.val].val,
      .comp b.values[i.val].property b.values[j.val].property⟩
    (by simp [evalNode])

@[simp] theorem size_generator (b : Builder S) (i : Fin S.size) :
    (b.generator i).values.size = b.values.size + 1 := by
  simp [generator, push]

@[simp] theorem size_comp (b : Builder S) (i j : Fin b.values.size) :
    (b.comp i j).values.size = b.values.size + 1 := by
  simp [comp, push]

/-- Append a generator and its left product with an existing value. This is the
parent-edge operation used when compiling orbit discovery trees. -/
@[expose] def act (b : Builder S) (i : Fin S.size) (j : Fin b.values.size) : Builder S :=
  (b.generator i).comp ⟨b.values.size, by simp⟩ ⟨j.val, by simp; omega⟩

@[simp] theorem size_id (b : Builder S) : b.id.values.size = b.values.size + 1 := by
  simp [Builder.id, push]

@[simp] theorem size_act (b : Builder S) (i : Fin S.size) (j : Fin b.values.size) :
    (b.act i j).values.size = b.values.size + 2 := by simp [act, Nat.add_assoc]

theorem get_id (b : Builder S) (j : Fin b.values.size) :
    b.id.values[j.val] = b.values[j.val] := by
  simp [Builder.id, push, Array.getElem_push_lt j.isLt]

theorem last_id (b : Builder S) :
    b.id.values[b.values.size].val = Perm.id n := by simp [Builder.id, push]

theorem get_act (b : Builder S) (i : Fin S.size) (j k : Fin b.values.size) :
    (b.act i j).values[k.val] = b.values[k.val] := by
  simp [act, comp, generator, push, Array.getElem_push, k.isLt, Nat.lt_succ_of_lt k.isLt,
    j.isLt]

theorem last_act (b : Builder S) (i : Fin S.size) (j : Fin b.values.size) :
    (b.act i j).values[b.values.size + 1].val = S[i.val].comp b.values[j.val].val := by
  simp [act, comp, generator, push, Array.getElem_push, j.isLt]

/-- Select any already evaluated node as the root. The resulting raw certificate
shares the builder's node array; cached values and proof fields are not serialized. -/
@[expose] def program (b : Builder S) (i : Fin b.values.size) : Program :=
  ⟨b.nodes, i.val⟩

theorem eval_program (b : Builder S) (i : Fin b.values.size) :
    (b.program i).eval S = some b.values[i.val].val := by
  simp [program, eval, evalCertified, b.valid]

theorem check_program (b : Builder S) (i : Fin b.values.size) :
    checkWord S b.values[i.val].val (b.program i) = true :=
  decide_eq_true (eval_program b i)

end Builder

end Hex.PermGroup.Program
