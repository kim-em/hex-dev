/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagEncode
public import Std.Data.HashMap.Lemmas

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameEncode
open Hex.SignDet Hex.SignDet.Dag

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [DecidableEq Ctx] [Hashable E] [Hashable Ctx]

/-- First-occurrence interning using structural list search. -/
@[expose] def insert (entries : Array (Entry E Ctx)) (entry : Entry E Ctx) :
    Array (Entry E Ctx) × Nat :=
  match entries.toList.idxOf? entry with
  | some index => (entries, index)
  | none => (entries.push entry, entries.size)

/-- The cache records exactly the first occurrence of every stored entry. -/
def Consistent (state : Encoder E Ctx) : Prop :=
  ∀ entry, state.indices[entry]? = state.entries.toList.idxOf? entry

theorem consistent_empty : Consistent ({} : Encoder E Ctx) := by
  intro entry
  simp

/-- The linear lookup preserves both the exact output and the cache invariant. -/
theorem insert_eq (state : Encoder E Ctx) (entry : Entry E Ctx)
    (consistent : Consistent state) :
    insert state.entries entry = ((state.insert entry).1.entries, (state.insert entry).2) ∧
      Consistent (state.insert entry).1 := by
  cases lookup : state.indices[entry]? with
  | some index =>
    have found : state.entries.toList.idxOf? entry = some index :=
      (consistent entry).symm.trans lookup
    constructor
    · simp only [insert, found, Encoder.insert, lookup]
    · simpa only [Encoder.insert, lookup] using consistent
  | none =>
    have missing : state.entries.toList.idxOf? entry = none :=
      (consistent entry).symm.trans lookup
    constructor
    · simp only [insert, missing, Encoder.insert, lookup]
    · intro key
      simp only [Encoder.insert, lookup, Std.HashMap.getElem?_insert,
        Array.toList_push, List.idxOf?, List.findIdx?_append]
      by_cases same : entry = key
      · subst key
        simp only [List.idxOf?] at missing
        simp [missing]
      · have different : (entry == key) = false := by simp [same]
        rw [different]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [consistent key]
        simp [different, List.idxOf?]

/-- Structural postorder traversal retaining the first exact occurrence. -/
@[expose] def loop (entries : Array (Entry E Ctx)) : Replay E Ctx →
    Array (Entry E Ctx) × Nat
  | .leaf node => insert entries ⟨node, none⟩
  | .split node left right =>
    let (entries, first) := loop entries left
    let (entries, second) := loop entries right
    insert entries ⟨node, some (first, second)⟩

/-- Both traversals retain identical entries and root indices at every step. -/
theorem loop_eq (tree : Replay E Ctx) (state : Encoder E Ctx)
    (consistent : Consistent state) :
    loop state.entries tree = ((encodeFrom state tree).1.entries, (encodeFrom state tree).2) ∧
      Consistent (encodeFrom state tree).1 := by
  induction tree generalizing state with
  | leaf node => exact insert_eq state ⟨node, none⟩ consistent
  | split node left right leftIH rightIH =>
    have first := leftIH state consistent
    have second := rightIH (encodeFrom state left).1 first.2
    have added := insert_eq (encodeFrom (encodeFrom state left).1 right).1
      ⟨node, some ((encodeFrom state left).2, (encodeFrom (encodeFrom state left).1 right).2)⟩
      second.2
    simpa only [loop, first.1, second.1, encodeFrom] using added

/-- A reducible frame encoder with the same complete packet as hash interning.
The hash instances are retained to match the compiled encoder's signature. -/
@[expose] def encodeLinear [Hashable E] [Hashable Ctx] (tree : Replay E Ctx) : Dag E Ctx :=
  let (entries, root) := loop #[] tree
  ⟨entries, root⟩

/-- Compiled serialization keeps the existing hash-map implementation. -/
@[csimp] theorem encodeLinear_eq : @encodeLinear = @Hex.SignDet.Dag.encode := by
  funext E Ctx _ _ _ _ _ tree
  have agrees := (loop_eq tree ({} : Encoder E Ctx) consistent_empty).1
  unfold encodeLinear Hex.SignDet.Dag.encode
  rw [agrees]

end Hex.RealClosure.Algebraic.KernelReplay.FrameEncode

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameEncode.encodeLinear_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameEncode.encodeLinear_eq
