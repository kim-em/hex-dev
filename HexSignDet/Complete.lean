/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Descriptor

public section

namespace Hex.SignDet

/-- Select formal derivative slots without inventing a sign for a missing
slot. Index zero and every out-of-range index fail. -/
@[expose] def Thom.select (indices : List Nat) (signs : List Int) : Option (List Int) :=
  indices.mapM fun i => if 0 < i then signs[i - 1]? else none

/-- Restricting a complete derivative word to valid indices returns exactly
the values at those indices, including the empty list. -/
theorem Thom.select_full (n : Nat) (g : Nat → Int) (indices : List Nat)
    (h : ∀ i ∈ indices, 1 ≤ i ∧ i ≤ n) :
    Thom.select indices ((List.range n).map fun j => g (j + 1)) =
      some (indices.map g) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    have hi := h i (by simp)
    have hrest : ∀ j ∈ rest, 1 ≤ j ∧ j ≤ n := by
      intro j hj
      exact h j (by simp [hj])
    have hget : ((List.range n).map fun j => g (j + 1))[i - 1]? = some (g i) := by
      have hlt : i - 1 < n := by omega
      have hlt' : i - 1 < ((List.range n).map fun j => g (j + 1)).length := by
        simpa only [List.length_map, List.length_range] using hlt
      rw [List.getElem?_eq_getElem hlt']
      simp only [List.getElem_map, List.getElem_range, Nat.sub_add_cancel hi.1]
    have htail := ih hrest
    simp only [Thom.select] at htail
    have hpos : 0 < i := by omega
    simp only [Thom.select, List.mapM_cons, List.map_cons]
    simp only [hpos, ↓reduceIte]
    rw [hget, htail]
    rfl

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Canonically ordered full derivative slots, including the highest one. -/
@[expose] def RawDescriptor.full (raw : RawDescriptor E Ctx) (signs : List Int) :
    RawDescriptor E Ctx :=
  {raw with indices := (List.range raw.head.natDegree).map (· + 1), signs}

omit [One E] [Add E] [Sub E] [DecidableEq Ctx] in
theorem RawDescriptor.full_queries (raw : RawDescriptor E Ctx) (signs : List Int) :
    (raw.full signs).queries = (raw.full []).queries := rfl

omit [One E] [Add E] [Sub E] [DecidableEq Ctx] in
theorem RawDescriptor.full_queries_length (raw : RawDescriptor E Ctx) (signs : List Int) :
    (raw.full signs).queries.length = raw.head.natDegree := by
  simp only [queries, full, List.length_map, List.length_range]

omit [One E] [Add E] [Sub E] [DecidableEq Ctx] [Mul E] [NatCast E] in
/-- Canonical full slots need no repeated distinctness or range search once
the checked table supplies the sign word's length and ternary entries. -/
theorem RawDescriptor.full_wellFormed (raw : RawDescriptor E Ctx) (signs : List Int)
    (hp : 0 < raw.head.natDegree) (hlen : signs.length = raw.head.natDegree)
    (hs : signs.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) = true) :
    (raw.full signs).wellFormed = true := by
  change (decide (0 < raw.head.natDegree) &&
    decide (((List.range raw.head.natDegree).map (· + 1)).length = signs.length) &&
    decide ((List.range raw.head.natDegree).map (· + 1)).Nodup &&
    ((List.range raw.head.natDegree).map (· + 1)).all
      (fun i => decide (1 ≤ i ∧ i ≤ raw.head.natDegree)) &&
    signs.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1))) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hp, ?_⟩, ?_⟩, ?_⟩, hs⟩
  · simpa only [List.length_map, List.length_range] using hlen.symm
  · apply decide_eq_true
    apply (List.nodup_range (n := raw.head.natDegree)).map (· + 1)
    intro i j hne he
    exact hne (Nat.add_right_cancel he)
  · apply List.all_eq_true.mpr
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have hj := List.mem_range.mp hj
    simp only [decide_eq_true_eq]
    omega

/-- A completion retains the exact domain/context and all the old selected
derivative signs. Both descriptors must separately have count-one evidence. -/
@[expose] def RawDescriptor.completes (source target : RawDescriptor E Ctx) : Bool :=
  decide (target.context = source.context ∧ target.head = source.head ∧
    target.lower = source.lower ∧ target.upper = source.upper ∧
    target.indices = (List.range source.head.natDegree).map (· + 1)) &&
  decide (Thom.select source.indices target.signs = some source.signs)

/-- Checked completion evidence. Unique-root preservation additionally uses
the companion's semantic interpretation of both descriptor replays. -/
structure Completion {sign : E → Int} {context : Ctx}
    (source : Descriptor E Ctx sign context) where
  descriptor : Descriptor E Ctx sign context
  agrees : source.raw.completes descriptor.raw = true

theorem Completion.bindings {sign : E → Int} {context : Ctx}
    {source : Descriptor E Ctx sign context} (c : Completion source) :
    c.descriptor.raw.context = source.raw.context ∧
    c.descriptor.raw.head = source.raw.head ∧
    c.descriptor.raw.lower = source.raw.lower ∧
    c.descriptor.raw.upper = source.raw.upper ∧
    c.descriptor.raw.indices = (List.range source.raw.head.natDegree).map (· + 1) ∧
    Thom.select source.raw.indices c.descriptor.raw.signs = some source.raw.signs := by
  have h := c.agrees
  simp only [RawDescriptor.completes, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2, h.2⟩

/-- Thom comparison is applicable only to full derivative encodings of the
same literal head. Equal derivative vectors from different heads are rejected. -/
@[expose] def Descriptor.fullOrder {sign : E → Int} {context : Ctx}
    (left right : Descriptor E Ctx sign context) : Option Ordering :=
  if left.raw.head = right.raw.head ∧
      left.raw.indices = (List.range left.raw.head.natDegree).map (· + 1) ∧
      right.raw.indices = (List.range right.raw.head.natDegree).map (· + 1) then
    Thom.compareSigns left.raw.signs right.raw.signs
  else none

/-- Acceptance retains the applicability guards and the exact finite rule. -/
theorem Descriptor.fullOrder_eq {sign : E → Int} {context : Ctx}
    {left right : Descriptor E Ctx sign context} {order : Ordering}
    (h : left.fullOrder right = some order) :
    (left.raw.head = right.raw.head ∧
      left.raw.indices = (List.range left.raw.head.natDegree).map (· + 1) ∧
      right.raw.indices = (List.range right.raw.head.natDegree).map (· + 1)) ∧
    Thom.compareSigns left.raw.signs right.raw.signs = some order := by
  unfold fullOrder at h
  split at h
  · rename_i hg
    exact ⟨hg, h⟩
  · contradiction

variable [Neg E] [Inv E]

/-- Complete a descriptor by a full derivative table and checked restriction
to its old signs. Internal failures remain diagnostic until total producer
completeness and the required Thom foundation have been supplied. -/
def Descriptor.buildCompletion {sign : E → Int} {context : Ctx}
    (source : Descriptor E Ctx sign context) : Except BuildError (Completion source) :=
  match Sturm.prepare sign source.raw.head source.raw.lower source.raw.upper with
  | none => .error .replay
  | some domain =>
    let raw := source.raw.full []
    match buildPrepared context domain raw.queries with
    | .error err => .error err
    | .ok t =>
      let candidates := (t.val.table t.property).rows.toList.filter fun row =>
        decide (Thom.select source.raw.indices row.1 = some source.raw.signs)
      match candidates with
      | [(signs, 1)] =>
        match Descriptor.ofReplay? sign context (source.raw.full signs) t.val with
        | none => .error .replay
        | some target =>
          if h : source.raw.completes target.raw = true then .ok ⟨target, h⟩
          else .error .replay
      | _ => .error .system

end Hex.SignDet
