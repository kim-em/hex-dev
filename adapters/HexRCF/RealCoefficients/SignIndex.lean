/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.LiteralSign
public section

/-! Index finite sign evidence without changing its authentication. -/

namespace Hex.RCF.RealCoefficients.LiteralSign

/-- A search tree contains positions in the original evidence array, rather
than independent signs. Routing is untrusted: a hit checks the complete key. -/
inductive Index where
  | empty
  | node (position : Nat) (left right : Index)
  deriving Repr

namespace Index

variable {D : Type u} [DecidableEq D]

/-- Out-of-range positions and unequal comparison ties remain missing hits.
The comparator chooses a route but never supplies proof evidence. -/
@[expose] def lookup (entries : Array (Entry D)) (compare : D → D → Ordering)
    (key : D) : Index → Option Int
  | .empty => none
  | .node position left right =>
    match entries[position]? with
    | none => none
    | some entry =>
      if entry.key = key then some entry.value
      else match compare key entry.key with
        | .lt => lookup entries compare key left
        | .eq => none
        | .gt => lookup entries compare key right

/-- Every hit comes from an original entry with precisely the requested key,
even for malformed routing or a comparator without order laws. -/
theorem lookup_entry (entries : Array (Entry D)) (compare : D → D → Ordering)
    (key : D) (index : Index) (value : Int)
    (hit : index.lookup entries compare key = some value) :
    ∃ entry ∈ entries.toList, entry.key = key ∧ entry.value = value := by
  induction index with
  | empty => simp only [lookup, reduceCtorEq] at hit
  | node position left right ihLeft ihRight =>
    cases found : entries[position]? with
    | none => simp only [lookup, found, reduceCtorEq] at hit
    | some entry =>
      simp only [lookup, found] at hit
      split at hit
      · rename_i same
        exact ⟨entry, Array.mem_toList_iff.mpr (Array.mem_of_getElem? found),
          same, Option.some.inj hit⟩
      · cases direction : compare key entry.key with
        | lt => exact ihLeft (by simpa only [direction] using hit)
        | eq => simp only [direction, reduceCtorEq] at hit
        | gt => exact ihRight (by simpa only [direction] using hit)

private def balanced : Nat → List Nat → Index
  | 0, _ => .empty
  | fuel + 1, positions =>
    let middle := positions.length / 2
    match positions[middle]? with
    | none => .empty
    | some position => .node position
        (balanced fuel (positions.take middle))
        (balanced fuel (positions.drop (middle + 1)))

/-- Sort positions by their keys and arrange a balanced routing tree.
The result is only an index; lookup still checks array bounds and exact keys. -/
def build (entries : Array (Entry D)) (compare : D → D → Ordering) : Index :=
  let ordered := entries.toList.zipIdx.mergeSort
    (fun left right => compare left.1.key right.1.key != .gt)
  balanced ordered.length (ordered.map Prod.snd)

end Index

namespace Table

variable {D : Type u} [DecidableEq D]

/-- Query the original evidence through an untrusted positional index.
A missing route uses the original linear lookup, preserving every recorded
hit even when the routing tree or comparator is malformed. -/
@[expose] def lookupIndex (table : Table D) (compare : D → D → Ordering)
    (index : Index) (key : D) : Option Int :=
  match index.lookup table.entries.toArray compare key with
  | some value => some value
  | none => table.lookup? key

/-- Indexing cannot lose a hit already recorded in the original table. -/
theorem lookupIndex_isSome (table : Table D) (compare : D → D → Ordering)
    (index : Index) (key : D) (recorded : (table.lookup? key).isSome = true) :
    (table.lookupIndex compare index key).isSome = true := by
  unfold lookupIndex
  cases index.lookup table.entries.toArray compare key with
  | none => exact recorded
  | some value => rfl

theorem lookupIndex_spec (table : Table D) (query : D → Hex.DensePoly Rat)
    (compare : D → D → Ordering) (index : Index) (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (accepted : table.check query = true) (key : D) (value : Int)
    (hit : table.lookupIndex compare index key = some value) :
    value = (SignType.sign (eval key) : Int) := by
  unfold lookupIndex at hit
  cases routed : index.lookup table.entries.toArray compare key with
  | none =>
      exact table.lookup_spec query eval x hx hl hu heval accepted key value
        (by simpa only [routed] using hit)
  | some found =>
      have sameValue : found = value := Option.some.inj (by simpa only [routed] using hit)
      obtain ⟨entry, member, same, valueEq⟩ := index.lookup_entry
        table.entries.toArray compare key found routed
      have actual := table.entry_spec query entry member x hx hl hu accepted
      rw [same, ← heval, valueEq, sameValue] at actual
      exact actual

/-- As with linear lookup, missing entries use the mathematical sign only.
Executable replay must resolve its finite reads from the checked table. -/
@[expose] noncomputable def signIndex (table : Table D) (compare : D → D → Ordering)
    (index : Index) (eval : D → ℝ) (key : D) : Int :=
  match table.lookupIndex compare index key with
  | some value => value
  | none => (SignType.sign (eval key) : Int)

theorem signIndex_spec (table : Table D) (query : D → Hex.DensePoly Rat)
    (compare : D → D → Ordering) (index : Index) (eval : D → ℝ) (x : ℝ)
    (hx : (realPoly table.head).IsRoot x)
    (hl : (table.lower : ℝ) < x) (hu : x < (table.upper : ℝ))
    (heval : ∀ a, eval a = (realPoly (query a)).eval x)
    (accepted : table.check query = true) (key : D) :
    table.signIndex compare index eval key = (SignType.sign (eval key) : Int) := by
  unfold signIndex
  cases hit : table.lookupIndex compare index key with
  | none => rfl
  | some value =>
    exact table.lookupIndex_spec query compare index eval x
      hx hl hu heval accepted key value hit

end Table
end Hex.RCF.RealCoefficients.LiteralSign
