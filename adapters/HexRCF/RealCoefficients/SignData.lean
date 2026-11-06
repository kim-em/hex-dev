/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski
public section

/-! Literal sign entries and positional routing, independent of real semantics. -/

namespace Hex.RCF.RealCoefficients.LiteralSign

/-- A sign attached to an exact key. Consumers authenticate its value and any
retained rational query evidence against their own fixed interpretation. -/
structure Entry (D : Type u) where
  key : D
  value : Int
  evidence : Option (TarskiCertificate Rat Rat Unit)

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

end Hex.RCF.RealCoefficients.LiteralSign
