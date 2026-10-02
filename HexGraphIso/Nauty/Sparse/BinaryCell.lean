/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryIndex
public import HexGraphIso.Nauty.Sparse.BinaryCells
public import HexGraphIso.Nauty.Sparse.CompactClasses

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- The input vertices traversed by one singleton-cell scan. -/
@[expose] def seen (lab : Array Nat) (first last : Nat) : List Nat :=
  (List.range' first (last - first)).map fun q => lab[q]!

@[expose] def hits (lab : Array Nat) (pred : Nat → Bool) (first last : Nat) : Nat :=
  ((seen lab first last).filter pred).length

@[expose] def cut (lab : Array Nat) (pred : Nat → Bool) (first last : Nat) : Nat :=
  first + ((seen lab first last).filter fun v => !pred v).length

theorem seen_eq (lab : Array Nat) (first last : Nat) :
    seen lab first last = segN lab first (last - first) := by
  simp only [seen, List.range'_eq_map_range, List.map_map, segN]
  rfl

/-- Observations of one complete executed singleton-cell body. The cut and
hit count refer to its input traversal; the loop theorem derives every
field from the executed compaction, reverse fill and finalization. -/
structure Cell (level first last : Nat) (pred : Nat → Bool) (s t : RefineSt n) : Prop where
  control : CountTrace.control t =
    (((CountTrace.control s).hash first).hash (hits s.lab pred first last)).binary
      first (cut s.lab pred first last) last
  ptn : t.ptn = if cut s.lab pred first last ≠ last ∧ cut s.lab pred first last ≠ first then
    s.ptn.set! (cut s.lab pred first last - 1) level else s.ptn
  count : t.numcells = if cut s.lab pred first last ≠ last ∧ cut s.lab pred first last ≠ first then
    s.numcells + 1 else s.numcells
  frame : CountFrame s t
  window : Sort.Window s.lab t.lab first last
  retained : segN t.lab first (cut s.lab pred first last - first) =
    (seen s.lab first last).filter (fun v => !pred v)
  collected : segN t.lab (cut s.lab pred first last) (last - cut s.lab pred first last) =
    ((seen s.lab first last).filter pred).reverse
  cache : s.lab.toList.Perm (List.range n) → s.ptn.size = n →
    Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
    IsCell s.ptn level first (last - first) → first + 1 < last →
    Index.Valid n t.lab t.ptn level t.cellstart t.cellend

end Hex.GraphIso.Nauty.Sparse.Binary
