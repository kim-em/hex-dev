/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexFinish
public import HexGraphIso.Nauty.Sparse.Window

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- Cache entries outside the cell being split retain their old meaning. -/
structure Frame (n first last : Nat) (oldlab lab oldstarts starts oldends ends : Array Nat) : Prop where
  ends : ∀ q, q < first ∨ last < q → ends[q]! = oldends[q]!
  starts : ∀ q, q < n → q < first ∨ last < q → starts[lab[q]!]! = oldstarts[oldlab[q]!]!

namespace Frame

variable {n first last a value : Nat}
variable {oldlab lab oldstarts starts oldends ends : Array Nat}

theorem of_window (hw : Sort.Window oldlab lab first (last + 1)) :
    Frame n first last oldlab lab starts starts ends ends := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro q hq ho
  rw [hw.outside q (by omega)]

theorem set_end (h : Frame n first last oldlab lab oldstarts starts oldends ends)
    (ha : first ≤ a ∧ a ≤ last) :
    Frame n first last oldlab lab oldstarts starts oldends (ends.setIfInBounds a value) := by
  refine ⟨?_, h.starts⟩
  intro q hq
  change (ends.set! a value)[q]! = oldends[q]!
  rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
  exact h.ends q hq

theorem set_start (h : Frame n first last oldlab lab oldstarts starts oldends ends)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (ha : first ≤ a ∧ a ≤ last) (hb : a < n) :
    Frame n first last oldlab lab oldstarts (starts.setIfInBounds lab[a]! value) oldends ends := by
  refine ⟨h.ends, ?_⟩
  intro q hq ho
  change (starts.set! lab[a]! value)[lab[q]!]! = oldstarts[oldlab[q]!]!
  rw [Array.getElem!_set!_ne _ _ _ _ (fun he => by have := hinj a q hb hq he; omega)]
  exact h.starts q hq ho

theorem scatter (h : Frame n first last oldlab lab oldstarts starts oldends ends)
    (hs : Scatter n lab starts out a upto value) (ha : first ≤ a) (hb : upto ≤ last + 1) :
    Frame n first last oldlab lab oldstarts out oldends ends := by
  refine ⟨h.ends, ?_⟩
  intro q hq ho
  rw [hs.get q hq, ite_eq_right (by omega)]
  exact h.starts q hq ho

theorem relabel (h : Frame n first last oldlab lab oldstarts starts oldends ends)
    (hw : Sort.Window lab out first (last + 1)) :
    Frame n first last oldlab out oldstarts starts oldends ends := by
  refine ⟨h.ends, ?_⟩
  intro q hq ho
  rw [hw.outside q (by omega)]
  exact h.starts q hq ho

end Frame

end Hex.GraphIso.Nauty.Sparse.Index
