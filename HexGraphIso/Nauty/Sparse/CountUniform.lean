/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
public import HexGraphIso.Nauty.Sparse.SortProps
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

/-- A uniform count cell returns immediately after hashing its start.
No scratch array, partition, counter, or active-queue entry changes. -/
theorem splitCounts_uniform (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! →
      s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) :
    splitCounts level first distance s = s.hash first := by
  unfold splitCounts
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => t = s.hash first)
  mvcgen +jp
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨cursor, state⟩ => ⌜state = first + 1 + cursor.prefix.length ∧
          state + cursor.suffix.length = s.cellend[first]! + 1⌝)
      | exact (⇓_ => ⌜False⌝)
  all_goals simp_all +zetaDelta [RefineSt.hash, Std.Legacy.Range.toList]
  all_goals try omega
  all_goals try grind

end Hex.GraphIso.Nauty.Sparse
