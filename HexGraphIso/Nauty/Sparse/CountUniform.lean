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

/-- A constant-count cell exhausts the initial equal-count scan. -/
theorem CountSort.firstRun_uniform (lab hits : Array Nat) (first last : Nat)
    (hf : first < last)
    (hk : ∀ q, first ≤ q → q < last → hits[lab[q]!]! = hits[lab[first]!]!) :
    CountSort.firstRun lab hits first last = last := by
  unfold CountSort.firstRun
  apply Id.of_wp_run_eq rfl (fun v : Nat => v = last)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜state = first + 1 + cursor.prefix.length ∧
      state + cursor.suffix.length = last⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  all_goals try omega
  all_goals grind

/-- A uniform count cell returns immediately after hashing its start.
No scratch array, partition, counter, or active-queue entry changes. -/
theorem splitCounts_uniform (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! →
      s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) :
    splitCounts level first distance s = s.hash first := by
  simp [splitCounts, Id.run, bind, pure, CountSort.firstRun_uniform s.lab s.hits first
    (s.cellend[first]! + 1) (by omega) (fun q hq he => hk q hq (by omega))]

end Hex.GraphIso.Nauty.Sparse
