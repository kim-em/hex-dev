/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountParts
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.CountSort

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

/-- Finalizing count fragments only changes labels at the one indirect
sort call. The index, queue and hash updates retain that exact array. -/
theorem finish_lab (level first last : Nat) (distance : Bool)
    (s : RefineSt n) (w1 v2 w2 v3 : Nat) :
    (finish level first last distance s w1 v2 w2 v3).lab =
      if last = v2 then s.lab else if last = v3 then s.lab
      else Sort.indirect s.lab s.hits v3 (last - v3) := by
  unfold finish
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => t.lab =
    if last = v2 then s.lab else if last = v3 then s.lab
    else Sort.indirect s.lab s.hits v3 (last - v3))
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜state.1.lab = Sort.indirect s.lab s.hits v3 (last - v3)⌝)
      | exact (⇓_ => ⌜True⌝)
  all_goals simp_all +zetaDelta [RefineSt.hash, RefineSt.push]

end Hex.GraphIso.Nauty.Sparse.CountSort
