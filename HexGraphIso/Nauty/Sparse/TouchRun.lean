/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Touched
public import HexGraphIso.Nauty.Sparse.Window
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- The singleton splitter's neighbour scan marks exactly the observed
vertices and enumerates each touched nonsingleton cell once. -/
theorem touch_scan (neighbor : Nat → Nat) (keys marks vmarks : Array Nat)
    (n stamp lo hi : Nat) (hm : Scratch.Marks n stamp marks) (hs : vmarks.size = n)
    (hv : ∀ e, lo ≤ e → e < hi → neighbor e < n)
    (hk : ∀ e, lo ≤ e → e < hi → keys[neighbor e]! ≤ n) :
    let r : Array Nat × Array Nat × Array Nat := Id.run do
      let mut marks := marks
      let mut touched := #[]
      let mut hitVertices := vmarks
      for e in [lo:hi] do
        let j := neighbor e
        hitVertices := hitVertices.set! j (stamp + 1)
        let k := keys[j]!
        if k != n && marks[k]! != stamp + 1 then
          marks := marks.set! k (stamp + 1)
          touched := touched.push k
      return (marks, touched, hitVertices)
    Touched n stamp marks r.1 r.2.1
        ((List.range' lo (hi - lo)).map fun e => keys[neighbor e]!) ∧
      Index.Writes n vmarks r.2.2 ((List.range' lo (hi - lo)).map neighbor) (stamp + 1) := by
  have step_bounds (pref suff : List Nat) (cur : Nat)
      (hr : [lo:hi].toList = pref ++ cur :: suff) : lo ≤ cur ∧ cur < hi := by
    have hh := List.mem_of_range'_eq_append_cons (show
      List.range' lo (hi - lo) = pref ++ cur :: suff from by
        simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using hr)
    obtain ⟨i, hi', hc⟩ := List.mem_range'.mp hh
    simp only [Nat.one_mul] at hc
    omega
  simp only
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Array Nat × Array Nat =>
    Touched n stamp marks r.1 r.2.1
        ((List.range' lo (hi - lo)).map fun e => keys[neighbor e]!) ∧
      Index.Writes n vmarks r.2.2 ((List.range' lo (hi - lo)).map neighbor) (stamp + 1))
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      Touched n stamp marks state.1 state.2.1 (cursor.prefix.map fun e => keys[neighbor e]!) ∧
      Index.Writes n vmarks state.2.2 (cursor.prefix.map neighbor) (stamp + 1)⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  case vc3.pre => exact ⟨Touched.empty hm, Index.Writes.initial hs⟩
  case vc1.step.isTrue =>
    rename_i pref cur suff hr b hf hin
    have hb := step_bounds pref suff cur (by simpa [Std.Legacy.Range.toList] using hr)
    have hkey := hk cur hb.1 hb.2
    exact ⟨hin.1.fresh (by omega) hf.2, hin.2.step (hv cur hb.1 hb.2)⟩
  case vc2.step.isFalse =>
    rename_i pref cur suff hr b hf hin
    have hb := step_bounds pref suff cur (by simpa [Std.Legacy.Range.toList] using hr)
    have hkey := hk cur hb.1 hb.2
    refine ⟨?_, hin.2.step (hv cur hb.1 hb.2)⟩
    by_cases he : keys[neighbor cur]! = n
    · simpa only [he] using hin.1.sentinel
    · exact hin.1.repeated (by omega) (hf he)

end Hex.GraphIso.Nauty.Sparse
