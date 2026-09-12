/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Fill
public import HexGraphIso.Nauty.Sparse.IndexWrites
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Reverse indexing in the executed reinsertion loop reads the corresponding
entry of the reversed hit list. -/
theorem reverse_read (hit : Array Nat) (i : Nat) (hi : i < hit.size) :
    hit[hit.size - 1 - i]! = hit.toList.reverse[i]! := by
  rw [getElem!_pos hit.toList.reverse i (by simpa using hi), List.getElem_reverse]
  simp only [Array.length_toList, Array.getElem_toList,
    getElem!_pos hit (hit.size - 1 - i) (by omega)]

/-- The actual reverse hit loop copies every hit and writes its new cell
start. Its bounds permit empty hit lists and repeated input vertices. -/
theorem restore_scan (before hit starts : Array Nat) (first n : Nat)
    (hb : first + hit.size ≤ before.size) (hs : starts.size = n)
    (hv : ∀ v ∈ hit.toList, v < n) :
    let r : Array Nat × Array Nat × Nat := Id.run do
      let mut lab := before
      let mut starts := starts
      let mut v3 := first
      for t in [0:hit.size] do
        let j := hit[hit.size - 1 - t]!
        starts := starts.set! j first
        lab := lab.set! v3 j
        v3 := v3 + 1
      return (lab, starts, v3)
    Fill before hit.toList.reverse first hit.toList.reverse.length r.1 ∧
      Index.Writes n starts r.2.1 hit.toList.reverse first ∧ r.2.2 = first + hit.size := by
  simp only
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Array Nat × Nat =>
    Fill before hit.toList.reverse first hit.toList.reverse.length r.1 ∧
      Index.Writes n starts r.2.1 hit.toList.reverse first ∧ r.2.2 = first + hit.size)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      Fill before hit.toList.reverse first cursor.prefix.length state.1 ∧
      Index.Writes n starts state.2.1 (hit.toList.reverse.take cursor.prefix.length) first ∧
      state.2.2 = first + cursor.prefix.length⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  case vc2.pre =>
    exact ⟨Fill.initial before hit.toList.reverse first (by simpa using hb), Index.Writes.initial hs⟩
  case vc3.post.success =>
    rename_i hin
    simpa only [show hit.size = hit.toList.reverse.length by simp, List.take_length] using hin.2.1
  case vc1.step =>
    rename_i pref cur suff hr b hin
    have hcur : cur = pref.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' 0 hit.size = pref ++ cur :: suff from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel, Nat.sub_zero] using hr)
      simpa only [Nat.one_mul, Nat.zero_add] using hh
    have hbound := range_cursor (Nat.zero_le hit.size) hr
    have hi : pref.length < hit.toList.reverse.length := by
      simp only [List.length_reverse, Array.length_toList]
      omega
    have hm : hit.toList.reverse[pref.length]! ∈ hit.toList.reverse := by
      rw [getElem!_pos hit.toList.reverse pref.length hi]
      exact List.getElem_mem _
    have hv' := hv _ (by simpa only [List.mem_reverse, Array.mem_toList_iff] using hm)
    rw [reverse_read hit cur (by omega), hcur]
    refine ⟨hin.1.step hi, ?_, by omega⟩
    have hh := hin.2.1.step hv'
    simpa only [List.take_succ_eq_append_getElem hi,
      getElem!_pos hit.toList.reverse pref.length hi] using hh

end Hex.GraphIso.Nauty.Sparse
