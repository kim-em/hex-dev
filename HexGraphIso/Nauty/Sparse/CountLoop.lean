/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountReady
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

open Std.Do
set_option mvcgen.warning false

/-- The executed count-split iterator admits the semantic trace. Its
pending original cells retain exact keys through earlier disjoint splits. -/
theorem count_pass (level : Nat) (distance : Bool) (key : Nat → Nat)
    (cells : Array Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hn : cells.toList.Nodup)
    (hc : ∀ a ∈ cells.toList, Ready level key a s.cellend[a]! s) :
    Pass level distance key cells.toList s (Id.run do
      let mut s := s
      for first in cells do s := splitCounts level first distance s
      return s) := by
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Pass level distance key cells.toList s t)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      Pass level distance key cursor.prefix s state ∧
      state.lab.toList.Perm (List.range n) ∧ state.ptn.size = n ∧
      Index.Valid n state.lab state.ptn level state.cellstart state.cellend ∧
      ∀ a ∈ cursor.suffix, Ready level key a s.cellend[a]! state⌝)
  all_goals simp_all
  case vc2.pre => exact .nil
  case vc1.step =>
    rename_i pref first rest hlist state result hin
    have hcur := hin.2.2.2.2.1
    have he := hcur.endpoint hin.2.2.2.1
    have hcell : IsCell state.ptn level first (state.cellend[first]! + 1 - first) := by
      simpa only [he] using hcur.cell
    have hf : first ≤ state.cellend[first]! := by rw [he]; exact hcur.le
    have hb : state.cellend[first]! < n := by rw [he]; exact hcur.bound
    have hk : ∀ q, first ≤ q → q ≤ state.cellend[first]! → state.hits[state.lab[q]!]! < n + 2 := by
      simpa only [he] using hcur.keys
    have hv : ∀ v ∈ segN state.lab first (state.cellend[first]! + 1 - first), state.hits[v]! = key v := by
      simpa only [he] using hcur.values
    have hvalid := split_valid level first distance state hin.2.1 hin.2.2.1 hin.2.2.2.1 hcell hf hb hk
    refine ⟨hin.1.append (.cons hcell hf hb hk hv .nil),
      hvalid.1, hvalid.2.1, hvalid.2.2, ?_⟩
    intro a ha
    have hne : a ≠ first := by
      have hnot := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
      intro heq
      exact hnot (heq ▸ ha)
    exact hcur.keep (hin.2.2.2.2.2 a ha) hne distance hin.2.1 hin.2.2.1 hin.2.2.2.1

end Hex.GraphIso.Nauty.Sparse.CountTrace
