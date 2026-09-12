/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryPass
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

open Std.Do
set_option mvcgen.warning false

/-- The touched-cell iterator composes the executed cell contract. A cell
already processed cannot invalidate the cache description of a later cell. -/
theorem pass_loop (step : Nat → RefineSt n → RefineSt n) (level stamp : Nat)
    (hstep : ∀ first s, s.lab.toList.Perm (List.range n) → s.ptn.size = n →
      Index.Valid n s.lab s.ptn level s.cellstart s.cellend →
      IsCell s.ptn level first (s.cellend[first]! + 1 - first) →
      first < s.cellend[first]! → s.cellend[first]! < n →
      Cell level first (s.cellend[first]! + 1) (fun v => s.vmarks[v]! == stamp) s (step first s))
    (cells : Array Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hn : cells.toList.Nodup)
    (hc : ∀ a ∈ cells.toList,
      IsCell s.ptn level a (s.cellend[a]! + 1 - a) ∧ a < s.cellend[a]! ∧ s.cellend[a]! < n) :
    Pass level stamp cells.toList s (Id.run do
      let mut s := s
      for first in cells do s := step first s
      return s) := by
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Pass level stamp cells.toList s t)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      Pass level stamp cursor.prefix s state ∧
      state.lab.toList.Perm (List.range n) ∧ state.ptn.size = n ∧
      Index.Valid n state.lab state.ptn level state.cellstart state.cellend ∧
      (∀ a ∈ cursor.suffix,
        IsCell state.ptn level a (s.cellend[a]! + 1 - a) ∧ a < s.cellend[a]! ∧ s.cellend[a]! < n)⌝)
  all_goals simp_all
  all_goals try exact ⟨.nil, hp, hs, hi, hc⟩
  all_goals try assumption
  case vc2.pre => exact .nil
  case vc1.step =>
    rename_i pref first rest hlist state result hin
    have hfirst := hc first (Or.inr (Or.inl rfl))
    have hcur := hin.2.2.2.2.1
    have hends := hin.2.2.2.1.ends_eq first (s.cellend[first]! + 1 - first)
      hcur (by omega) (by omega)
    have he : state.cellend[first]! = s.cellend[first]! := by omega
    have hcell : IsCell state.ptn level first (state.cellend[first]! + 1 - first) := by
      simpa only [he] using hcur
    have hbody := hstep first state hin.2.1 hin.2.2.1 hin.2.2.2.1 hcell (by omega) (by omega)
    have hvalid := hbody.valid hin.2.1 hin.2.2.1 hin.2.2.2.1 hcell (by omega)
    refine ⟨hin.1.append (.cons hcell (by omega) (by omega) hbody .nil),
      hvalid.1, hvalid.2.1, hvalid.2.2, ?_⟩
    intro a ha
    have hh := hin.2.2.2.2.2 a ha
    have hne : a ≠ first := by
      have hnot := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
      intro heq
      exact hnot (heq ▸ ha)
    exact hbody.preserve hcell hh hne

end Hex.GraphIso.Nauty.Sparse.Binary
