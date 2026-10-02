/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompactFinish
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- The singleton splitter's actual compaction loop retains unmarked vertices
in order and collects marked vertices in order, even when writes alias the
position currently being read. -/
theorem compact_scan (before : Array Nat) (p : Nat → Bool) (first last : Nat)
    (hf : first ≤ last) (hb : last ≤ before.size) :
    let t : Array Nat × Nat × Array Nat := Id.run do
      let mut lab := before
      let mut v2 := first
      let mut hit := #[]
      for j in [first:last] do
        let v := lab[j]!
        if p v then hit := hit.push v
        else
          lab := lab.set! v2 v
          v2 := v2 + 1
      return (lab, v2, hit)
    Compact before p first last ((List.range' first (last - first)).map fun q => before[q]!)
      t.1 t.2.2 t.2.1 := by
  simp only
  apply Id.of_wp_run_eq rfl (fun t : Array Nat × Nat × Array Nat =>
    Compact before p first last ((List.range' first (last - first)).map fun q => before[q]!)
      t.1 t.2.2 t.2.1)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜
      Compact before p first (first + cursor.prefix.length)
        (cursor.prefix.map fun q => before[q]!) state.1 state.2.2 state.2.1⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  case vc3.pre => exact Compact.initial before p first (by omega)
  case vc1.step.isTrue =>
    rename_i pref cur suff hr b hkey hin
    have hcur : cur = first + pref.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' first (last - first) = pref ++ cur :: suff from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using hr)
      simpa only [Nat.one_mul] using hh
    have hbound := range_cursor hf hr
    have hread := hin.exterior cur (by omega) (Or.inr (by omega))
    rw [hread] at hkey ⊢
    have hh := hin.collect (by omega) (by simpa only [hcur] using hkey)
    simpa only [Nat.add_assoc, hcur] using hh
  case vc2.step.isFalse =>
    rename_i pref cur suff hr b hkey hin
    have hcur : cur = first + pref.length := by
      have hh := List.eq_of_range'_eq_append_cons (show
        List.range' first (last - first) = pref ++ cur :: suff from by
          simpa only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] using hr)
      simpa only [Nat.one_mul] using hh
    have hbound := range_cursor hf hr
    have hread := hin.exterior cur (by omega) (Or.inr (by omega))
    rw [hread] at hkey ⊢
    have hh := hin.keep (by omega) (by simpa only [hcur] using hkey)
    simpa only [Nat.add_assoc, hcur] using hh

end Hex.GraphIso.Nauty.Sparse
