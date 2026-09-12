/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexVertex
public import HexGraphIso.Nauty.Sparse.IndexWrites
public import HexGraphIso.Nauty.Sparse.CompactRun
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- A nontrivial cell's vertex list is exactly its cached inverse image. -/
theorem Index.Valid.cell_mem {lab ptn starts ends : Array Nat} {n level first last v : Nat}
    (hi : Index.Valid n lab ptn level starts ends)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hc : IsCell ptn level first (last - first))
    (hn : first + 1 < last) (hb : last ≤ n) (hv : v < n) :
    v ∈ (List.range' first (last - first)).map (fun q => lab[q]!) ↔ starts[v]! = first := by
  constructor
  · intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at hq
    rw [← he, hi.starts_eq first (last - first) hc (by omega) (by omega) q
      (by omega) (by omega), ite_eq_right (by omega)]
  · intro hk
    obtain ⟨q, hq, he⟩ := perm_position hp hv
    have hh := hi.nontrivial hs hend hq (by rw [he, hk]; omega)
    dsimp only at hh
    have he' := hi.ends_eq first (last - first) hc (by omega) (by omega)
    rw [he, hk, he'] at hh
    exact List.mem_map.mpr ⟨q, by simp only [List.mem_range'_1]; omega, he⟩

/-- The literal first-touch clearing loop changes precisely its cell's
vertices, without requiring any bound on the previous count values. -/
theorem clear_scan (lab before : Array Nat) (n first last : Nat)
    (hp : lab.toList.Perm (List.range n)) (hs : before.size = n)
    (hf : first ≤ last) (hb : last ≤ n) :
    let out : Array Nat := Id.run do
      let mut hits := before
      for q in [first:last] do
        hits := hits.set! lab[q]! 0
      return hits
    Index.Writes n before out ((List.range' first (last - first)).map fun q => lab[q]!) 0 := by
  simp only
  apply Id.of_wp_run_eq rfl (fun out : Array Nat =>
    Index.Writes n before out ((List.range' first (last - first)).map fun q => lab[q]!) 0)
  mvcgen
  case inv1 =>
    exact (⇓⟨cursor, state⟩ => ⌜Index.Writes n before state
      (cursor.prefix.map fun q => lab[q]!) 0⌝)
  all_goals simp_all +zetaDelta [Std.Legacy.Range.toList]
  case vc2.pre => exact Index.Writes.initial hs
  case vc1.step =>
    rename_i pref cur suff hr b hin
    have hh := range_cursor hf hr
    exact hin.step (perm_bound hp (by omega))

end Hex.GraphIso.Nauty.Sparse
