/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefPath
public import HexGraphIso.Nauty.Sparse.GenerationFrame
public import HexGraphIso.Orbit
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Orbit
import all HexGraphIso.Generated

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- Every image under the true path stabilizer contains the transported
native reference with the same all-same boundary. This justifies reference
occurrence before the emitted subgroup is known to be complete. -/
theorem RefPath.orbit {G : GraphIso.Sparse.Colored n k} {base : List (Fin n)}
    {tcLevel boundary level tc len a b : Nat} {rs : RefineSt n} {st : State n}
    {scratch other : Scratch} {u v : Fin n} {targets : List Nat} {key : Key n}
    (hr : RefineSt.Ready G.graph level rs) (hpath : PathInv G level st)
    (hlab : st.lab = rs.lab) (hptn : st.ptn = rs.ptn)
    (hbase : ∀ x : Fin n, st.fixedpts.mem x.val = true → x ∈ base)
    (hc : IsCell rs.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ha : a < len) (hb' : b < len)
    (hs : Scratch.Bounded n scratch) (ht : Scratch.Bounded n other)
    (hatU : rs.lab[tc + a]! = u.val) (hatV : rs.lab[tc + b]! = v.val)
    (horbit : Aut.Orbit G.toDense base u v)
    (h : RefPath G.graph tcLevel boundary (level + 1)
      (rs.child (.ofGraph G.graph) level tc rs.lab[tc + a]! scratch) targets key) :
    RefPath G.graph tcLevel boundary (level + 1)
      (rs.child (.ofGraph G.graph) level tc rs.lab[tc + b]! other) targets key := by
  obtain ⟨p, hp, hfix, hmove⟩ := horbit
  have hp : GraphIso.Sparse.IsIso G G p := (GraphIso.Sparse.isIso_toDense G G p).mp hp
  have hn0 : 0 < n := by have := u.isLt; omega
  have hstab := path_stab hpath hn0 hp (fun x hx => hfix x (hbase x hx))
  rw [hlab, hptn] at hstab
  have hautom : Automorphism G (renamingArray (renamingOf p)) :=
    ⟨by simp [renamingArray], p, hp, fun x => by
      rw [renamingArray_get _ x.isLt, renamingOf_lt p x.isLt]⟩
  apply h.carried hr hc hb hn ha hb' hs ht hautom.checked hstab
  rw [hatU, hatV, renamingArray_get _ u.isLt, renamingOf_lt p u.isLt, hmove]

end Hex.GraphIso.Nauty.Sparse.Generation
