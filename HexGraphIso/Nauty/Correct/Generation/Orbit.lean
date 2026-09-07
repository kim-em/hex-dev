/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Frame
public import HexGraphIso.Nauty.Correct.Generation.Coverage
import all HexGraphIso.Generated
import all HexGraphIso.Nauty.Correct.Generation.Carry

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {base : List (Fin n)}

/-- Every image of a reference child under the true path stabilizer
contains the same reference occurrence. This supplies the matching-search
premise before any generation theorem has been established. -/
theorem HasLeaf.orbit {rs : RefineSt n} {st : SearchSt n}
    {tcLevel level tc e oU oV : Nat} {u v : Fin n} {targets : List Nat} {key : Key n}
    (hok : IterOk { g := rowsOf G } level rs) (hlvl : level < n)
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    (hlab : st.lab = rs.lab) (hptn : st.ptn = rs.ptn)
    (hbase : ∀ b : Fin n, st.fixedpts.mem b.val = true → b ∈ base)
    (hcell : (tc, e) ∈ cells rs.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hatU : rs.lab[tc + oU]! = u.val) (hatV : rs.lab[tc + oV]! = v.val)
    (horbit : Aut.Orbit G base u v)
    (h : HasLeaf { g := rowsOf G } tcLevel (level + 1)
      (childSt { g := rowsOf G } level rs tc rs.lab[tc + oU]!) targets key) :
    HasLeaf { g := rowsOf G } tcLevel (level + 1)
      (childSt { g := rowsOf G } level rs tc rs.lab[tc + oV]!) targets key := by
  obtain ⟨p, hp, hfix, hmap⟩ := horbit
  have hstab := path_stab (by omega : 0 < n) hpath hp (fun b hb => hfix b (hbase b hb))
  rw [hlab, hptn] at hstab
  apply h.carried hok hlvl (size_rowsOf G)
    (checkAutom_renaming (ctx := { g := rowsOf G }) (renamingOf p) (rowsMap_of_isIso hp))
    hstab hcell hne hoU hoV
  rw [hatU, hatV, renamingArray_get _ u.isLt, renamingOf_lt p u.isLt, hmap]

end Hex.GraphIso.Nauty.Generation
