/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Equitable
public import HexGraphIso.Nauty.Policy.Recovery
public import HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Reordering labels within cells preserves equitability. -/
theorem Equitable.reorder {ctx : Ctx n} {level : Nat} {lab out ptn : Array Nat}
    (h : Equitable ctx level lab ptn) (hp : cellsPerm ptn level lab out)
    (hsize : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level) :
    Equitable ctx level out ptn := by
  intro cd hcd de hde
  have hcdCell := cells_isCell (Nat.le_of_eq hsize.symm) hend cd hcd
  have hdeCell := cells_isCell (Nat.le_of_eq hsize.symm) hend de hde
  have hcdPerm := hp cd.1 (cd.2 + 1 - cd.1) hcdCell
  have hdePerm := hp de.1 (de.2 + 1 - de.1) hdeCell
  have hwork : worksetOf n lab de.1 de.2 = worksetOf n out de.1 de.2 := worksetOf_perm hdePerm
  rw [splitDone_iff_constOn, ← hwork]
  exact (splitDone_iff_constOn.mp (h cd hcd de hde)).perm hcdPerm.symm

/-- An actual target-cell child refines to an equitable partition. -/
theorem child_equitable {G : Colored n k} {ctx : Ctx n} {level numcells tc tv : Nat}
    {st : Search n} {cell : VSet n} (first : Bool) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (heq : Equitable ctx level st.lab st.ptn)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    let R := (child first level tc tv st).refined ctx (level + 1) (numcells + 1)
    Equitable ctx (level + 1) R.lab R.ptn := by
  obtain ⟨len, hcell, hmem⟩ := htarget
  obtain ⟨hc, hlen, hrange⟩ := hcell (mem_ne_empty htv)
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hmem tv htv)
  change st.lab[tc + o]! = tv at hv
  have hend : st.ptn[st.ptn.size - 1]! ≤ level := searchOk_end hn0 hok hlevel
  have hlvl : level ≤ n := Nat.le_trans hok.bc (bcount_le _ _ _)
  have hc' : (tc, tc + len - 1) ∈ cells st.ptn level n :=
    isCell_mem_cells hc (by change n ≤ st.ptn.size; rw [hok.ptnSize]; exact Nat.le_refl _) hend (by omega)
  have hp := equitable_breakout hok.labSize hok.ptnSize hend
    (fun q hq => (hok.vals q hq).imp id (fun he => by rw [he]; omega))
    (labOk_of_reach hok.labSize hok.reach) (labInj_of_reach hok.labSize hn0 hok.reach)
    hsymm heq hc' (by omega) (by omega : o ≤ tc + len - 1 - tc) hok.count.symm

  rw [hv] at hp
  cases first <;> exact hp

/-- Recovering a parent retains its equitability despite the child's labelling order. -/
theorem recover_equitable {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st out : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (heq : Equitable ctx level st.lab st.ptn)
    (hout : SearchOut G level level st out) :
    let result := Nauty.recover (n + 2) level out
    Equitable ctx level result.lab result.ptn := by
  dsimp only
  rw [recover_ptn_eq hok hout]
  rw [Nauty.recover_lab]
  exact heq.reorder hout.perm hok.ptnSize (searchOk_end hn0 hok hlevel)

end Hex.GraphIso.Nauty
