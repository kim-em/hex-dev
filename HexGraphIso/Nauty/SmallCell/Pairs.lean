/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Key
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A checked scatter between two reached labellings yields a valid
explicit autos-ledger entry at the initial coloured partition. -/
theorem pairOk_of_reach {G : Colored n k} {ctx : Ctx n}
    {lab₁ lab₂ γ : Array Nat}
    (hn0 : 0 < n)
    (hs₁ : lab₁.size = n) (hr₁ : CellsReach G lab₁)
    (hr₂ : CellsReach G lab₂)
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!)
    (hca : checkAutom ctx.g γ = true) :
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmperm γ n).1 (fmperm γ n).2 := by
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmperm hroot.labOk hroot.labSize hroot.ptnSize
    hroot.ptnEnd hca
  exact cellStab_of_scatter hroot.ptnSize hroot.labSize hs₁
    hroot.ptnEnd hr₁ hr₂ hsc

/-- The implicit pair recorded at a small-cell node is valid at the root
partition.  Its missing vertices are realized by the node's flip
automorphisms, while singleton cells supply the fixed set. -/
theorem SubtreeOk.pair_ok {ctx : Ctx n} {G : Colored n k}
    {level : Nat} {r : RefineSt n}
    (hn0 : 0 < n) (hlevel : 1 <= level)
    (hgsz : ctx.g.size = n)
    (hsymm : forall u v, u < n -> v < n ->
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : forall v, v < n -> (ctx.g[v]!).mem v = false)
    (hS : SubtreeOk ctx level r)
    (hreach : CellsReach G r.lab)
    (hinit : forall q : Nat,
      (initPtn n (n + 2) (initialPartition G).2)[q]! <= 1 ->
        r.ptn[q]! <= 1) :
    PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (fmptn r.lab r.ptn level n).1
      (fmptn r.lab r.ptn level n).2 := by
  have hroot := initial_nodeOk G hn0
  apply pairOk_fmptn
  · intro v hv
    obtain ⟨p, hp, hpv⟩ := labInj_surj
      (Nat.le_of_eq hS.it.ok.labSize.symm) hS.it.ok.labOk hS.it.inj v hv
    obtain ⟨c, hc, hp1, hp2⟩ := cells_cover p hp
    exact ⟨p, c.1, c.2, hc, hp1, hp2, hpv⟩
  · intro v c1 c2 hv hcell hp hq
    rcases hp with ⟨p, hp1, hp2, hpv⟩
    rcases hq with ⟨q, hq1, hq2, hqlt⟩
    have hoff : p - c1 ≠ q - c1 := by
      intro heq
      have : p = q := by omega
      subst q
      omega
    obtain ⟨sigma, hrows, hperm, hmap⟩ :=
      stabilizer_transitive hS hgsz hsymm hloop hcell
        (by omega) (by omega) (by omega) hoff
    let gamma := renamingArray sigma
    refine ⟨gamma, checkAutom_renaming sigma hrows, ?_, ?_, ?_⟩
    · intro u hu hfix
      obtain ⟨c, hcellc, hcu⟩ := fmptn_fix hfix
      have hcb := cells_bound (Nat.le_of_eq hS.it.ok.ptnSize.symm)
        hS.it.ok.ptnEnd (c, c) hcellc
      have hc : c < r.lab.size := by
        rw [hS.it.ok.labSize, ← hS.it.ok.ptnSize]
        exact hcb
      have hic := cells_isCell
        (by rw [hS.it.ok.ptnSize]; exact Nat.le_refl _)
        hS.it.ok.ptnEnd (c, c) hcellc
      have heq := cellsPerm_singleton hperm.cells
        (show IsCell r.ptn level c 1 by simpa using hic)
      change r.lab[c]! = (r.lab.map sigma.toFun)[c]! at heq
      rw [getElem!_map_of_lt _ _ hc] at heq
      rw [renamingArray_get sigma hu]
      rw [← hcu]
      exact heq.symm
    · have hrootperm : cellsPerm
          (initPtn n (n + 2) (initialPartition G).2) 1
          r.lab (mapSt sigma r).lab := by
        apply cellsPerm_coarsen
            (ptnC := initPtn n (n + 2) (initialPartition G).2)
            (ptnF := r.ptn) (levC := 1) (levF := level)
        · rw [size_initPtn, hS.it.ok.ptnSize]
        · rw [hS.it.ok.labSize, hS.it.ok.ptnSize]
        · simp [hS.it.ok.labSize, hS.it.ok.ptnSize]
        · exact hperm.cells
        · exact hS.it.ok.ptnEnd
        · exact hroot.ptnEnd
        · intro x hx
          exact Nat.le_trans (hinit x hx) hlevel
      apply cellStab_of_scatter hroot.ptnSize hroot.labSize
        hS.it.ok.labSize hroot.ptnEnd hreach
        (cellsPerm_trans hreach hrootperm)
      intro i hi
      have hil : i < r.lab.size := by rw [hS.it.ok.labSize]; exact hi
      have hv' := hS.it.ok.labOk i hil
      rw [renamingArray_get sigma hv']
      exact (getElem!_map_of_lt sigma.toFun r.lab hil).symm
    · have hσ := hmap
      simp only [Nat.add_sub_of_le hp1, Nat.add_sub_of_le hq1] at hσ
      rw [renamingArray_get sigma hv, ← hpv, ← hσ]
      rw [hpv]
      exact hqlt

end Hex.GraphIso.Nauty
