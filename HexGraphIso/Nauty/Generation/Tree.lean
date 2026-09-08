/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Coverage
public import HexGraphIso.Nauty.Invariant.TargetCell

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- The refined search-tree invariant, including the depth bound needed
to rule out a non-discrete node when the vertex budget is exhausted. -/
structure TreeOk (ctx : Ctx n) (level : Nat) (st : RefineSt n) : Prop where
  it : IterOk ctx level st
  eqt : Equitable ctx level st.lab st.ptn
  acc : bcount st.ptn level n = st.numcells
  depth : level ≤ st.numcells

/-- Every target child is a valid refined tree with strictly more cells. -/
theorem TreeOk.child {level tc e o : Nat} {st : RefineSt n}
    (h : TreeOk ctx level st) (hlvl : level < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e) (ho : o ≤ e - tc) :
    TreeOk ctx (level + 1) (childSt ctx level st tc st.lab[tc + o]!) := by
  obtain ⟨hit, heqt, hcount, hgrow⟩ := refined_child h.it h.eqt h.acc hlvl hsymm hcell hne ho
  exact ⟨hit, heqt, hcount, Nat.le_trans (Nat.succ_le_succ h.depth) hgrow⟩

/-- Every valid refined tree has a leaf following the specification's
target-cell rule. This prevents uniformity premises from being vacuous. -/
theorem TreeOk.nonempty {level tcLevel : Nat} {st : RefineSt n}
    (h : TreeOk ctx level st) (hlevel : 1 ≤ level)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    ∃ targets key, HasLeaf ctx tcLevel level st targets key := by
  suffices go : ∀ fuel level (st : RefineSt n), TreeOk ctx level st → 1 ≤ level →
      n < level + fuel → ∃ targets key, HasLeaf ctx tcLevel level st targets key by
    exact go (n + 1) level st h hlevel (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro level st h _ hfuel
    have := h.it.lvl
    omega
  | succ fuel ih =>
    intro level st h hlevel hfuel
    by_cases hnum : st.numcells = n
    · have hdisc : ∀ q, q < n → st.ptn[q]! ≤ level := by
        have hc : List.countP (fun q => decide (st.ptn[q]! ≤ level)) (List.range n) =
            (List.range n).length := by
          rw [List.length_range]
          exact h.acc.trans hnum
        intro q hq
        simpa using List.countP_eq_length.mp hc q (List.mem_range.mpr hq)
      exact ⟨[], _, HasLeaf.leaf hdisc⟩
    · have hbc : bcount st.ptn level n < n := by
        rw [h.acc]
        exact Nat.lt_of_le_of_ne (h.acc ▸ bcount_le _ _ _) hnum
      have hlt : level < n := by have := h.depth; have := h.acc; omega
      obtain ⟨tc, len, hmk, hcell, hlen, hrange⟩ :=
        maketargetcell_open (ctx := ctx) (tcLevel := tcLevel) (hint := -1)
          (lab := st.lab) hlevel h.it.ok.ptnSize h.it.ok.ptnEnd hbc
      have hspec := maketargetcell_eq_spec (tcLevel := tcLevel) h.eqt h.it.ok.labOk
        h.it.ok.labSize h.it.ok.ptnSize h.it.ok.ptnEnd
      have htarget : tc = specTargetcell ctx st.lab st.ptn level tcLevel :=
        (congrArg Prod.fst (hspec.symm.trans hmk)).symm
      have hecell : (tc, tc + len - 1) ∈ cells st.ptn level n :=
        isCell_mem_cells hcell (by rw [h.it.ok.ptnSize]; exact Nat.le_refl _) h.it.ok.ptnEnd (by omega)
      have hchild := h.child hlt hsymm hecell (by omega) (Nat.zero_le _)
      obtain ⟨targets, key, hleaf⟩ := ih (level + 1) _ hchild (by omega) (by omega)
      exact ⟨tc :: targets, _, HasLeaf.step hlt hecell (by omega) (Nat.zero_le _) htarget hleaf⟩

end Hex.GraphIso.Nauty.Generation
