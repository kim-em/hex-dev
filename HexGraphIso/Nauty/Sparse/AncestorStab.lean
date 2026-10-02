/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.StateFrame
public import HexGraphIso.Nauty.Invariant.PathStab
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A descendant's actual effect also preserves each coarser ancestor
level, including both reference-store alternatives. The final boundary is
already closed at that ancestor, so every fine cell has a coarse owner. -/
theorem FrameOut.coarsen {G : GraphIso.Sparse.Colored n k}
    {base bound level : Nat} {st out : State n}
    (h : FrameOut G bound level st out) (hb : base ≤ bound) (hl : base ≤ level)
    (hsize : st.lab.size = n) (hptn : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ base) : FrameOut G base base st out := by
  have carry {lab : Array Nat} (hs : lab.size = st.lab.size)
      (hp : cellsPerm st.ptn level st.lab lab) : cellsPerm st.ptn base st.lab lab :=
    cellsPerm_coarsen rfl (hsize.trans hptn.symm) ((hs.trans hsize).trans hptn.symm)
      hp (Nat.le_trans hend hl) hend (fun _ hq => Nat.le_trans hq hl)
  refine ⟨⟨h.effect.labSize, h.effect.ptnSize, h.effect.reach, ?_,
    carry h.effect.labSize h.effect.perm, ?_, ?_, h.effect.canon⟩, h.scratch⟩
  · intro q hq
    exact h.effect.low q (by rcases hq with hq | hq <;> omega)
  · rcases h.effect.firstStore with he | ⟨hs, hp⟩
    · exact Or.inl he
    · exact Or.inr ⟨hs, carry hs hp⟩
  · rcases h.effect.canonStore with he | ⟨hs, hp⟩
    · exact Or.inl he
    · exact Or.inr ⟨hs, carry hs hp⟩

/-- Compose a complete descendant call with a suspended ancestor frame.
This transports its actual labels and saved references in one step. -/
theorem FrameOut.extend {G : GraphIso.Sparse.Colored n k}
    {base bound level numcells : Nat} {parent st out : State n}
    (h : FrameOut G base base parent st) (next : FrameOut G bound level st out)
    (hp : Ready G base numcells parent) (hn : 0 < n) (hpos : 1 ≤ base)
    (hb : base ≤ bound) (hl : base ≤ level) : FrameOut G base base parent out := by
  have hsize : st.lab.size = n := h.effect.labSize.trans hp.ok.labSize
  have hptn : st.ptn.size = n := h.effect.ptnSize.trans hp.ok.ptnSize
  have hps : st.ptn.size = parent.ptn.size := h.effect.ptnSize
  have hpEnd : parent.ptn[parent.ptn.size - 1]! ≤ base := searchOk_end hn hp.ok hpos
  have he : st.ptn[parent.ptn.size - 1]! = parent.ptn[parent.ptn.size - 1]! :=
    h.effect.low _ (Or.inl hpEnd)
  have hend : st.ptn[st.ptn.size - 1]! ≤ base := by rw [hps, he]; exact hpEnd
  exact h.trans (next.coarsen hb hl hsize hptn hend)

/-- A permutation stabilizing a suspended partition also stabilizes a
coarser suspended ancestor. Their actual effects into the same current
state supply both boundary inclusion and label transport. -/
theorem FrameOut.stab_below {G : GraphIso.Sparse.Colored n k}
    {a b acells bcells : Nat} {parent child out : State n} {gamma : Array Nat}
    (ha : FrameOut G a a parent out) (hb : FrameOut G b b child out)
    (hp : Ready G a acells parent) (hc : Ready G b bcells child)
    (hn : 0 < n) (hapos : 1 ≤ a) (hbpos : 1 ≤ b) (hab : a ≤ b)
    (hs : CellStab child.ptn b child.lab gamma) : CellStab parent.ptn a parent.lab gamma := by
  have hsize : out.lab.size = n := hb.effect.labSize.trans hc.ok.labSize
  have hpend : parent.ptn[parent.ptn.size - 1]! ≤ a := searchOk_end hn hp.ok hapos
  have hcend : child.ptn[child.ptn.size - 1]! ≤ b := searchOk_end hn hc.ok hbpos
  have hr : CellStab child.ptn b out.lab gamma :=
    LocalAutos.reindexStab hs hb.effect.perm hc.ok.ptnSize hc.ok.labSize hsize hcend
  have hcoarse : CellStab parent.ptn a out.lab gamma := by
    apply cellsPerm_coarsen (ptnF := child.ptn) (levF := b)
      (hp.ok.ptnSize.trans hc.ok.ptnSize.symm) (hsize.trans hc.ok.ptnSize.symm)
      (by rw [Array.size_map]; exact hsize.trans hc.ok.ptnSize.symm) hr hcend hpend
    intro q hq
    change parent.ptn[q]! ≤ a at hq
    change child.ptn[q]! ≤ b
    have hpa : out.ptn[q]! = parent.ptn[q]! := ha.effect.low q (Or.inl hq)
    have hcb : out.ptn[q]! = child.ptn[q]! := hb.effect.low q
      (Or.inr (by change out.ptn[q]! ≤ b; omega))
    omega
  exact LocalAutos.reindexStab hcoarse (cellsPerm_symm ha.effect.perm)
    hp.ok.ptnSize hsize hp.ok.labSize hpend

/-- A literal scatter between a retained reference and a descendant's
current label stabilizes their common suspended ancestor cells. -/
theorem FrameOut.scatter_stab {G : GraphIso.Sparse.Colored n k}
    {level numcells : Nat} {parent out : State n} {reference gamma : Array Nat}
    (h : FrameOut G level level parent out) (hp : Ready G level numcells parent)
    (hn : 0 < n) (hl : 1 ≤ level) (hs : reference.size = n)
    (href : cellsPerm parent.ptn level parent.lab reference)
    (hmap : ∀ i, i < n → gamma[reference[i]!]! = out.lab[i]!) :
    CellStab parent.ptn level parent.lab gamma :=
  cellStab_of_scatter hp.ok.ptnSize hp.ok.labSize hs (searchOk_end hn hp.ok hl)
    href h.effect.perm hmap

end Hex.GraphIso.Nauty.Sparse
