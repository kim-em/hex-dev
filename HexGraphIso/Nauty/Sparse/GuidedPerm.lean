/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GuidedLeaf
public import HexGraphIso.Nauty.Sparse.ReadyPerm
import all HexGraphIso.Nauty.Sparse.FollowsPerm

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native guided history with all its refinement codes, allowing the
current endpoint's labels to be reordered within the same cells. -/
def GuidedPerm (G : Hex.SparseGraph n) (tcLevel : Nat) (store : Array Int) (base : Nat)
    (root : RefineSt n) (level : Nat) (current : RefineSt n) : Prop :=
  ∃ leaf path codes, ∃ trace : CodePath G base root path level leaf codes,
    trace.Guided tcLevel store ∧ current.ptn = leaf.ptn ∧ cellsPerm leaf.ptn level current.lab leaf.lab

namespace GuidedPerm

variable {G : Hex.SparseGraph n} {tcLevel : Nat} {store : Array Int} {base level : Nat}
  {root current : RefineSt n}

theorem refl (G : Hex.SparseGraph n) (tcLevel : Nat) (store : Array Int) (level : Nat) (st : RefineSt n) :
    GuidedPerm G tcLevel store level st level st :=
  ⟨st, [], [st.longcode], .refl _ _, trivial, rfl, cellsPerm_refl _ _ _⟩

/-- Recovered label order retains the same complete guided path. -/
theorem setLab (h : GuidedPerm G tcLevel store base root level current) (lab : Array Nat)
    (he : cellsPerm current.ptn level lab current.lab) :
    GuidedPerm G tcLevel store base root level { current with lab } := by
  obtain ⟨leaf, path, codes, trace, hg, hp, hc⟩ := h
  exact ⟨leaf, path, codes, trace, hg, hp, cellsPerm_trans (hp ▸ he) hc⟩

/-- At a discrete endpoint, the guided history has the literal current
label array, so its scatter and native key can be used directly. -/
theorem leaf (h : GuidedPerm G tcLevel store base root level current)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    (hd : discreteAt current.ptn level n = true) :
    ∃ leaf path codes, ∃ trace : CodePath G base root path level leaf codes,
      trace.Guided tcLevel store ∧ leaf.lab = current.lab ∧ leaf.ptn = current.ptn := by
  obtain ⟨leaf, path, codes, trace, hg, hp, he⟩ := h
  have hl := trace.descent.ready hr
  have hdisc : discreteAt leaf.ptn level n = true := by rw [← hp]; exact hd
  have hpoint := discrete_pointwise he (Nat.le_of_eq hl.spec.node.ptnSize.symm)
    hl.spec.node.ptnEnd hdisc
  have harray : current.lab = leaf.lab := by
    apply Array.ext (hc.spec.node.labSize.trans hl.spec.node.labSize.symm)
    intro i hi hj
    have hv := hpoint i (by rw [hc.spec.node.labSize] at hi; exact hi)
    simpa only [getElem!_pos current.lab i hi, getElem!_pos leaf.lab i hj] using hv
  exact ⟨leaf, path, codes, trace, hg, harray.symm, hp.symm⟩

/-- A canonical or saved target extends the history through actual
individualization and cached refinement, including after sibling recovery. -/
theorem child (h : GuidedPerm G tcLevel store base root level current)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    {tc len o : Nat} (hcell : IsCell current.ptn level tc len) (hb : tc + len ≤ n)
    (hn : 1 < len) (ho : o < len)
    (hchoice : tc = targetcell (.ofGraph G) current.lab current.ptn level tcLevel (-1) ∨
      store[level]! = Int.ofNat tc) (scratch : Scratch) (hs : Scratch.Bounded n scratch) :
    GuidedPerm G tcLevel store base root (level + 1)
      (current.child (.ofGraph G) level tc current.lab[tc + o]! scratch) := by
  obtain ⟨leaf, path, codes, trace, hg, hp, he⟩ := h
  have hl := trace.descent.ready hr
  have hcount : leaf.numcells = current.numcells := by rw [hl.spec.count, hc.spec.count, hp]
  have hperm : cellsPerm current.ptn level leaf.lab (current.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [FollowsPerm.map_id, hp]
    exact cellsPerm_symm he
  have hchoice' : tc = targetcell (.ofGraph G) leaf.lab leaf.ptn level tcLevel (-1) ∨
      store[level]! = Int.ofNat tc := by
    rcases hchoice with hchoice | hchoice
    · exact Or.inl (hchoice.trans (hc.target_perm hl hp he tcLevel (-1)))
    · exact Or.inr hchoice
  let fresh := Scratch.fresh n
  have hf : Scratch.Bounded n fresh := (Scratch.fresh_valid n leaf.lab leaf.ptn (level + 1)).toBounded
  obtain ⟨j, hj, _, hchild⟩ := child_match G G (Perm.id n) (by simp) hc hl hp.symm hcount hperm
    hcell hb hn ho scratch fresh hs hf
  have hcell' : IsCell leaf.ptn level tc len := by rw [← hp]; exact hcell
  obtain ⟨next, hnext⟩ := hg.extend hcell' hb hn hj fresh hf hchoice'
  refine ⟨_, _, _, next, hnext, hchild.ptn.symm, ?_⟩
  rw [hchild.ptn]
  have hh := hchild.cells
  rw [FollowsPerm.map_id] at hh
  exact cellsPerm_symm hh

end GuidedPerm

/-- A recovered guided history and a checked native automorphism supply
the saved first sentinel and graph without a cheap-shape assumption. -/
theorem FirstRef.guided_follows {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n} {f l : Label n}
    (h : FirstRef G tcLevel base root st) (hr : RefineSt.Ready G base root)
    (hc : RefineSt.Ready G level current) (hg : GuidedPerm G tcLevel st.firsttc base root level current)
    (hd : discreteAt current.ptn level n = true)
    (hf : Label.ofArray? n st.firstlab = some f) (hl : Label.ofArray? n current.lab = some l)
    (p : Perm n) (hiso : ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j)
    (hlabels : st.firstlab.map (renamingOf p).toFun = current.lab) :
    level = h.last ∧ st.firstcode[level + 1]! = codeSentinel ∧ G.relabel l.perm = G.relabel f.perm := by
  obtain ⟨leaf, path, codes, trace, hguided, hlabel, hptn⟩ := hg.leaf hr hc hd
  obtain ⟨hlevel, _, hsent, hgraph⟩ := h.leaf_guided hr trace hguided
    (by rw [hptn]; exact hd) hf (by rw [hlabel]; exact hl) p hiso (by rw [hlabel]; exact hlabels)
  exact ⟨hlevel, hsent, hgraph⟩

end Hex.GraphIso.Nauty.Sparse
