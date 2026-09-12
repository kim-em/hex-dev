/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceLeaf
import all HexGraphIso.Nauty.Policy.History

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native saved-target history whose endpoint may differ from the
current label order inside cells, as happens after sibling recovery. -/
def FollowsPerm (G : Hex.SparseGraph n) (store : Array Int) (base : Nat)
    (root : RefineSt n) (level : Nat) (current : RefineSt n) : Prop :=
  ∃ leaf path, DescPath G base root path level leaf ∧ Targets store base (path.map Prod.fst) ∧
    current.ptn = leaf.ptn ∧ cellsPerm leaf.ptn level current.lab leaf.lab

namespace FollowsPerm

variable {G : Hex.SparseGraph n} {store : Array Int} {base level : Nat} {root current : RefineSt n}

theorem refl (G : Hex.SparseGraph n) (store : Array Int) (level : Nat) (st : RefineSt n) :
    FollowsPerm G store level st level st :=
  ⟨st, [], .refl _ _, (by intro i hi; simp at hi), rfl, cellsPerm_refl _ _ _⟩

/-- Reordering a recovered parent's cells preserves its recorded descent. -/
theorem setLab (h : FollowsPerm G store base root level current) (lab : Array Nat)
    (hc : cellsPerm current.ptn level lab current.lab) :
    FollowsPerm G store base root level { current with lab } := by
  obtain ⟨leaf, path, hd, ht, hp, he⟩ := h
  exact ⟨leaf, path, hd, ht, hp, cellsPerm_trans (hp ▸ hc) he⟩

theorem set_after (h : FollowsPerm G store base root level current) {slot : Nat}
    (hs : level ≤ slot) (value : Int) :
    FollowsPerm G (store.set! slot value) base root level current := by
  obtain ⟨leaf, path, hd, ht, hp, he⟩ := h
  refine ⟨leaf, path, hd, ht.set_after ?_ value, hp, he⟩
  simp only [List.length_map]
  have := hd.length
  omega

/-- At a discrete endpoint the history label is the literal current label. -/
theorem leaf (h : FollowsPerm G store base root level current)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    (hd : discreteAt current.ptn level n = true) :
    ∃ leaf path, DescPath G base root path level leaf ∧ Targets store base (path.map Prod.fst) ∧
      leaf.lab = current.lab ∧ leaf.ptn = current.ptn := by
  obtain ⟨leaf, path, hp, ht, hptn, he⟩ := h
  have hl := hp.ready hr
  have hdisc : discreteAt leaf.ptn level n = true := by rw [← hptn]; exact hd
  have hpoint := discrete_pointwise he (Nat.le_of_eq hl.spec.node.ptnSize.symm)
    hl.spec.node.ptnEnd hdisc
  have harray : current.lab = leaf.lab := by
    apply Array.ext (hc.spec.node.labSize.trans hl.spec.node.labSize.symm)
    intro i hi hj
    have hv := hpoint i (by rw [hc.spec.node.labSize] at hi; exact hi)
    simpa only [getElem!_pos current.lab i hi, getElem!_pos leaf.lab i hj] using hv
  exact ⟨leaf, path, hp, ht, harray.symm, hptn.symm⟩

private theorem map_id (lab : Array Nat) : lab.map (renamingOf (Perm.id n)).toFun = lab := by
  have he : (renamingOf (Perm.id n)).toFun = id := by funext v; simp [renamingOf]
  rw [he, Array.map_id]

/-- Individualization and native cached refinement extend a stored-target
history even when the current parent has a different within-cell order. -/
theorem child (h : FollowsPerm G store base root level current)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    {tc len o : Nat} (hcell : IsCell current.ptn level tc len) (hb : tc + len ≤ n)
    (hn : 1 < len) (ho : o < len) (htc : store[level]! = Int.ofNat tc)
    (scratch : Scratch) (hs : Scratch.Bounded n scratch) :
    FollowsPerm G store base root (level + 1)
      (current.child (.ofGraph G) level tc current.lab[tc + o]! scratch) := by
  obtain ⟨leaf, path, hd, ht, hp, he⟩ := h
  have hl := hd.ready hr
  have hcount : leaf.numcells = current.numcells := by rw [hl.spec.count, hc.spec.count, hp]
  have hperm : cellsPerm current.ptn level leaf.lab (current.lab.map (renamingOf (Perm.id n)).toFun) := by
    rw [map_id, hp]
    exact cellsPerm_symm he
  let fresh := Scratch.fresh n
  have hf : Scratch.Bounded n fresh := (Scratch.fresh_valid n leaf.lab leaf.ptn (level + 1)).toBounded
  obtain ⟨j, hj, _, hchild⟩ := child_match G G (Perm.id n) (by simp) hc hl hp.symm hcount hperm
    hcell hb hn ho scratch fresh hs hf
  have hcell' : IsCell leaf.ptn level tc len := by rw [← hp]; exact hcell
  let next := leaf.child (.ofGraph G) level tc leaf.lab[tc + j]! fresh
  have hstep : DescPath G level leaf [(tc, j)] (level + 1) next :=
    .step tc len j fresh hcell' hb hn hj hf (.refl _ _)
  refine ⟨next, path ++ [(tc, j)], hd.append hstep, ?_, hchild.ptn.symm, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    apply ht.append
    simpa only [List.length_map, ← hd.length] using htc
  · rw [hchild.ptn]
    have hh := hchild.cells
    rw [map_id] at hh
    exact cellsPerm_symm hh

end FollowsPerm
end Hex.GraphIso.Nauty.Sparse
