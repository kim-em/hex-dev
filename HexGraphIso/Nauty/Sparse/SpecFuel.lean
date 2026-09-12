/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecTree

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Standalone sparse refinement preserves valid node data and exact counts,
and never decreases the cell count. -/
theorem refine_node (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (hp : lab.toList.Perm (List.range n))
    (h : NodeOk n level lab ptn active) (hc : numcells = bcount ptn level n) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    r.lab.toList.Perm (List.range n) ∧ NodeOk n level r.lab r.ptn r.active ∧
    r.numcells = bcount r.ptn level n ∧ numcells ≤ r.numcells := by
  have hb := (Scratch.fresh_valid n lab ptn level).toBounded
  have hend : ptn[n - 1]! ≤ level := by simpa only [h.ptnSize] using h.ptnEnd
  have ht := refineWith_state G level lab ptn active numcells (.fresh n) hp h.ptnSize hend h.starts hb
  have hcount := refineWith_count G level lab ptn active numcells (.fresh n) hp h.ptnSize hend h.starts hb hc
  let s : State n := { (default : State n) with
    lab, ptn, active
    canong := { (default : Storage n) with scratch := .fresh n } }
  have ho := visit_nodeOk G level numcells s hp h hb
  have hmono := bcount_mono (fun q hq => (refineWith_boundary (.ofGraph G) level lab ptn
    active numcells (.fresh n)).closed hq) (nn := n)
  exact ⟨ht.1, ho, hcount, by dsimp only [refine]; omega⟩

/-- The unpruned specification cannot exhaust when its remaining recursion
bound exceeds the number of possible further cell splits. -/
theorem specLeaves_nonempty (G : Hex.SparseGraph n) (tcLevel fuel level : Nat)
    (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hc : numcells = bcount ptn level n) (hl : level ≤ numcells)
    (hf : n < fuel + numcells) :
    specLeaves G tcLevel fuel level lab ptn active numcells ≠ [] := by
  induction fuel generalizing level lab ptn active numcells with
  | zero =>
    have := bcount_le ptn level n
    omega
  | succ fuel ih =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    obtain ⟨hp', h', hc', hm⟩ := refine_node G level lab ptn active numcells hp h hc
    change r.lab.toList.Perm (List.range n) at hp'
    change NodeOk n level r.lab r.ptn r.active at h'
    change r.numcells = bcount r.ptn level n at hc'
    change numcells ≤ r.numcells at hm
    have hend : r.ptn[n - 1]! ≤ level := by simpa only [h'.ptnSize] using h'.ptnEnd
    have hbound := bcount_le r.ptn level n
    rw [specLeaves]
    split
    · obtain ⟨l, hl⟩ := Label.ofArray?_exists hp'
      rw [hl]
      simp
    · next hd =>
      have hcount : bcount r.ptn level n < n := by
        have he := discreteAt_iff_bcount h'.ptnSize.symm h'.ptnEnd
        change ¬ discreteAt r.ptn level n = true at hd
        have hn : bcount r.ptn level n ≠ n := fun hh => hd (he.mpr hh)
        omega
      let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
      obtain ⟨ht, hn, hr⟩ := maketargetcell_valid G r.lab r.ptn level tcLevel (-1) hp'
        h'.ptnSize hend hcount
      change IsCell r.ptn level target.1 target.2.2 at ht
      change 1 < target.2.2 at hn
      change target.1 + target.2.2 ≤ n at hr
      have ho : 0 < target.2.2 := by omega
      have hpchild := breakout_perm hp' h'.ptnSize hend ht hr ho
      have hchild := childNodeOk h'.labSize h'.labOk h'.ptnSize h'.ptnEnd h'.vals ht hr ho
      have hweak : ∀ q, q < n → r.ptn[q]! ≤ level ∨ level + 1 < r.ptn[q]! := by
        intro q _
        rcases h'.vals q with hh | hh
        · exact Or.inl hh
        · exact Or.inr (by omega)
      have hopen := ht.2.2.1 target.1 (Nat.le_refl _) (by omega)
      have hsplit := bcount_breakout_eq hweak hopen (by rw [h'.ptnSize]; omega) n (Nat.le_refl _)
      rw [ite_eq_left (by omega : target.1 < n)] at hsplit
      have hcchild : r.numcells + 1 = bcount (r.ptn.set! target.1 (level + 1)) (level + 1) n := by
        omega
      have hi := ih (level + 1) _ _ _ (r.numcells + 1) hpchild hchild hcchild (by omega) (by omega)
      obtain ⟨leaf, hleaf⟩ := List.exists_mem_of_ne_nil _ hi
      intro he
      have hm : leaf.prepend r.longcode ∈ (List.range target.2.2).flatMap (fun offset =>
          let child := breakout n r.lab r.ptn (level + 1) target.1 r.lab[target.1 + offset]!
          (specLeaves G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
            (r.numcells + 1)).map (SpecLeaf.prepend r.longcode)) :=
        List.mem_flatMap.mpr ⟨0, List.mem_range.mpr ho, List.mem_map.mpr ⟨leaf, hleaf, rfl⟩⟩
      rw [he] at hm
      cases hm

/-- Every native coloured graph has an attaining leaf in the finite sparse
tree, including the empty graph. -/
theorem rootLeaves_nonempty (G : GraphIso.Sparse.Colored n k) : rootLeaves G ≠ [] := by
  rw [rootLeaves]
  split
  · simp
  · next hn =>
    have hn : 0 < n := by omega
    have ho := initial_nodeOk G hn
    have hc := initial_count G
    apply specLeaves_nonempty G.graph 100 (n + 2) 1 _ _ _ _ (initialPartition_perm G) ho hc.symm
    · have hp := bcount_pos_of_boundary (ptn := initPtn n (n + 2)
        (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2) (level := 1)
        (nn := n) (q := n - 1) (by omega) (by simpa only [ho.ptnSize] using ho.ptnEnd)
      omega
    · omega

end Hex.GraphIso.Nauty.Sparse
