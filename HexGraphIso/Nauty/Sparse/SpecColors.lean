/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecMax
public import HexGraphIso.Nauty.Sparse.RefineFrame

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every enumerated leaf preserves the original ordered colour classes.
The induction follows every executed refinement and target rotation. -/
theorem specLeaves_cellsReach (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (tcLevel fuel level : Nat) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hc : numcells = bcount ptn level n) (hl : level ≤ numcells)
    (hr : CellsReach G.toDense lab)
    (hcoarse : ∀ q : Nat, (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2)[q]! ≤ 1 →
      ptn[q]! ≤ level) {leaf : SpecLeaf n}
    (hleaf : leaf ∈ specLeaves G.graph tcLevel fuel level lab ptn active numcells) :
    CellsReach G.toDense leaf.label.toArray := by
  induction fuel generalizing level lab ptn active numcells leaf with
  | zero => cases hleaf
  | succ fuel ih =>
    let r := refine (.ofGraph G.graph) level lab ptn active numcells
    obtain ⟨hp', h', hc', hm⟩ := refine_node G.graph level lab ptn active numcells hp h hc
    change r.lab.toList.Perm (List.range n) at hp'
    change NodeOk n level r.lab r.ptn r.active at h'
    change r.numcells = bcount r.ptn level n at hc'
    change numcells ≤ r.numcells at hm
    have hend : r.ptn[n - 1]! ≤ level := by simpa only [h'.ptnSize] using h'.ptnEnd
    have hrr : CellsReach G.toDense r.lab := refineWith_cellsReach G hn level lab ptn active numcells
      (.fresh n) hp h (Scratch.fresh_valid n lab ptn level).toBounded hr hcoarse
    have hcr : ∀ q : Nat, (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2)[q]! ≤ 1 →
        r.ptn[q]! ≤ level := fun q hq =>
      (refineWith_boundary (.ofGraph G.graph) level lab ptn active numcells (.fresh n)).closed (hcoarse q hq)
    rw [specLeaves] at hleaf
    dsimp only at hleaf
    split at hleaf
    · split at hleaf
      · cases hleaf
      · next l hparse =>
        have he : leaf = ⟨[r.longcode, codeSentinel], l⟩ := List.mem_singleton.mp hleaf
        subst leaf
        change CellsReach G.toDense l.toArray
        rw [Label.ofArray?_toArray hparse]
        exact hrr
    · next hd =>
      have hcount : bcount r.ptn level n < n := by
        have hb := bcount_le r.ptn level n
        change ¬ discreteAt r.ptn level n = true at hd
        have hh : bcount r.ptn level n ≠ n := fun he =>
          hd ((discreteAt_iff_bcount h'.ptnSize.symm h'.ptnEnd).mpr he)
        omega
      let target := maketargetcell (.ofGraph G.graph) r.lab r.ptn level tcLevel (-1)
      obtain ⟨ht, hn', hb⟩ := maketargetcell_valid G.graph r.lab r.ptn level tcLevel (-1)
        hp' h'.ptnSize hend hcount
      obtain ⟨o, ho, hleaf⟩ := List.mem_flatMap.mp hleaf
      obtain ⟨last, hlast, rfl⟩ := List.mem_map.mp hleaf
      have ho : o < target.2.2 := List.mem_range.mp ho
      obtain ⟨hpc, hchild, hcc, hlc⟩ := breakout_node hp' h' hc' (by omega) ht hb hn' ho
      have hrc := breakout_cellsReach hn hrr ht (by rw [h'.ptnSize]; exact hb)
        h'.labSize h'.ptnSize ho h'.ptnEnd hcr
      apply ih _ _ _ _ _ hpc hchild hcc hlc hrc _ hlast
      intro q hq
      change (r.ptn.set! target.1 (level + 1))[q]! ≤ level + 1
      rcases getElem!_set!_cases r.ptn target.1 (level + 1) q with he | he
      · rw [he]
        exact Nat.le_trans (hcr q hq) (by omega)
      · rw [he]
        exact Nat.le_refl _

/-- Every leaf of a nonempty coloured root has exactly the original contents
in each ordered initial colour cell. -/
theorem rootLeaves_cellsReach (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    {leaf : SpecLeaf n} (hm : leaf ∈ rootLeaves G) : CellsReach G.toDense leaf.label.toArray := by
  have ho := initial_nodeOk G hn
  have hc := initial_count G
  rw [rootLeaves, ite_eq_right (by omega)] at hm
  apply specLeaves_cellsReach G hn 100 (n + 2) 1 _ _ _ _ (initialPartition_perm G) ho hc.symm _ _ _ hm
  · have hh := bcount_pos_of_boundary (ptn := initPtn n (n + 2)
      (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2) (level := 1)
      (nn := n) (q := n - 1) (by omega) (by simpa only [ho.ptnSize] using ho.ptnEnd)
    omega
  · rw [initialPartition_eq]
    exact cellsReach_initial G.toDense
  · simp only [initialPartition_eq]
    exact fun _ hh => hh

/-- The declarative maximum's labelling retains the ordered initial colours. -/
theorem canonSpecLabel_cellsReach (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    CellsReach G.toDense (canonSpecLabel G).toArray :=
  rootLeaves_cellsReach G hn (specBest_mem G)

/-- The declarative sparse form has the canonical sorted colour sequence,
also at order zero. -/
theorem canonSpecLabel_colors (G : GraphIso.Sparse.Colored n k) (i : Fin n) :
    ((G.relabel (canonSpecLabel G)).coloring.cells[i]).val = (sortedColorSeq G.toDense)[i.val]! := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  obtain ⟨hb, he⟩ := achieved_position_colors (canonSpecLabel_cellsReach G hn) i.val i.isLt
  have ha : (canonSpecLabel G).toArray[i.val]! = ((canonSpecLabel G).get i).val := by
    rw [getElem!_pos (canonSpecLabel G).toArray i.val (by rw [Label.size_toArray]; exact i.isLt)]
    simp only [Label.toArray, Array.getElem_ofFn]
  have hv : (⟨(canonSpecLabel G).toArray[i.val]!, hb⟩ : Fin n) = (canonSpecLabel G).get i := Fin.ext ha
  change (G.toDense.coloring.cells.get ⟨(canonSpecLabel G).toArray[i.val]!, hb⟩).val = _ at he
  rw [hv] at he
  simpa [GraphIso.Sparse.Colored.relabel, GraphIso.Sparse.Colored.toDense, Hex.Vector.get_eq_getElem] using he

/-- The attaining graph has normalized, strictly increasing native rows. -/
theorem canonSpecKey_sorted (G : GraphIso.Sparse.Colored n k) (i : Fin n) :
    ((canonSpecKey G).graph.nbrs i).toList.Pairwise (· < ·) :=
  (canonSpecKey G).graph.sorted i

end Hex.GraphIso.Nauty.Sparse
