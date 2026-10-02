/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecChildMap
public import HexGraphIso.Nauty.Sparse.TargetCells

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every leaf of the executed unpruned sparse tree transports under an
isomorphism and arbitrary orders within corresponding input cells. The
induction includes every target member and preserves the entire code chain. -/
theorem specLeaves_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (tcLevel fuel level : Nat) (lab out ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (hg : SpecNode G level lab ptn active numcells)
    (hh : SpecNode H level out ptn active numcells)
    (hcell : cellsPerm ptn level out (lab.map (renamingOf p).toFun))
    {leaf : SpecLeaf n} (hm : leaf ∈ specLeaves G tcLevel fuel level lab ptn active numcells) :
    leaf.map p ∈ specLeaves H tcLevel fuel level out ptn active numcells := by
  induction fuel generalizing level lab out ptn active numcells leaf with
  | zero => cases hm
  | succ fuel ih =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    let s := refine (.ofGraph H) level out ptn active numcells
    have hr : SpecNode G level r.lab r.ptn r.active r.numcells := hg.refined.1
    have hs : SpecNode H level s.lab s.ptn s.active s.numcells := hh.refined.1
    have hreq : Equitable (Graph.context G) level r.lab r.ptn := hg.refined.2
    have hseq : Equitable (Graph.context H) level s.lab s.ptn := hh.refined.2
    have hend : ptn[n - 1]! ≤ level := by simpa only [hg.node.ptnSize] using hg.node.ptnEnd
    have he : RefineSt.Equiv (renamingOf p) level r s :=
      refineWith_equiv G H p hiso level lab out ptn active numcells (.fresh n) (.fresh n)
        hg.label hh.label hg.node.ptnSize hend hg.node.starts
        (Scratch.fresh_valid n lab ptn level).toBounded
        (Scratch.fresh_valid n out ptn level).toBounded hcell
    have hs' : SpecNode H level s.lab r.ptn r.active r.numcells := by
      simpa only [he.ptn, ← he.active, ← he.count] using hs
    rw [he.ptn] at hseq
    have hrend : r.ptn[n - 1]! ≤ level := by simpa only [hr.node.ptnSize] using hr.node.ptnEnd
    rw [specLeaves] at hm ⊢
    change leaf ∈ (if discreteAt r.ptn level n then _ else _) at hm
    change leaf.map p ∈ (if discreteAt s.ptn level n then _ else _)
    rw [he.ptn]
    by_cases hd : discreteAt r.ptn level n = true
    · simp only [hd, ite_true] at hm ⊢
      obtain ⟨label, hparse⟩ := Label.ofArray?_exists hr.label
      have heq := he.discrete hr.node.ptnSize hrend hr.node.labSize hs.node.labSize hd
      have hp := SpecLeaf.parse_map p hr.label hparse
      rw [heq, hp]
      rw [hparse] at hm
      have hl : leaf = ⟨[r.longcode, codeSentinel], label⟩ := List.mem_singleton.mp hm
      subst leaf
      simp only [SpecLeaf.map, he.code, List.mem_singleton]
      rfl
    · simp only [hd, Bool.false_eq_true, ite_false] at hm ⊢
      have hcount : bcount r.ptn level n < n := by
        have hb := bcount_le r.ptn level n
        have hn : bcount r.ptn level n ≠ n := fun h =>
          hd ((discreteAt_iff_bcount hr.node.ptnSize.symm hr.node.ptnEnd).mpr h)
        omega
      let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
      have htmap := maketargetcell_equiv G H p hiso r.lab s.lab r.ptn level tcLevel (-1)
        hr.label hs.label hr.node.ptnSize hrend hseq he.cells hcount
      obtain ⟨ht, hn, hb⟩ := maketargetcell_valid G r.lab r.ptn level tcLevel (-1)
        hr.label hr.node.ptnSize hrend hcount
      rw [htmap, ← he.count, ← he.code]
      obtain ⟨o, ho, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨last, hlast, rfl⟩ := List.mem_map.mp hm
      have ho : o < target.2.2 := List.mem_range.mp ho
      have hweak : ∀ q, q < n → r.ptn[q]! ≤ level ∨ level + 1 < r.ptn[q]! := by
        intro q _
        rcases hr.node.vals q with h | h
        · exact Or.inl h
        · exact Or.inr (by have := hr.depth; have := hr.count; have := bcount_le r.ptn level n; omega)
      obtain ⟨j, hj, _, hchild⟩ := breakout_match (renamingOf p) level target.1 target.2.2 o
        r.lab s.lab r.ptn hr.node.labSize hs.node.labSize hr.node.ptnSize hrend hweak ht hb hn ho he.cells
      apply List.mem_flatMap.mpr
      refine ⟨j, List.mem_range.mpr hj, ?_⟩
      apply List.mem_map.mpr
      refine ⟨last.map p, ?_, (SpecLeaf.map_prepend p r.longcode last).symm⟩
      exact ih _ _ _ _ _ _ (hr.child hreq ht hb hn ho) (hs'.child hseq ht hb hn hj) hchild hlast

end Hex.GraphIso.Nauty.Sparse
