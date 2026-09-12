/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SubtreeKey
public import HexGraphIso.Nauty.Sparse.SpecTransport
import all HexGraphIso.Nauty.Spec.SpecIso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Reverse ordered-cell equivalence through inverse vertex renamings.
Only inverse values on the actual vertex range are used. -/
theorem cells_inverse {σ τ : Renaming n} {level : Nat} {lab out ptn : Array Nat}
    (hp : lab.size = n) (hq : out.size = n) (hs : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hok : LabOk lab n)
    (hc : cellsPerm ptn level out (lab.map σ.toFun))
    (hinv : ∀ v, v < n → τ (σ v) = v) :
    cellsPerm ptn level lab (out.map τ.toFun) := by
  have hmap : (lab.map σ.toFun).map τ.toFun = lab := by
    rw [Array.map_map]
    calc
      lab.map (τ.toFun ∘ σ.toFun) = lab.map id := map_congr_of_labOk hok hinv
      _ = lab := by simp
  apply cellsPerm_of_forall_cells hs hp (by rw [Array.size_map, hq]) hend
  intro cell hcell
  have hb := cells_bound (Nat.le_of_eq hs.symm) hend cell hcell
  rw [hs] at hb
  have hle := cells_le cell hcell
  have hcp := cells_isCell (Nat.le_of_eq hs.symm) hend cell hcell
  have hm := (hc _ _ hcp).map τ.toFun
  rw [← segN_map (by rw [hq]; omega),
    ← segN_map (by rw [Array.size_map, hp]; omega), hmap] at hm
  exact hm.symm

/-- A native graph isomorphism and corresponding ordered cells identify
the complete subtree maxima, including their full refinement-code chains. -/
theorem subtreeKey_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (tcLevel fuel level : Nat) (lab out ptn : Array Nat) (active : VSet n) (numcells : Nat)
    (hg : SpecNode G level lab ptn active numcells)
    (hh : SpecNode H level out ptn active numcells)
    (hc : cellsPerm ptn level out (lab.map (renamingOf p).toFun))
    (hf : n < fuel + numcells) :
    subtreeKey G tcLevel fuel level lab ptn active numcells =
      subtreeKey H tcLevel fuel level out ptn active numcells := by
  have hback : ∀ u v, G.adj (p.inv.get u) (p.inv.get v) = H.adj u v := by
    intro u v
    simpa only [Perm.get_inv_get] using (hiso (p.inv.get u) (p.inv.get v)).symm
  have hcells : cellsPerm ptn level lab (out.map (renamingOf p.inv).toFun) := by
    apply cells_inverse hg.node.labSize hh.node.labSize hg.node.ptnSize hg.node.ptnEnd hg.node.labOk hc
    intro v hv
    rw [renamingOf_lt p hv, renamingOf_lt p.inv (p.get ⟨v, hv⟩).isLt]
    exact congrArg Fin.val (Perm.inv_get_get p ⟨v, hv⟩)
  apply Key.le_antisymm
  · apply SpecLeaf.maximum_le
      (specLeaves_nonempty G tcLevel fuel level lab ptn active numcells
        hg.label hg.node hg.count hg.depth hf)
    intro leaf hm
    exact ⟨leaf.map p, specLeaves_map G H p hiso tcLevel fuel level lab out ptn active numcells
      hg hh hc hm, SpecLeaf.map_key G H p hiso leaf⟩
  · apply SpecLeaf.maximum_le
      (specLeaves_nonempty H tcLevel fuel level out ptn active numcells
        hh.label hh.node hh.count hh.depth hf)
    intro leaf hm
    exact ⟨leaf.map p.inv, specLeaves_map H G p.inv hback tcLevel fuel level out lab ptn active numcells
      hh hg hcells hm, SpecLeaf.map_key H G p.inv hback leaf⟩

/-- Label permutations within ordered cells leave a native subtree maximum
unchanged even when the two sparse refinements enumerate leaves differently. -/
theorem subtreeKey_perm {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab out ptn : Array Nat} {active : VSet n}
    (hg : SpecNode G level lab ptn active numcells) (hh : SpecNode G level out ptn active numcells)
    (hc : cellsPerm ptn level out lab) (hf : n < fuel + numcells) :
    subtreeKey G tcLevel fuel level lab ptn active numcells =
      subtreeKey G tcLevel fuel level out ptn active numcells := by
  apply subtreeKey_map G G (Perm.id n) (by intros; simp only [Perm.get_id])
    tcLevel fuel level lab out ptn active numcells
    hg hh _ hf
  have he : (renamingOf (Perm.id n)).toFun = id := by funext v; simp [renamingOf]
  simpa only [he, Array.map_id] using hc

end Hex.GraphIso.Nauty.Sparse
