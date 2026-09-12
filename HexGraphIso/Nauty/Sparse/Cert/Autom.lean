/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Literal.Autom
public import HexGraphIso.Nauty.Sparse.Literal.Leaf
public import HexGraphIso.Nauty.Sparse.SubtreeMap
public import HexGraphIso.Nauty.Cert.Cert

public section

namespace Hex.GraphIso.Nauty.Sparse.Replay

/-- Check a raw automorphism and its transport of the current ordered cells
to another sibling. Parsing checks the entire permutation; graph checking
uses sparse generation marks. The cell test operates only on label segments. -/
@[expose] def checkAutom (G : Hex.SparseGraph n) (level : Nat)
    (lab out ptn raw : Array Nat) : Bool :=
  match Literal.label? n raw with
  | none => false
  | some l =>
    Literal.isautom (.ofGraph G) raw &&
      checkCellsPerm ptn out (Hex.Array.map' (renamingOf l.perm).toFun lab) level n

/-- Every accepted witness is an actual graph automorphism transporting
the complete ordered partition, not just the individualized vertex. -/
theorem checkAutom_sound {G : Hex.SparseGraph n} {level : Nat}
    {lab out ptn raw : Array Nat}
    (hp : lab.size = n) (hq : out.size = n) (hs : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (h : checkAutom G level lab out ptn raw = true) :
    ∃ p : Perm n, (∀ i j, G.adj (p.get i) (p.get j) = G.adj i j) ∧
      cellsPerm ptn level out (lab.map (renamingOf p).toFun) := by
  rw [checkAutom, Literal.label?_eq] at h
  split at h
  · cases h
  · rename_i l hl
    rw [Bool.and_eq_true, Literal.isautom_eq, Hex.Array.map'_eq_map] at h
    refine ⟨l.perm, ?_, ?_⟩
    · apply (isautom_iff G l.perm raw ?_).mp h.1
      intro i
      exact (Label.ofArray?_get hl i.val i.isLt).symm
    · exact checkCellsPerm_sound hs hq (by rw [Array.size_map, hp]) hend h.2

/-- A checked earlier sibling's bound and attainment transfer through a
genuine automorphism. Both directions use actual sparse leaf transport. -/
theorem Valid.map {G : Hex.SparseGraph n} {B : Key n} {a : Bool}
    {tcLevel fuel level numcells : Nat} {lab out ptn : Array Nat} {active : VSet n}
    (hg : SpecNode G level lab ptn active numcells)
    (hh : SpecNode G level out ptn active numcells)
    (p : Perm n) (hiso : ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j)
    (hc : cellsPerm ptn level out (lab.map (renamingOf p).toFun))
    (h : Valid G B (specLeaves G tcLevel fuel level lab ptn active numcells) a) :
    Valid G B (specLeaves G tcLevel fuel level out ptn active numcells) a := by
  have hback : ∀ i j, G.adj (p.inv.get i) (p.inv.get j) = G.adj i j := by
    intro i j
    simpa only [Perm.get_inv_get] using (hiso (p.inv.get i) (p.inv.get j)).symm
  have hcells : cellsPerm ptn level lab (out.map (renamingOf p.inv).toFun) := by
    apply cells_inverse hg.node.labSize hh.node.labSize hg.node.ptnSize hg.node.ptnEnd
      hg.node.labOk hc
    intro v hv
    rw [renamingOf_lt p hv, renamingOf_lt p.inv (p.get ⟨v, hv⟩).isLt]
    exact congrArg Fin.val (Perm.inv_get_get p ⟨v, hv⟩)
  constructor
  · intro leaf hm
    have hb := h.bound (leaf.map p.inv)
      (specLeaves_map G G p.inv hback tcLevel fuel level out lab ptn active numcells
        hh hg hcells hm)
    rwa [SpecLeaf.map_key G G p.inv hback] at hb
  · rw [h.attains]
    constructor
    · rintro ⟨leaf, hm, he⟩
      exact ⟨leaf.map p, specLeaves_map G G p hiso tcLevel fuel level lab out ptn active numcells
        hg hh hc hm, (SpecLeaf.map_key G G p hiso leaf).trans he⟩
    · rintro ⟨leaf, hm, he⟩
      exact ⟨leaf.map p.inv, specLeaves_map G G p.inv hback tcLevel fuel level out lab ptn active numcells
        hh hg hcells hm, (SpecLeaf.map_key G G p.inv hback leaf).trans he⟩

end Hex.GraphIso.Nauty.Sparse.Replay
