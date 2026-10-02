/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Guided
public import HexGraphIso.Nauty.Sparse.FirstRef
public import HexGraphIso.Nauty.SmallCell.Key
import all HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Equitable.Step

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A renaming relating two descendant labels stabilizes their common
ancestor's ordered cells. This uses the frame of the executed native calls. -/
theorem DescPath.map_cells {G : Hex.SparseGraph n} {base last₁ last₂ : Nat}
    {root first current : RefineSt n} {path₁ path₂ : List (Nat × Nat)}
    (hfirst : DescPath G base root path₁ last₁ first)
    (hcurrent : DescPath G base root path₂ last₂ current) (hr : RefineSt.Ready G base root)
    (p : Perm n) (hlabels : first.lab.map (renamingOf p).toFun = current.lab) :
    cellsPerm root.ptn base root.lab (root.lab.map (renamingOf p).toFun) := by
  have hf := hfirst.ready hr
  have hmap : ∀ i, i < n → (renamingArray (renamingOf p))[first.lab[i]!]! = current.lab[i]! := by
    intro i hi
    rw [renamingArray_get _ (perm_bound hf.spec.label hi),
      ← hlabels, getElem!_map_of_lt _ _ (by rw [hf.spec.node.labSize]; exact hi)]
  have hs := cellStab_of_scatter hr.spec.node.ptnSize hr.spec.node.labSize
    hf.spec.node.labSize hr.spec.node.ptnEnd (hfirst.frame hr).1 (hcurrent.frame hr).1 hmap
  have he : root.lab.map (fun v => (renamingArray (renamingOf p))[v]!) =
      root.lab.map (renamingOf p).toFun := by
    apply map_congr_of_labOk (fun i hi => perm_bound hr.spec.label (by rwa [hr.spec.node.labSize] at hi))
    intro v hv
    exact renamingArray_get _ hv
  change cellsPerm root.ptn base root.lab (root.lab.map fun v => (renamingArray (renamingOf p))[v]!) at hs
  rwa [he] at hs

/-- An automorphism relating actual descendant labels identifies their
depth and complete code sequence when one path is selected and the other
uses native or saved targets. No small-cell shape is required. -/
theorem CodePath.guided_leaf {G : Hex.SparseGraph n} {tcLevel base last₁ last₂ : Nat}
    {root first current : RefineSt n} {path₁ path₂ : List (Nat × Nat)}
    {codes₁ codes₂ : List Nat} {store : Array Int} {f l : Label n}
    (hfirst : CodePath G base root path₁ last₁ first codes₁)
    (hr : RefineSt.Ready G base root) (hselect : hfirst.Selects tcLevel)
    (htarget : Targets store base (path₁.map Prod.fst))
    (hcurrent : CodePath G base root path₂ last₂ current codes₂)
    (hguided : hcurrent.Guided tcLevel store)
    (hd₁ : discreteAt first.ptn last₁ n = true) (hd₂ : discreteAt current.ptn last₂ n = true)
    (hf : Label.ofArray? n first.lab = some f) (hl : Label.ofArray? n current.lab = some l)
    (p : Perm n) (hiso : ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j)
    (hlabels : first.lab.map (renamingOf p).toFun = current.lab) :
    last₂ = last₁ ∧ codes₂ = codes₁ ∧ G.relabel l.perm = G.relabel f.perm := by
  have hcells := hfirst.descent.map_cells hcurrent.descent hr p hlabels
  have hroot : RefineSt.Equiv (renamingOf p) base root root := ⟨rfl, hcells, rfl, rfl⟩
  obtain ⟨hdepth, hcodes⟩ := hfirst.guided_codes G G p hiso hr hr hroot hselect htarget
    hcurrent hguided hd₁ hd₂ hlabels
  refine ⟨hdepth, hcodes, ?_⟩
  have hp := SpecLeaf.parse_map p (hfirst.descent.ready hr).spec.label hf
  rw [hlabels, hl] at hp
  have he : l.perm = p.comp f.perm := congrArg Label.perm (Option.some.inj hp)
  apply Hex.SparseGraph.ext
  intro i j
  simp only [Hex.SparseGraph.adj_relabel, he, Perm.get_comp]
  exact hiso _ _

/-- The saved native first reference supplies the selected path, code
slots and terminal sentinel needed by the general automorphism argument. -/
theorem FirstRef.leaf_guided {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n} {path : List (Nat × Nat)}
    {codes : List Nat} {f l : Label n}
    (h : FirstRef G tcLevel base root st) (hr : RefineSt.Ready G base root)
    (hc : CodePath G base root path level current codes) (hg : hc.Guided tcLevel st.firsttc)
    (hd : discreteAt current.ptn level n = true)
    (hf : Label.ofArray? n st.firstlab = some f) (hl : Label.ofArray? n current.lab = some l)
    (p : Perm n) (hiso : ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j)
    (hlabels : st.firstlab.map (renamingOf p).toFun = current.lab) :
    level = h.last ∧ codes = h.codes ∧ st.firstcode[level + 1]! = codeSentinel ∧
      G.relabel l.perm = G.relabel f.perm := by
  obtain ⟨hlevel, hcodes, hgraph⟩ := h.trace.guided_leaf hr h.selects h.targets hc hg h.discrete hd
    (by rw [h.lab]; exact hf) hl p hiso (by rw [h.lab]; exact hlabels)
  exact ⟨hlevel, hcodes, hlevel ▸ h.sentinel, hgraph⟩

end Hex.GraphIso.Nauty.Sparse
