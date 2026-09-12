/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecNode
public import HexGraphIso.Nauty.Spec.CanonSpec

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Discrete ordered-cell equivalence determines the whole output label
array, including when earlier nontrivial cells used different tie orders. -/
theorem RefineSt.Equiv.discrete {s t : RefineSt n} (h : RefineSt.Equiv σ level s t)
    (hs : s.ptn.size = n) (hend : s.ptn[n - 1]! ≤ level)
    (hp : s.lab.size = n) (hq : t.lab.size = n) (hd : discreteAt s.ptn level n = true) :
    t.lab = s.lab.map σ.toFun := by
  have he := discrete_pointwise h.cells (Nat.le_of_eq hs.symm) (by simpa only [hs] using hend) hd
  apply Array.ext (by simp only [Array.size_map, hp, hq])
  intro i hi hj
  have hh := he i (by omega)
  simpa only [getElem!_pos t.lab i hi, getElem!_pos (s.lab.map σ.toFun) i hj] using hh

namespace SpecLeaf

/-- Transport a specification leaf's vertices, retaining its path codes. -/
@[expose] def map (p : Perm n) (leaf : SpecLeaf n) : SpecLeaf n :=
  ⟨leaf.codes, ⟨p.comp leaf.label.perm⟩⟩

theorem map_prepend (p : Perm n) (code : Nat) (leaf : SpecLeaf n) :
    (leaf.prepend code).map p = (leaf.map p).prepend code := rfl

/-- A transported leaf attains the identical sparse key under an
isomorphism, including every normalized native adjacency row. -/
theorem map_key (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) (leaf : SpecLeaf n) :
    (leaf.map p).key H = leaf.key G := by
  have hg : H.relabel (p.comp leaf.label.perm) = G.relabel leaf.label.perm := by
    apply Hex.SparseGraph.ext
    intro u v
    simp only [Hex.SparseGraph.adj_relabel, Perm.get_comp]
    exact hiso _ _
  simp only [map, key, hg]

/-- The executed label parser returns the transported typed label when
its input array is renamed. -/
theorem parse_map (p : Perm n) {lab : Array Nat} {label : Label n}
    (hp : lab.toList.Perm (List.range n)) (hl : Label.ofArray? n lab = some label) :
    Label.ofArray? n (lab.map (renamingOf p).toFun) = some ⟨p.comp label.perm⟩ := by
  obtain ⟨other, ho⟩ := Label.ofArray?_exists (perm_map hp p)
  have hsize : lab.size = n := by simpa using hp.length_eq
  have he : other = (⟨p.comp label.perm⟩ : Label n) := by
    apply Label.ext
    intro i
    apply Fin.ext
    change (other.get i).val = ((p.comp label.perm).get i).val
    rw [Perm.get_comp]
    rw [Label.ofArray?_get ho i.val i.isLt,
      getElem!_map_of_lt _ _ (by omega), ← Label.ofArray?_get hl i.val i.isLt,
      renamingOf_lt p (label.get i).isLt]
    rfl
  rw [ho, he]

end SpecLeaf
end Hex.GraphIso.Nauty.Sparse
