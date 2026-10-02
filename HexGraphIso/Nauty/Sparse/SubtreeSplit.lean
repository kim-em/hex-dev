/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SubtreeKey
public import HexGraphIso.Nauty.Sparse.VertexKey
public import HexGraphIso.Nauty.Sparse.PrefixKey

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every child selected by the unpruned node's native target dispatch has
the full entry invariant, including its inherited refinement certificate. -/
theorem SpecNode.target_child {G : Hex.SparseGraph n} {tcLevel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} (h : SpecNode G level lab ptn active numcells) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
    discreteAt r.ptn level n = false → ∀ o, o < target.2.2 →
      let child := breakout n r.lab r.ptn (level + 1) target.1 r.lab[target.1 + o]!
      SpecNode G (level + 1) child.1 child.2.1 child.2.2 (r.numcells + 1) := by
  intro r target hd o ho
  have hr := h.refined.1
  have heq := h.refined.2
  have hend : r.ptn[n - 1]! ≤ level := by simpa only [hr.node.ptnSize] using hr.node.ptnEnd
  have hcount : bcount r.ptn level n < n := by
    have hb := bcount_le r.ptn level n
    have hne : bcount r.ptn level n ≠ n := by
      intro he
      have ht := (discreteAt_iff_bcount hr.node.ptnSize.symm hr.node.ptnEnd).mpr he
      rw [hd] at ht
      contradiction
    omega
  obtain ⟨hc, hlen, hb⟩ := maketargetcell_valid G r.lab r.ptn level tcLevel (-1)
    hr.label hr.node.ptnSize hend hcount
  exact hr.child heq hc hb hlen ho

/-- The discrete unpruned node has exactly the key read from its executed
refinement and parsed leaf label. -/
theorem subtreeKey_discrete {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {label : Label n} :
    let r := refine (.ofGraph G) level lab ptn active numcells
    discreteAt r.ptn level n = true → Label.ofArray? n r.lab = some label →
      subtreeKey G tcLevel (fuel + 1) level lab ptn active numcells =
        ⟨[r.longcode, codeSentinel], G.relabel label.perm⟩ := by
  intro r hd hp
  rw [subtreeKey, specLeaves]
  change SpecLeaf.maximum G (if discreteAt r.ptn level n then _ else _) = _
  rw [hd, ite_eq_left rfl, hp]
  rfl

/-- A child's entire maximum, prefixed by this node's code, lies below
the node maximum. Sufficient fuel supplies its literal attaining leaf. -/
theorem SpecNode.child_le {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} (h : SpecNode G level lab ptn active numcells)
    (hf : n < (fuel + 1) + numcells) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
    discreteAt r.ptn level n = false → ∀ o, o < target.2.2 →
      Key.Le (prefixKey [r.longcode]
        (vertexKey G tcLevel fuel level r.lab r.ptn target.1 r.numcells r.lab[target.1 + o]!))
        (subtreeKey G tcLevel (fuel + 1) level lab ptn active numcells) := by
  intro r target hd o ho
  have hc := h.target_child hd o ho
  have hcount : numcells ≤ r.numcells :=
    (refine_node G level lab ptn active numcells h.label h.node h.count).2.2.2
  have hchildfuel : n < fuel + (r.numcells + 1) := by omega
  obtain ⟨leaf, hm, he⟩ := hc.key_attains (tcLevel := tcLevel) (fuel := fuel) hchildfuel
  have hparent : leaf.prepend r.longcode ∈ specLeaves G tcLevel (fuel + 1) level lab ptn active numcells := by
    rw [specLeaves]
    change _ ∈ (if discreteAt r.ptn level n then _ else _)
    rw [hd, ite_eq_right (by decide)]
    apply List.mem_flatMap.mpr
    exact ⟨o, List.mem_range.mpr ho, List.mem_map.mpr ⟨leaf, hm, rfl⟩⟩
  have hb := subtreeKey_bound hparent
  change Key.Le (prefixKey [r.longcode] (leaf.key G)) _ at hb
  rw [he] at hb
  exact hb

/-- Bounding every complete child bounds the complete parent. The proof
decomposes an actual attaining leaf of the existing unpruned enumeration. -/
theorem SpecNode.key_le {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {bound : Key n}
    (h : SpecNode G level lab ptn active numcells) (hf : n < (fuel + 1) + numcells) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
    discreteAt r.ptn level n = false →
      (∀ o, o < target.2.2 → Key.Le (prefixKey [r.longcode]
        (vertexKey G tcLevel fuel level r.lab r.ptn target.1 r.numcells r.lab[target.1 + o]!)) bound) →
      Key.Le (subtreeKey G tcLevel (fuel + 1) level lab ptn active numcells) bound := by
  intro r target hd hchildren
  obtain ⟨leaf, hm, he⟩ := h.key_attains (tcLevel := tcLevel) (fuel := fuel + 1) hf
  rw [specLeaves] at hm
  change leaf ∈ (if discreteAt r.ptn level n then _ else _) at hm
  rw [hd, ite_eq_right (by decide)] at hm
  obtain ⟨o, ho, hlocal⟩ := List.mem_flatMap.mp hm
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hlocal
  rw [← he]
  exact Key.le_trans (prefixKey_le [r.longcode] (subtreeKey_bound hchild))
    (hchildren o (List.mem_range.mp ho))

/-- An internal node's maximum is attained by one of its complete child
maxima. The child is obtained from a literal attaining specification leaf. -/
theorem SpecNode.child_attains {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} (h : SpecNode G level lab ptn active numcells)
    (hf : n < (fuel + 1) + numcells) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
    discreteAt r.ptn level n = false →
      ∃ o, o < target.2.2 ∧ prefixKey [r.longcode]
        (vertexKey G tcLevel fuel level r.lab r.ptn target.1 r.numcells r.lab[target.1 + o]!) =
        subtreeKey G tcLevel (fuel + 1) level lab ptn active numcells := by
  intro r target hd
  obtain ⟨leaf, hm, he⟩ := h.key_attains (tcLevel := tcLevel) (fuel := fuel + 1) hf
  rw [specLeaves] at hm
  change leaf ∈ (if discreteAt r.ptn level n then _ else _) at hm
  rw [hd, ite_eq_right (by decide)] at hm
  obtain ⟨o, ho, hlocal⟩ := List.mem_flatMap.mp hm
  obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hlocal
  refine ⟨o, List.mem_range.mp ho, Key.le_antisymm (h.child_le hf hd o (List.mem_range.mp ho)) ?_⟩
  rw [← he]
  exact prefixKey_le [r.longcode] (subtreeKey_bound hchild)

/-- Every sufficiently fueled node maximum begins with that node's
literal refinement code, irrespective of the chosen descendant. -/
theorem SpecNode.key_prefix {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} (h : SpecNode G level lab ptn active numcells)
    (hf : n < (fuel + 1) + numcells) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    ∃ cs, (subtreeKey G tcLevel (fuel + 1) level lab ptn active numcells).codes = r.longcode :: cs := by
  intro r
  obtain ⟨leaf, hm, he⟩ := h.key_attains (tcLevel := tcLevel) (fuel := fuel + 1) hf
  rw [← he]
  change ∃ cs, leaf.codes = r.longcode :: cs
  rw [specLeaves] at hm
  change leaf ∈ (if discreteAt r.ptn level n then _ else _) at hm
  split at hm
  · split at hm
    · cases hm
    · have hh := List.mem_singleton.mp hm
      subst leaf
      exact ⟨[codeSentinel], rfl⟩
  · obtain ⟨o, _, hlocal⟩ := List.mem_flatMap.mp hm
    obtain ⟨child, _, rfl⟩ := List.mem_map.mp hlocal
    exact ⟨child.codes, rfl⟩

end Hex.GraphIso.Nauty.Sparse
