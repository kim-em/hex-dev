/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeBound
import all HexGraphIso.Nauty.Sparse.Coverage

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- A native node frozen at entry, together with its preceding refinement codes. -/
structure Frame (n : Nat) where
  level : Nat
  numcells : Nat
  codes : List Nat
  entry : State n

/-- The complete sparse subtree with a depth-derived sufficient fuel bound. -/
def Frame.key (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n) : Key n :=
  prefixKey f.codes (subtreeKey G tcLevel (n + 1 - f.level) f.level
    f.entry.lab f.entry.ptn f.entry.active f.numcells)

/-- The literal code computed by the cached native visit. -/
def Frame.code (G : Hex.SparseGraph n) (f : Frame n) : Nat :=
  (visit (.ofGraph G) f.level f.numcells f.entry).2.1

/-- Frozen entries retain the native structural invariant and code depth. -/
structure Frame.Valid (G : GraphIso.Sparse.Colored n k) (f : Frame n) : Prop where
  positive : 1 ≤ f.level
  length : f.codes.length + 1 = f.level
  node : NodeInv G f.level f.numcells f.entry

theorem Frame.Valid.depth {G : GraphIso.Sparse.Colored n k} {f : Frame n}
    (h : f.Valid G) : f.level ≤ n :=
  Nat.le_trans h.node.ok.bc (bcount_le _ _ _)

/-- The complete subtree starts with the code of its executed cached visit. -/
theorem Frame.Valid.tail {G : GraphIso.Sparse.Colored n k} {f : Frame n}
    (h : f.Valid G) (tcLevel : Nat) :
    ∃ tail : Key n, f.key G.graph tcLevel = prefixKey (f.codes ++ [f.code G.graph]) tail := by
  have hd := h.depth
  have hn : 0 < n := by have := h.positive; omega
  have hf : n + 1 - f.level = (n - f.level) + 1 := by omega
  have hcount := h.node.spec.depth
  obtain ⟨cs, hcs⟩ := h.node.spec.key_prefix (tcLevel := tcLevel)
    (fuel := n - f.level) (by omega)
  have hc : (refine (.ofGraph G.graph) f.level f.entry.lab f.entry.ptn
      f.entry.active f.numcells).longcode =
      (visit (.ofGraph G.graph) f.level f.numcells f.entry).2.1 :=
    (h.node.visit_equiv hn h.positive).2.1
  refine ⟨⟨cs, (subtreeKey G.graph tcLevel (n - f.level + 1) f.level
    f.entry.lab f.entry.ptn f.entry.active f.numcells).graph⟩, ?_⟩
  simp only [Frame.key, hf, prefixKey, Frame.code, hcs, hc,
    List.append_assoc, List.singleton_append]

/-- A returned ancestor is covered directly or by rejection of every
continuation of its first actual refinement code. -/
def Frame.Witness (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (best : Option (Key n)) : Prop :=
  Covers (f.key G tcLevel) best ∨
    ∀ tail : Key n, Covers (prefixKey (f.codes ++ [f.code G]) tail) best

theorem Frame.Witness.resolve {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {best : Option (Key n)} (h : f.Witness G.graph tcLevel best)
    (hv : f.Valid G) : Covers (f.key G.graph tcLevel) best := by
  rcases h with h | h
  · exact h
  · obtain ⟨tail, he⟩ := hv.tail tcLevel
    rw [he]
    exact h tail

theorem Frame.Witness.grow {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    {before after : Option (Key n)} (h : f.Witness G tcLevel before)
    (hg : Grows before after) : f.Witness G tcLevel after := by
  rcases h with h | h
  · exact Or.inl (h.grow hg)
  · exact Or.inr (fun tail => (h tail).grow hg)

/-- Frozen native subtrees indexed by the sweep receiving their return. -/
abbrev Frames (n : Nat) := Nat → Option (Frame n)

def Frames.insert (frames : Frames n) (f : Frame n) : Frames n :=
  fun level => if level = f.level - 1 then some f else frames level

/-- A nonlocal exit names a valid frozen ancestor and its coverage witness. -/
def Witness (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat) (frames : Frames n)
    (target : Nat) (best : Option (Key n)) : Prop :=
  ∃ f, frames target = some f ∧ f.Valid G ∧ f.Witness G.graph tcLevel best

theorem Witness.resolve {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {frames : Frames n} {f : Frame n} {best : Option (Key n)}
    (h : Witness G tcLevel (frames.insert f) (f.level - 1) best) :
    Covers (f.key G.graph tcLevel) best := by
  obtain ⟨other, he, hv, hw⟩ := h
  simp only [Frames.insert, ↓reduceIte, Option.some.injEq] at he
  subst other
  exact hw.resolve hv

theorem Witness.below {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {frames : Frames n} {f : Frame n} {best : Option (Key n)} (ht : target < f.level - 1) :
    Witness G tcLevel (frames.insert f) target best ↔ Witness G tcLevel frames target best := by
  simp only [Witness, Frames.insert, ite_eq_right (by omega : target ≠ f.level - 1)]

theorem Witness.grow {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {frames : Frames n} {before after : Option (Key n)}
    (h : Witness G tcLevel frames target before) (hg : Grows before after) :
    Witness G tcLevel frames target after := by
  obtain ⟨f, hf, hv, hw⟩ := h
  exact ⟨f, hf, hv, hw.grow hg⟩

end Hex.GraphIso.Nauty.Sparse.Max
