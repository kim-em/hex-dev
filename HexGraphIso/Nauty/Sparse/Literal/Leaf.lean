/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Rules
public import HexBasic.OfFn

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Literal

/-- The checked label parser with exported list-based array mapping. -/
def label? (n : Nat) (lab : Array Nat) : Option (Label n) :=
  if h : lab.size = n ∧ ∀ v ∈ lab, v < n then
    Label.ofVector? ⟨Hex.Array.map' (fun v =>
      (⟨v.val, h.2 v.val v.property⟩ : Fin n)) lab.attach, by simp [h.1]⟩
  else none

theorem label?_eq : label? = Label.ofArray? := by
  funext n lab
  simp only [label?, Label.ofArray?, Hex.Array.map'_eq_map]

/-- Native sparse relabelling with exported function tabulation. -/
def relabel (G : SparseGraph n) (p : Perm n) : SparseGraph n :=
  let q := p.inv
  let rows := Hex.Vector.ofFn' fun i =>
    Hex.SparseGraph.Builder.mapRow (G.nbrs (p.get i)) q.get
  Hex.SparseGraph.ofRows rows
    (fun i => by simp [rows, Hex.Vector.ofFn'_eq_ofFn, Hex.SparseGraph.Builder.mapRow, Hex.SparseGraph.Builder.sorted_normalize])
    (fun i j => by
      simp only [rows, Hex.Vector.ofFn'_eq_ofFn, Hex.SparseGraph.Builder.mapRow, Fin.getElem_fin, Vector.getElem_ofFn, Hex.SparseGraph.Builder.mem_normalize,
        List.mem_map, Array.mem_toList_iff]
      constructor
      · rintro ⟨v, hv, he⟩
        have hvj : v = p.get j := by rw [← he, Perm.get_inv_get]
        refine ⟨p.get i, ?_, Perm.inv_get_get p i⟩
        rw [hvj] at hv
        exact (G.symm (p.get i) (p.get j)).mp hv
      · rintro ⟨v, hv, he⟩
        have hvi : v = p.get i := by rw [← he, Perm.get_inv_get]
        refine ⟨p.get j, ?_, Perm.inv_get_get p j⟩
        rw [hvi] at hv
        exact (G.symm (p.get j) (p.get i)).mp hv)
    (fun i => by
      simp only [rows, Hex.Vector.ofFn'_eq_ofFn, Hex.SparseGraph.Builder.mapRow, Fin.getElem_fin, Vector.getElem_ofFn, Hex.SparseGraph.Builder.mem_normalize,
        List.mem_map, Array.mem_toList_iff]
      rintro ⟨v, hv, he⟩
      have hvi : v = p.get i := by rw [← he, Perm.get_inv_get]
      rw [hvi] at hv
      exact G.loopless (p.get i) hv)

theorem relabel_eq : @relabel = @Hex.SparseGraph.relabel := by
  funext n G p
  simp only [relabel, Hex.SparseGraph.relabel, Hex.Vector.ofFn'_eq_ofFn]

/-- Compare an actual leaf using native sparse rows and the exported
relabelling operations. -/
def leaf (G : Hex.SparseGraph n) (B : Key n) (l : SpecLeaf n) : Option Bool :=
  match Key.cmp ⟨l.codes, relabel G l.label.perm⟩ B with
  | .gt => none
  | .eq => some true
  | .lt => some false

theorem leaf_eq : @leaf = @Replay.leaf := by
  funext n G B l
  simp only [leaf, Replay.leaf, SpecLeaf.key, relabel_eq]
  rfl

end Hex.GraphIso.Nauty.Sparse.Literal
