/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Canon
public import HexGraphIso.Nauty.Sparse.Literal.Check

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Literal

/-- Construct the checked native result with exported sparse relabelling. -/
def relabelColored (G : GraphIso.Sparse.Colored n k) (l : Label n) :
    GraphIso.Sparse.Colored n k where
  graph := relabel G.graph l.perm
  coloring := {
    cells := Hex.Vector.ofFn' fun i => G.coloring.cells[l.get i]
    onto := fun c => by
      obtain ⟨v, hv⟩ := G.coloring.onto c
      obtain ⟨i, hi⟩ := l.perm.get_surj v
      subst hi
      refine ⟨i, ?_⟩
      simpa [Hex.Vector.get_eq_getElem, Label.get] using hv }

theorem relabelColored_eq : @relabelColored = @GraphIso.Sparse.Colored.relabel := by
  funext n k G l
  simp only [relabelColored, GraphIso.Sparse.Colored.relabel, relabel_eq]

/-- Canonical colours obtained by the exported stable bucket initializer. -/
def colorSeq (G : GraphIso.Sparse.Colored n k) : List Nat :=
  (initialPartitionWith n k G.coloring.cells.toArray Fin.val).1.toList.map (rawColor G)

theorem colorSeq_eq : @colorSeq = @Sparse.colorSeq := by
  funext n k G
  simp only [colorSeq, Sparse.colorSeq, initialPartitionWith_eq]

/-- Literal result replay: parse the label, check the tree, and compare
native sparse graphs and ordered colours. -/
def checkCanon (G : GraphIso.Sparse.Colored n k) (c : CertCandidate n) :
    Option (GraphIso.Sparse.CanonResult n k) :=
  match label? n c.lab with
  | none => none
  | some l =>
    if checkKey G c.tree c.key &&
        (graphCmp c.key.graph (relabel G.graph l.perm) == .eq) &&
        (labelColors G l == colorSeq G) then
      some ⟨relabelColored G l, l⟩
    else none

theorem checkCanon_eq : @checkCanon = @Sparse.checkCanon := by
  funext n k G c
  simp only [checkCanon, Sparse.checkCanon, label?_eq, checkKey_eq,
    relabel_eq, relabelColored_eq, colorSeq_eq]
  rfl

theorem checkCanon_sound {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    {r : GraphIso.Sparse.CanonResult n k} (h : checkCanon G c = some r) :
    canonSpecKey G = c.key ∧ r.form = G.relabel r.label ∧
      r.form = GraphIso.Sparse.canon G := by
  rw [checkCanon_eq] at h
  exact Sparse.checkCanon_sound h

end Hex.GraphIso.Nauty.Sparse.Literal
