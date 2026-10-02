/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.CompactCanon
public import HexGraphIso.Nauty.Sparse.Literal.Canon

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Literal.Compact

/-- Literal compact replay using the exported sparse refinement operations
and exactly the same checked sibling-reference scan as native replay. -/
def checkNode (G : Hex.SparseGraph n) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → CertNode → Key n → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, B =>
    match cert with
    | .node children =>
      let r := Literal.refine (.ofGraph G) level lab ptn active numcells
      match B.codes with
      | [] => none
      | b :: bs =>
        if r.longcode = b ∧ discreteAt r.ptn level n = false then
          let t := Literal.maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
          if children.length = t.2.2 then
            Sparse.Compact.checkChildren G level r.lab r.ptn t.1 (fun o c =>
              let child := breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
              checkNode G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
                (r.numcells + 1) c ⟨bs, B.graph⟩) children
          else none
        else none
    | _ => Literal.checkNode G tcLevel (fuel + 1) level lab ptn active numcells cert B
  termination_by structural fuel => fuel

theorem checkNode_eq : @checkNode = @Sparse.Compact.checkNode := by
  funext n G tcLevel fuel level lab ptn active numcells cert B
  induction fuel generalizing level lab ptn active numcells cert B with
  | zero => rfl
  | succ fuel ih =>
    simp only [checkNode, Sparse.Compact.checkNode, Literal.refine_eq,
      Literal.maketargetcell_eq, Literal.checkNode_eq, ih]
    rfl

def checkKey (G : GraphIso.Sparse.Colored n k) (cert : CertNode) (B : Key n) : Bool :=
  if n = 0 then Literal.checkKey G cert B else
    let p := Literal.initialPartitionWith n k G.coloring.cells.toArray Fin.val
    checkNode G.graph 100 (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length cert B == some true

theorem checkKey_eq : @checkKey = @Sparse.Compact.checkKey := by
  funext n k G cert B
  simp only [checkKey, Sparse.Compact.checkKey, Literal.initialPartitionWith_eq,
    checkNode_eq, Literal.checkKey_eq]

theorem checkKey_sound {G : GraphIso.Sparse.Colored n k} {cert : CertNode} {B : Key n}
    (h : checkKey G cert B = true) : canonSpecKey G = B :=
  Sparse.Compact.checkKey_sound (by simpa only [checkKey_eq] using h)

theorem not_isomorphic_of_checkKeys {G H : GraphIso.Sparse.Colored n k}
    {cg ch : CertNode} {bg bh : Key n}
    (hg : checkKey G cg bg = true) (hh : checkKey H ch bh = true)
    (hd : checkDiff bg bh = true) : ¬ GraphIso.Sparse.Isomorphic G H := by
  intro hiso
  apply checkDiff_sound hd
  rw [← checkKey_sound hg, ← checkKey_sound hh]
  obtain ⟨p, hp⟩ := hiso.elim
  exact canonSpecKey_map hp

/-- Literal replay of the compact certificate and its attaining label. -/
def checkCanon (G : GraphIso.Sparse.Colored n k) (c : CertCandidate n) :
    Option (GraphIso.Sparse.CanonResult n k) :=
  match Literal.label? n c.lab with
  | none => none
  | some l =>
    if checkKey G c.tree c.key &&
        (graphCmp c.key.graph (Literal.relabel G.graph l.perm) == .eq) &&
        (labelColors G l == Literal.colorSeq G) then
      some ⟨Literal.relabelColored G l, l⟩
    else none

theorem checkCanon_eq : @checkCanon = @Sparse.Compact.checkCanon := by
  funext n k G c
  simp only [checkCanon, Sparse.Compact.checkCanon, Literal.label?_eq, checkKey_eq,
    Literal.relabel_eq, Literal.relabelColored_eq, Literal.colorSeq_eq]
  rfl

theorem checkCanon_sound {G : GraphIso.Sparse.Colored n k} {c : CertCandidate n}
    {r : GraphIso.Sparse.CanonResult n k} (h : checkCanon G c = some r) :
    canonSpecKey G = c.key ∧ r.form = G.relabel r.label ∧
      r.form = GraphIso.Sparse.canon G := by
  rw [checkCanon_eq] at h
  exact Sparse.Compact.checkCanon_sound h

end Hex.GraphIso.Nauty.Sparse.Literal.Compact
