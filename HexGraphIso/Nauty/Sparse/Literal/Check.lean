/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Decision
public import HexGraphIso.Nauty.Sparse.Literal.Target
public import HexGraphIso.Nauty.Sparse.Literal.Leaf

@[expose] public section

namespace Hex.GraphIso.Nauty.Sparse.Literal

/-- Replay a sparse subtree against its claimed maximum suffix. Failure is
inconclusive; success records whether an actual leaf attains the bound. -/
def checkNode (G : Hex.SparseGraph n) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → CertNode → Key n → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, B =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    match cert with
    | .autom _ _ => none
    | .leaf =>
      if discreteAt r.ptn level n then
        match label? n r.lab with
        | none => none
        | some l => leaf G B ⟨[r.longcode, codeSentinel], l⟩
      else none
    | .codePrune =>
      match B.codes with
      | [] => none
      | b :: _ => if compare r.longcode b = .lt then some false else none
    | .node children =>
      match B.codes with
      | [] => none
      | b :: bs =>
        if r.longcode = b ∧ discreteAt r.ptn level n = false then
          let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
          if children.length = t.2.2 then
            Replay.all (fun (co : CertNode × Nat) =>
              let child := breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + co.2]!
              checkNode G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
                (r.numcells + 1) co.1 ⟨bs, B.graph⟩) children.zipIdx
          else none
        else none
  termination_by structural fuel => fuel

/-- Check a sparse key from the actual stable ordered colour buckets. The
empty input retains its unique empty label and terminal sentinel. -/
def checkKey (G : GraphIso.Sparse.Colored n k) (cert : CertNode) (B : Key n) : Bool :=
  if n = 0 then
    match cert with
    | .leaf => leaf G.graph B ⟨[codeSentinel], Label.id n⟩ == some true
    | _ => false
  else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    checkNode G.graph 100 (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length cert B == some true

/-- Literal replay follows exactly the specification checker. Only the
bounded iterator spelling changes; native sparse operations and all proof
rules retain their values. -/
theorem checkNode_eq : @checkNode = @Sparse.checkNode := by
  funext n G tcLevel fuel level lab ptn active numcells cert B
  induction fuel generalizing level lab ptn active numcells cert B with
  | zero => rfl
  | succ fuel ih =>
    simp only [checkNode, Sparse.checkNode, refine_eq, maketargetcell_eq, label?_eq, leaf_eq, ih]
    rfl

theorem checkKey_eq : @checkKey = @Sparse.checkKey := by
  funext n k G cert B
  simp only [checkKey, Sparse.checkKey, initialPartitionWith_eq, checkNode_eq, leaf_eq]
  rfl

/-- Kernel acceptance of the literal sparse replay identifies the full
canonical key. -/
theorem checkKey_sound {G : GraphIso.Sparse.Colored n k} {cert : CertNode} {B : Key n}
    (h : checkKey G cert B = true) : canonSpecKey G = B :=
  Sparse.checkKey_sound (by simpa only [checkKey_eq] using h)

theorem not_isomorphic_of_checkKeys {G H : GraphIso.Sparse.Colored n k}
    {cg ch : CertNode} {bg bh : Key n}
    (hg : checkKey G cg bg = true) (hh : checkKey H ch bh = true)
    (hd : checkDiff bg bh = true) : ¬ GraphIso.Sparse.Isomorphic G H :=
  Sparse.not_isomorphic_of_checkKeys
    (by simpa only [checkKey_eq] using hg) (by simpa only [checkKey_eq] using hh) hd

end Hex.GraphIso.Nauty.Sparse.Literal
