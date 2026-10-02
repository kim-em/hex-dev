/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Code
public import HexGraphIso.Nauty.Sparse.SpecMax

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Sparse canonical proof records. Every branch names all target positions;
codes, partitions and labels are recomputed by the native sparse checker. -/
inductive CertNode where
  | leaf
  | codePrune
  /-- Reference a strictly earlier sibling through a checked raw automorphism.
  The expansion checker rejects references; compact replay checks their context. -/
  | autom (earlier : Nat) (images : Array Nat)
  | node (children : List CertNode)
deriving Repr

/-- Replay a sparse subtree against its claimed maximum suffix. Failure is
inconclusive; success records whether an actual leaf attains the bound. -/
@[expose] def checkNode (G : Hex.SparseGraph n) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → CertNode → Key n → Option Bool
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, level, lab, ptn, active, numcells, cert, B =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    match cert with
    | .autom _ _ => none
    | .leaf =>
      if discreteAt r.ptn level n then
        match Label.ofArray? n r.lab with
        | none => none
        | some l => Replay.leaf G B ⟨[r.longcode, codeSentinel], l⟩
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
@[expose] def checkKey (G : GraphIso.Sparse.Colored n k) (cert : CertNode) (B : Key n) : Bool :=
  if n = 0 then
    match cert with
    | .leaf => Replay.leaf G.graph B ⟨[codeSentinel], Label.id n⟩ == some true
    | _ => false
  else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    checkNode G.graph 100 (n + 2) 1 p.1 (initPtn n (n + 2) p.2)
      (initActive n p.2) p.2.length cert B == some true

end Hex.GraphIso.Nauty.Sparse
