/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Sound

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Expand a native proof subtree against a supplied key, discarding nodes
whose recomputed code is strictly smaller. The optimized canonical search
supplies the key; this traversal produces proof records, not a new maximum. -/
@[expose] def produceNode (G : Hex.SparseGraph n) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → Key n → CertNode
  | 0, _, _, _, _, _, _ => .leaf
  | fuel + 1, level, lab, ptn, active, numcells, B =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    match B.codes with
    | [] => .leaf
    | b :: bs =>
      if compare r.longcode b = .lt then .codePrune
      else if discreteAt r.ptn level n then .leaf
      else
        let t := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
        .node ((List.range t.2.2).map fun o =>
          let child := breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
          produceNode G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
            (r.numcells + 1) ⟨bs, B.graph⟩)
  termination_by structural fuel => fuel

end Hex.GraphIso.Nauty.Sparse
