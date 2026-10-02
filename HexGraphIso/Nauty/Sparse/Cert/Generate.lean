/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Compact
public import HexGraphIso.Nauty.Sparse.Cert.Emit
public import HexGraphIso.Nauty.Cert.CertAutom

public section

namespace Hex.GraphIso.Nauty.Sparse.Compact

/-- Filter the production generators by the current ordered cells and retain
their inverses for the graph-independent orbit-witness BFS. This is only a
proposal filter: every emitted witness passes the sparse checker. -/
@[expose] def usable (gens : List (Perm n)) (lab ptn : Array Nat) (level : Nat) :
    Array (Array Nat × Array Nat) :=
  let masks := cellMasks n lab ptn level
  (gens.filterMap fun p =>
    let raw := p.vec.toArray.map Fin.val
    if respectsMasks masks raw then some (raw, p.inv.vec.toArray.map Fin.val)
    else none).toArray

/-- Propose an earlier-to-current witness by inverting the BFS path from
the current target vertex to an earlier one. -/
@[expose] def choose (n : Nat) (lab : Array Nat) (tc : Nat)
    (gens : Array (Array Nat × Array Nat)) (o : Nat) : Option (Nat × Array Nat) :=
  (witness? n lab tc gens o).map fun (earlier, raw) => (earlier, invPerm raw)

/-- Generate a compact proof subtree against the actual search's key.
Successful witnesses prevent recursive expansion; every other target member
uses the full sparse proof traversal. No dense graph is constructed. -/
@[expose] def produceNode (G : Hex.SparseGraph n) (tcLevel : Nat) (gens : List (Perm n)) :
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
        let child := fun o => breakout n r.lab r.ptn (level + 1) t.1 r.lab[t.1 + o]!
        let proposals := choose (n := n) r.lab t.1 (usable gens r.lab r.ptn level)
        let witness := fun o earlier raw => Replay.checkAutom G (level + 1)
          (child earlier).1 (child o).1 (child o).2.1 raw
        let fallback := fun o => produceNode G tcLevel gens fuel (level + 1)
          (child o).1 (child o).2.1 (child o).2.2 (r.numcells + 1) ⟨bs, B.graph⟩
        .node ((List.range t.2.2).map (Replay.emit proposals witness fallback))
  termination_by structural fuel => fuel

/-- Top-level producer records are ordinary nodes; references are only
emitted inside the checked sibling context. -/
theorem produceNode_ne_autom (G : Hex.SparseGraph n) (tcLevel : Nat) (gens : List (Perm n))
    (fuel level : Nat) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (B : Key n)
    (earlier : Nat) (raw : Array Nat) :
    produceNode G tcLevel gens fuel level lab ptn active numcells B ≠ .autom earlier raw := by
  cases fuel with
  | zero => simp [produceNode]
  | succ fuel =>
    simp only [produceNode]
    split
    · simp
    · split
      · simp
      · split <;> simp

end Hex.GraphIso.Nauty.Sparse.Compact
