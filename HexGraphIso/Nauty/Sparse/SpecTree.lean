/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetValid
public import HexGraphIso.Nauty.Sparse.Key

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An unpruned leaf carries its complete refinement-code chain and the
labelling that attains its normalized sparse graph. -/
structure SpecLeaf (n : Nat) where
  codes : List Nat
  label : Label n

namespace SpecLeaf

@[expose] def key (G : Hex.SparseGraph n) (leaf : SpecLeaf n) : Key n :=
  ⟨leaf.codes, G.relabel leaf.label.perm⟩

@[expose] def prepend (code : Nat) (leaf : SpecLeaf n) : SpecLeaf n :=
  { leaf with codes := code :: leaf.codes }

end SpecLeaf

/-- The finite unpruned sparse tree. Each node executes sparse refinement,
uses hint-free sparse target selection, and includes every target member.
Zero fuel produces no leaf; sufficient-fuel theorems exclude that case for
valid roots and descendants. No production pruning enters this definition. -/
@[expose] def specLeaves (G : Hex.SparseGraph n) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → VSet n → Nat → List (SpecLeaf n)
  | 0, _, _, _, _, _ => []
  | fuel + 1, level, lab, ptn, active, numcells =>
    let r := refine (.ofGraph G) level lab ptn active numcells
    if discreteAt r.ptn level n then
      match Label.ofArray? n r.lab with
      | none => []
      | some l => [⟨[r.longcode, codeSentinel], l⟩]
    else
      let target := maketargetcell (.ofGraph G) r.lab r.ptn level tcLevel (-1)
      (List.range target.2.2).flatMap fun offset =>
        let child := breakout n r.lab r.ptn (level + 1) target.1 r.lab[target.1 + offset]!
        (specLeaves G tcLevel fuel (level + 1) child.1 child.2.1 child.2.2
          (r.numcells + 1)).map (SpecLeaf.prepend r.longcode)

/-- Enumerate the unpruned tree from the actual stable sparse colour buckets.
The empty graph has the unique empty labelling and terminal sentinel. -/
@[expose] def rootLeaves (G : GraphIso.Sparse.Colored n k) : List (SpecLeaf n) :=
  if n = 0 then [⟨[codeSentinel], Label.id n⟩]
  else
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    specLeaves G.graph 100 (n + 2) 1 p.1 (initPtn n (n + 2) p.2) (initActive n p.2) p.2.length

end Hex.GraphIso.Nauty.Sparse
