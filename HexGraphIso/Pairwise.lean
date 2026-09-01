/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Iso
public import HexGraphIso.Lex
public import HexGraphIso.Canon

public section

/-!
A verified individualization-refinement isomorphism decision.

`decideIso?` runs one search over ordered-partition pairs: both graphs
are refined in lockstep by neighbour-count signatures, branches whose
refined partition structures diverge are pruned, and a vertex of the
first nonsingleton cell is individualized against every vertex of the
corresponding cell on the other side. A discrete pair induces one
candidate bijection, checked by the proven `checkIso`.

Both verdicts are sound theorems: `some true` produces a checked
transporter (`decideIso?_isomorphic`), and `some false` refutes every
colour-preserving isomorphism (`decideIso?_not_isomorphic`), because a
compatible isomorphism transports each refinement step (`Compat`
preservation) and is pinned to the induced bijection at a discrete
leaf. `none` is exhaustion of the node budget and decides nothing.

This is the verified engine behind the tactic's negative path: unlike
the reference enumeration it is feasible at practical sizes, and unlike
the nauty-compatible search it carries proofs. Its refinement is chosen
for proof cleanliness, not nauty compatibility; the certificate layer
for the nauty-exact search builds on the same equivariance techniques.
-/

namespace Hex.GraphIso.Pairwise

variable {n k : Nat}

/-- The cells of an ordered partition of `Fin n`. -/
abbrev Cells (n : Nat) := List (List (Fin n))

/-- The neighbour-count signature of `v` against the cells of `P`. -/
@[expose] def sig (G : Graph n) (P : Cells n) (v : Fin n) : List Nat :=
  P.map fun c => c.countP fun u => G.adj v u

/-- The distinct signatures occurring in a cell, in ascending order: a
canonical representative of the signature multiset. -/
@[expose] def cellSigs (G : Graph n) (P : Cells n) (c : List (Fin n)) :
    List (List Nat) :=
  dedupAdj (sortLe (c.map (sig G P)))

/-- Split one cell by signature: one group per distinct signature in
ascending signature order, members keeping their cell order. -/
@[expose] def splitCell (G : Graph n) (P : Cells n) (c : List (Fin n)) :
    Cells n :=
  (cellSigs G P c).map fun s => c.filter fun v => sig G P v == s

/-- One refinement round: split every cell against the current
partition. -/
@[expose] def refineRound (G : Graph n) (P : Cells n) : Cells n :=
  P.flatMap (splitCell G P)

/-- Iterated refinement. `n + 1` rounds always reach stability: a round
that splits nothing is the identity, and at most `n` splits can occur. -/
@[expose] def refineRounds (G : Graph n) : Nat → Cells n → Cells n
  | 0, P => P
  | r + 1, P => refineRounds G r (refineRound G P)

/-- The observable structure compared across the two sides: cell count,
cell sizes, and each cell's distinct-signature list. A compatible
isomorphism forces these to agree, so divergence refutes the branch. -/
@[expose] def shape (G : Graph n) (P : Cells n) : List (Nat × List (List Nat)) :=
  P.map fun c => (c.length, cellSigs G P c)

/-- The position of the first nonsingleton cell. -/
@[expose] def firstBig (P : Cells n) : Option (Nat × List (Fin n)) :=
  go 0 P
where
  go (i : Nat) : Cells n → Option (Nat × List (Fin n))
    | [] => none
    | c :: rest => if 2 ≤ c.length then some (i, c) else go (i + 1) rest

/-- Split `{v}` off the front of cell `i`. -/
@[expose] def individualize (P : Cells n) (i : Nat) (v : Fin n) : Cells n :=
  P.take i ++ [[v], (P[i]?.getD []).erase v] ++ P.drop (i + 1)

/-- The image of `v` under the correspondence induced by a discrete
partition pair: the partner of the first cell containing `v`. Identity
on malformed inputs; the result is only trusted through `checkIso`. -/
@[expose] def inducedFun (P Q : Cells n) (v : Fin n) : Fin n :=
  match (P.zip Q).find? fun cd => cd.1.contains v with
  | some (_, [w]) => w
  | _ => v

/-- The candidate transporter at a discrete pair, through the checked
permutation constructor. -/
@[expose] def inducedPerm (P Q : Cells n) : Perm n :=
  (permOfNatArray? n (Hex.Array.ofFn' fun v : Fin n => (inducedFun P Q v).val)).getD
    (Perm.id n)

/-- One expansion of a node: the child pairs individualizing `v` in `P`
against each `w` of the corresponding cell `d` of `Q`. -/
@[expose] def children (P Q : Cells n) (i : Nat) (v : Fin n)
    (d : List (Fin n)) : List (Cells n × Cells n) :=
  d.map fun w => (individualize P i v, individualize Q i w)

/-- Depth-first search over a worklist of partition pairs, structurally
recursive on the node budget so kernel replay can unfold it. `some true`
reports a checked isomorphism, `some false` an exhausted refuted
worklist, `none` budget exhaustion. -/
@[expose] def search (G H : Colored n k) :
    Nat → List (Cells n × Cells n) → Option Bool
  | 0, _ => none
  | _ + 1, [] => some false
  | budget + 1, (P, Q) :: stack =>
    let P' := refineRounds G.graph (n + 1) P
    let Q' := refineRounds H.graph (n + 1) Q
    if shape G.graph P' ≠ shape H.graph Q' then
      search G H budget stack
    else
      match firstBig P' with
      | none =>
        if checkIso G H (inducedPerm P' Q') then
          some true
        else
          search G H budget stack
      | some (i, c) =>
        match c with
        | [] => search G H budget stack
        | v :: _ =>
          search G H budget (children P' Q' i v (Q'[i]?.getD []) ++ stack)

/-- The root partition: one cell per colour, vertices in order. -/
@[expose] def colorCells (G : Colored n k) : Cells n :=
  (List.range k).map fun c =>
    (List.finRange n).filter fun v => G.coloring.cells[v].val == c

/-- The bounded verified isomorphism decision. `some true` and
`some false` are both proven verdicts; `none` is search exhaustion under
`maxNodes` and decides nothing. -/
@[expose] def decideIso? (limits : SearchLimits) (G H : Colored n k) :
    Option Bool :=
  search G H limits.maxNodes [(colorCells G, colorCells H)]

end Hex.GraphIso.Pairwise
