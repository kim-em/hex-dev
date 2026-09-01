/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search
public import HexGraphIso.Nauty.Equivariance

public section

/-!
The nauty-semantic canonical form as a total specification: the maximal
leaf key of the unpruned individualization-refinement tree.

A leaf key is the chain of refinement codes ending with the sentinel,
followed by the leaf's `g^lab` adjacency rows; keys compare
lexicographically, codes numerically and rows in nauty's row order.
The production search's canonical leaf realizes this maximum:

- a node whose chain is dominated (`compCanon < 0`) can never supply the
  canonical leaf, and those are exactly the nodes where nauty's
  history-dependent `firsttc` hint applies, so the specification's
  target-cell rule is the plain hint-free `targetcell`;
- the sentinel exceeds every real (cleaned) refinement code, which
  reproduces nauty's preference for shallower leaves on equal prefixes
  (`level < canonlevel` forcing `compCanon = 1`);
- children may be enumerated in any order under a maximum; the
  specification enumerates the target cell by position, which makes
  renaming-equivariance pointwise.

The branch guard is structural discreteness of the partition rather than
nauty's `numcells` counter; the two agree on every reachable state, and
the certificate checker replays concrete refinements where discreteness
is directly decidable.
-/

namespace Hex.GraphIso.Nauty

/-- A leaf key of the unpruned search tree: the level codes ending with
the sentinel, then the leaf's adjacency rows. -/
structure Key where
  /-- The refinement codes along the path, ending with the sentinel. -/
  codes : List Nat
  /-- The leaf's `g^lab` rows in nauty's row order. -/
  rows : List Nat
deriving Inhabited

/-- Lexicographic list comparison from an element comparison. -/
@[expose] def listCmp (cmp : Nat → Nat → Ordering) :
    List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmp a b with
    | .eq => listCmp cmp as bs
    | .lt => .lt
    | .gt => .gt

/-- Key order: level codes first, then rows in nauty's row order. -/
@[expose] def keyCmp (k1 k2 : Key) : Ordering :=
  match listCmp compare k1.codes k2.codes with
  | .eq => listCmp rowCmp k1.rows k2.rows
  | .lt => .lt
  | .gt => .gt

/-- The greater key, the first argument winning ties. -/
@[expose] def keyMax (k1 k2 : Key) : Key :=
  if keyCmp k1 k2 = .lt then k2 else k1

/-- The maximum of a list of keys, seeded by an initial key. -/
@[expose] def keysMax (k : Key) : List Key → Key
  | [] => k
  | k' :: rest => keysMax (keyMax k k') rest

/-- Discreteness of the partition at `level`: every cell a singleton. -/
@[expose] def discreteAt (ptn : Array Nat) (level nn : Nat) : Bool :=
  (cells ptn level nn).all fun p => p.1 == p.2

/-- The key of the maximal leaf of the unpruned search tree below one
node. -/
@[expose] def specNode (ctx : Ctx) (tcLevel : Nat) :
    Nat → Nat → Array Nat → Array Nat → Nat → Nat → Key
  | 0, _, _, _, _, _ => ⟨[], []⟩
  | fuel + 1, level, lab, ptn, active, numcells =>
    let rs := refine ctx level lab ptn active numcells
    if discreteAt rs.ptn level ctx.n then
      ⟨[rs.longcode, codeSentinel], leafRows ctx rs.lab⟩
    else
      let tcr := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      let children := (List.range tcr.2.2).map fun o =>
        let br := breakout rs.lab rs.ptn (level + 1) tcr.1 rs.lab[tcr.1 + o]!
        specNode ctx tcLevel fuel (level + 1) br.1 br.2.1 br.2.2
          (numcells + 1)
      match children with
      | [] => ⟨[], []⟩
      | c :: cs =>
        ⟨rs.longcode :: (keysMax c cs).codes, (keysMax c cs).rows⟩

/-- The canonical key of the unpruned nauty search on `n` vertices with
adjacency rows `g` and initial ordered partition `(lab0, cellEnds)`. -/
@[expose] def canonSpec (n : Nat) (g : Array Nat) (lab0 : Array Nat)
    (cellEnds : List Nat) : Key :=
  if n == 0 then
    ⟨[], []⟩
  else
    specNode { n, g } 100 (n + 2) 1 lab0 (initPtn n (n + 2) cellEnds)
      (initActive cellEnds) cellEnds.length

variable {n k : Nat}

/-- The nauty-semantic canonical key of a coloured graph. -/
@[expose] def canonSpecKey (G : Colored n k) : Key :=
  canonSpec n (rowsOf G) (initialPartition G).1 (initialPartition G).2

end Hex.GraphIso.Nauty
