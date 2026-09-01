/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGraphIsoMathlib
import Mathlib.Data.Fintype.Powerset

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxRecDepth 400000

#doc (Manual) "HexGraphIso: coloured graph canonical labelling" =>
%%%
tag := "hex-graph-iso"
%%%

# Introduction
%%%
tag := "hex-graph-iso-intro"
%%%

`HexGraphIso` computes canonical forms and isomorphisms of finite simple
undirected graphs with ordered vertex colours. The canonical labelling
algorithm used in `HexGraphIso` is an exact translation of the
[nauty](https://users.cecs.anu.edu.au/~bdm/nauty/) 2.9.3 algorithm into Lean. (We
use conformance testing, rather than a theorem, to ensure they are
identical, and prove our theorems about the Lean translation.) Two
coloured graphs are isomorphic exactly when their canonical forms are
equal ({name Hex.GraphIso.iso_iff_canon_eq}`iso_iff_canon_eq`), and the
`graph_iso` tactic closes both positive and negative isomorphism goals with the
kernel performing the decisive replay: positive goals through the
checked transporter, negative goals through a fully verified
individualization-refinement decision.

{docstring Hex.GraphIso.Colored}

{docstring Hex.GraphIso.canonicalize}

{docstring Hex.GraphIso.Pairwise.search}

# The Petersen graph three ways
%%%
tag := "hex-graph-iso-petersen"
%%%

The Petersen graph is the standard first nontrivial example: below it
appears as the generalized Petersen presentation `G(5, 2)` — an outer
pentagon `0..4`, an inner five-point star `5..9`, and spokes — and as
the Kneser presentation `K(5, 2)`, whose vertices are the two-element
subsets of a five-element set, listed in lexicographic order
`01 02 03 04 12 13 14 23 24 34` and joined when disjoint. An outer
pentagon edge becomes a pair of disjoint subsets sharing no element with
its neighbour; the inner star and the spokes likewise map onto
disjointness of the remaining pairs.

```lean
open Hex Hex.GraphIso

namespace HexGraphIsoChapterExample

def petersen : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

def kneser52 : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 7), (0, 8), (0, 9), (1, 5), (1, 6), (1, 9), (2, 4), (2, 6),
       (2, 8), (3, 4), (3, 5), (3, 7), (4, 9), (5, 8), (6, 7)]
    coloring := Coloring.trivial 10 }

-- The two canonical searches find an explicit vertex permutation
-- between the two presentations; `checkIso` validates it.
#guard
  ((Nauty.canonicalize? petersen).bind fun rP =>
    (Nauty.canonicalize? kneser52).map fun rK =>
      checkIso petersen kneser52
        ((rK.label.toPerm.inv).comp rP.label.toPerm)).getD false

-- The tactic closes the positive goal through the kernel-replayed
-- transporter check.
example : Isomorphic petersen kneser52 := by graph_iso
```

The pentagonal prism is the interesting negative companion: like the
Petersen graph it has ten vertices, every one of degree three, so degree
refinement alone does not settle the question. The verified pairwise
decision individualizes a vertex, re-refines, and refutes every branch;
the kernel replays that run.

```lean
def prism5 : Colored 10 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
       (5, 6), (6, 7), (7, 8), (8, 9), (5, 9),
       (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)]
    coloring := Coloring.trivial 10 }

example : ¬ Isomorphic petersen prism5 := by graph_iso
```

# Ordered colours constrain isomorphisms
%%%
tag := "hex-graph-iso-colours"
%%%

nauty's colours are ordered: an isomorphism preserves each colour index
and may not permute the cells. Marking an adjacent pair of Petersen
vertices with colour zero is therefore a different constraint from
marking a non-adjacent pair, although the cell sizes agree. Adjacency of
the colour-zero pair is an invariant, and the tactic's negative proof is
obtained from the general verified decision rather than a handwritten
special-purpose lemma.

```lean
def markPair (a b : Fin 10) : Coloring 10 2 :=
  (Coloring.ofVector? (Hex.Vector.ofFn' fun i =>
    if i = a ∨ i = b then 0 else 1)).getD (Coloring.mod 10 2)

-- 0-1 is an outer pentagon edge; 2-3 likewise; 0-2 is a non-edge.
def edgeMarkA : Colored 10 2 := ⟨petersen.graph, markPair 0 1⟩
def edgeMarkB : Colored 10 2 := ⟨petersen.graph, markPair 2 3⟩
def nonedgeMark : Colored 10 2 := ⟨petersen.graph, markPair 0 2⟩

example : Isomorphic edgeMarkA edgeMarkB := by graph_iso
example : ¬ Isomorphic edgeMarkA nonedgeMark := by graph_iso
example : ¬ Isomorphic edgeMarkB nonedgeMark := by graph_iso

end HexGraphIsoChapterExample
```

# The Mathlib bridge
%%%
tag := "hex-graph-iso-mathlib"
%%%

`HexGraphIsoMathlib` relates the executable coloured graphs to Mathlib's
{name}`SimpleGraph` and extends the same `graph_iso` syntax to closed
ground `SimpleGraph` terms. The two presentations below deliberately
have different vertex types — `Fin 10` and the two-element subsets of
`Fin 5` — so the positive goal genuinely enumerates two unrelated finite
types and returns a `SimpleGraph.Iso`, rather than recognizing a
definitional equality.

{docstring Hex.GraphIso.Mathlib.Colored}

{docstring Hex.GraphIso.Mathlib.encode}

{docstring Hex.GraphIso.Mathlib.colored_iso_iff_canon_eq}

```lean
open Hex.GraphIso.Mathlib

namespace HexGraphIsoMathlibChapterExample

def petersenDrawing : SimpleGraph (Fin 10) where
  Adj i j :=
    (i.val < 5 ∧ j.val < 5 ∧
      (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
    (5 ≤ i.val ∧ 5 ≤ j.val ∧
      (j.val = 5 + ((i.val + 2) % 5) ∨ i.val = 5 + ((j.val + 2) % 5))) ∨
    (i.val < 5 ∧ j.val = i.val + 5) ∨ (j.val < 5 ∧ i.val = j.val + 5)
  symm := ⟨by intro i j h; omega⟩
  loopless := ⟨by intro i h; omega⟩

instance : DecidableRel petersenDrawing.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

def kneser52 : SimpleGraph {s : Finset (Fin 5) // s.card = 2} where
  Adj s t := Disjoint s.val t.val ∧ s ≠ t
  symm := ⟨by intro s t h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro s h; exact h.2 rfl⟩

instance : DecidableRel kneser52.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

def pentagonalPrism : SimpleGraph (Fin 10) where
  Adj i j :=
    (i.val < 5 ∧ j.val < 5 ∧
      (j.val = (i.val + 1) % 5 ∨ i.val = (j.val + 1) % 5)) ∨
    (5 ≤ i.val ∧ 5 ≤ j.val ∧
      (j.val = 5 + ((i.val + 1) % 5) ∨ i.val = 5 + ((j.val + 1) % 5))) ∨
    (i.val < 5 ∧ j.val = i.val + 5) ∨ (j.val < 5 ∧ i.val = j.val + 5)
  symm := ⟨by intro i j h; omega⟩
  loopless := ⟨by intro i h; omega⟩

instance : DecidableRel pentagonalPrism.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

example : Nonempty (petersenDrawing ≃g kneser52) := by graph_iso

example : IsEmpty (petersenDrawing ≃g pentagonalPrism) := by graph_iso

end HexGraphIsoMathlibChapterExample
```

Neither proof requires an external nauty installation, and no proof
path uses `native_decide` or introduces an axiom.
