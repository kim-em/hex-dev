/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGraphIsoMathlib
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

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
identical, and prove our theorems about the Lean translation.) The exact
algorithm, including the output-relevant choices absent from the published
literature, is specified in {ref "nauty-algorithm"}[The `nauty` canonical
labelling algorithm]. The
public names (`canonicalize`, `canon`, `label`, `isIso`) run that
translation directly, and the theorems reach them because a proven
certificate checker is shown to accept the translation's answer on
every input. Two coloured graphs are isomorphic exactly when their
canonical forms are equal
({name Hex.GraphIso.iso_iff_canon_eq}`iso_iff_canon_eq`),
and the
`graph_iso` tactic closes both positive and negative isomorphism goals with the
kernel performing the decisive replay: positive goals through the
checked transporter, negative goals through a checked canonical-key
certificate when available and a fully verified
individualization-refinement decision as the exhaustion fallback.

Colours are the general input, but a graph with no colours to speak of
should not have to acquire one. The same operations and the same
tactic are available on a bare {name Hex.Graph}`Graph`: `Graph.canon`,
`Graph.findIso`, `Graph.isIso` and the rest read the one-cell
view {name Hex.Graph.singleColor}`Graph.singleColor` and hand the
conclusion back uncoloured, through the single equivalence
{name Hex.Graph.isomorphic_singleColor_iff}`Graph.isomorphic_singleColor_iff`.

The separate [`nauty-ffi`](https://github.com/leanprover/nauty-ffi) package is
available for users who want direct access to the corresponding dense-nauty
operations from Lean. It is an unverified native convenience package, not a
dependency or part of the verified `HexGraphIso` library.

{docstring Hex.GraphIso.Colored}

{docstring Hex.GraphIso.canonicalize}

{docstring Hex.Graph.Isomorphic}

# The Petersen graph three ways
%%%
tag := "hex-graph-iso-petersen"
%%%

The Petersen graph is the standard first nontrivial example, and the
library's family generators construct it twice: as the generalized
Petersen graph {name Hex.GraphIso.Families.gpetersen}`Families.gpetersen`
`5 2`, an outer pentagon `0..4`, an inner five-point star `5..9`
stepping by two, and spokes joining the rings; and as the Kneser graph
{name Hex.GraphIso.Families.kneser}`Families.kneser` `5 2`, whose
vertices are the two-element subsets of a five-element set in
colexicographic order, joined when disjoint. The two families are
unrelated at general parameters; that `G(5, 2)` and `K(5, 2)` are
isomorphic is a coincidence special to these values, and proving it is
the first example below. One explicit edge list shows the generalized
Petersen numbering concretely, checked against the general
construction. Neither claim mentions colours, so both are stated on
bare `Graph 10` values.

```lean
open Hex Hex.GraphIso

namespace HexGraphIsoChapterExample

def petersen : Graph 10 := Families.gpetersen 5 2

def kneser52 : Graph 10 := Families.kneser 5 2

-- The generalized Petersen numbering, concretely.
#guard Graph.ofEdges
    [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
     (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)] =
  Families.gpetersen 5 2

-- The two canonical searches compose into an explicit
-- vertex permutation between the presentations, and the
-- decision agrees.
#guard (Graph.findIso petersen kneser52).isSome
#guard Graph.isIso petersen kneser52

-- The tactic closes the positive goal through the
-- kernel-replayed transporter check.
example : Graph.Isomorphic petersen kneser52 := by graph_iso
```

The pentagonal prism, `Families.gpetersen 5 1`, is the interesting
negative companion: like the Petersen graph it has ten vertices, every
one of degree three, so degree refinement alone does not settle the
question. The fully verified pairwise decision can individualize a
vertex, re-refine, and refute every branch; the tactic normally closes
this case by replaying the smaller canonical-key certificates instead.

{docstring Hex.GraphIso.Pairwise.search}

```lean
def prism5 : Graph 10 := Families.gpetersen 5 1

example : ¬ Graph.Isomorphic petersen prism5 := by graph_iso
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
obtained from its general checked separator rather than a handwritten
special-purpose lemma. These claims do mention colours, so they are the
ones stated on {name Hex.GraphIso.Colored}`Colored`.

```lean
def markPair (a b : Fin 10) : Coloring 10 2 :=
  (Coloring.ofVector? (Hex.Vector.ofFn' fun i =>
    if i = a ∨ i = b then 0 else 1)).getD
      (Coloring.mod 10 2)

-- 0-1 is an outer pentagon edge; 2-3 likewise;
-- 0-2 is a non-edge.
def edgeMarkA : Colored 10 2 := ⟨petersen, markPair 0 1⟩
def edgeMarkB : Colored 10 2 := ⟨petersen, markPair 2 3⟩
def nonedgeMark : Colored 10 2 := ⟨petersen, markPair 0 2⟩

example : Isomorphic edgeMarkA edgeMarkB := by graph_iso
example : ¬ Isomorphic edgeMarkA nonedgeMark := by graph_iso
example : ¬ Isomorphic edgeMarkB nonedgeMark := by graph_iso

end HexGraphIsoChapterExample
```

# Latin-square isotopy as graph isomorphism
%%%
tag := "hex-graph-iso-latin-square"
%%%

The [nauty introduction](https://pallini.di.uniroma1.it/Introduction.html)
begins from a broad principle: finite objects built from finite sets and
relations can often be encoded as coloured graphs. Its Latin-square example
asks about *isotopy*: two squares are isotopic when one can be obtained from
the other by independently permuting the rows, the columns, and the symbols.

Before mentioning graphs, we can state that question directly in Lean. We
package the Latin property as bijectivity of every row and column, and define
isotopy using three independent permutations.

```lean
open Hex.GraphIso.Mathlib

namespace LatinSquareExample

structure LatinSquare where
  entry : Fin 3 → Fin 3 → Fin 3
  rows : ∀ i, Function.Bijective (entry i)
  columns : ∀ j, Function.Bijective (fun i => entry i j)

def Isotopic (L M : LatinSquare) : Prop :=
  ∃ r c s : Equiv.Perm (Fin 3),
    ∀ i j, M.entry (r i) (c j) = s (L.entry i j)
```

The introduction illustrates the construction with exactly this square:

```
1 3 2
2 1 3
3 2 1
```

The definitions below use the zero-based elements of `Fin 3`. The second
square is obtained by exchanging the first two rows and then exchanging the
symbols 1 and 2.

```lean
def nautySquare : LatinSquare where
  entry
    | 0, 0 => 0 | 0, 1 => 2 | 0, 2 => 1
    | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 2
    | 2, 0 => 2 | 2, 1 => 1 | 2, 2 => 0
  rows := by decide
  columns := by decide

def cyclicSquare : LatinSquare where
  entry i j := ⟨(i + j) % 3, by omega⟩
  rows := by decide
  columns := by decide
```

Following the nauty introduction, we make a graph with four colours of
vertices: one vertex for each row, column, symbol, and position. A position
vertex is joined to its row, its column, and the symbol written there. The
resulting graph has 18 vertices and 27 edges.

```lean
inductive Vertex
  | row : Fin 3 → Vertex
  | column : Fin 3 → Vertex
  | symbol : Fin 3 → Vertex
  | position : Fin 3 × Fin 3 → Vertex
  deriving DecidableEq, Fintype

private def incidence (L : LatinSquare)
    (x y : Vertex) : Prop :=
  match x, y with
  | .position (i, _), .row i' => i = i'
  | .position (_, j), .column j' => j = j'
  | .position (i, j), .symbol k => L.entry i j = k
  | _, _ => False

private instance (L : LatinSquare) :
    DecidableRel (incidence L) :=
  fun x y => by
    cases x <;> cases y <;>
      simp only [incidence] <;> infer_instance

private def graph (L : LatinSquare) :
    SimpleGraph Vertex :=
  SimpleGraph.fromRel (incidence L)

private def color : Vertex → Fin 4
  | .row _ => 0
  | .column _ => 1
  | .symbol _ => 2
  | .position _ => 3

def encode (L : LatinSquare) :
    Hex.GraphIso.Mathlib.Colored Vertex 4 where
  graph := graph L
  color := color
  onto := by decide

private instance (L : LatinSquare) :
    DecidableRel (encode L).graph.Adj :=
  fun x y => by
    change Decidable
      (x ≠ y ∧ (incidence L x y ∨ incidence L y x))
    infer_instance
```

It remains to justify the reduction. A colour-preserving graph isomorphism
restricts to a permutation on each of the row, column, and symbol vertices.
The three edges incident to a position vertex then force those permutations
to satisfy the isotopy equation. The generic `componentPerm` extracts all
three permutations, keeping the reflection proof itself short.

```lean
variable {L M : LatinSquare}

private def component : Fin 3 → Fin 3 → Vertex
  | 0 => Vertex.row
  | 1 => Vertex.column
  | 2 => Vertex.symbol

private def index : Vertex → Fin 3
  | .row i | .column i | .symbol i => i
  | .position _ => 0

private def componentMap
    (f : (encode L).Iso (encode M))
    (kind i : Fin 3) : Fin 3 :=
  index (f.graphIso (component kind i))

private theorem map_component
    (f : (encode L).Iso (encode M))
    (kind i : Fin 3) :
    f.graphIso (component kind i) =
      component kind (componentMap f kind i) := by
  have hc := f.map_color (component kind i)
  generalize h : f.graphIso (component kind i) = v
    at hc ⊢
  fin_cases kind <;> cases v <;>
    simp_all [component, componentMap, index,
      encode, color]

private noncomputable def componentPerm
    (f : (encode L).Iso (encode M)) (kind : Fin 3) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (componentMap f kind) <| by
    apply Function.Injective.bijective_of_finite
    intro i j h
    have hc : component kind i = component kind j := by
      apply f.graphIso.injective
      rw [map_component, map_component, h]
    fin_cases kind <;> simpa [component] using hc

private theorem map_entry
    (f : (encode L).Iso (encode M)) (i j : Fin 3) :
    M.entry (componentMap f 0 i) (componentMap f 1 j) =
      componentMap f 2 (L.entry i j) := by
  obtain ⟨p, hp⟩ : ∃ p,
      f.graphIso (Vertex.position (i, j)) =
        Vertex.position p := by
    have hc := f.map_color (Vertex.position (i, j))
    generalize h : f.graphIso (Vertex.position (i, j)) = v
      at hc
    cases v <;> simp_all [encode, color]
  have hr := f.graphIso.map_adj_iff.mpr
    (show (graph L).Adj (.position (i, j)) (.row i) by
      simp [graph, incidence])
  have hc := f.graphIso.map_adj_iff.mpr
    (show (graph L).Adj (.position (i, j)) (.column j) by
      simp [graph, incidence])
  have hs := f.graphIso.map_adj_iff.mpr
    (show (graph L).Adj
        (.position (i, j)) (.symbol (L.entry i j)) by
      simp [graph, incidence])
  rw [hp,
    show Vertex.row i = component 0 i from rfl,
    map_component] at hr
  rw [hp,
    show Vertex.column j = component 1 j from rfl,
    map_component] at hc
  rw [hp,
    show Vertex.symbol (L.entry i j) =
      component 2 (L.entry i j) from rfl,
    map_component] at hs
  simp [encode, graph, incidence, component] at hr hc hs
  simpa [hr, hc] using hs

theorem isotopic_of_isomorphic :
    (encode L).Isomorphic (encode M) → Isotopic L M := by
  rintro ⟨f⟩
  exact ⟨componentPerm f 0, componentPerm f 1,
    componentPerm f 2, map_entry f⟩
```

With that bridge established, the promised proof of a statement about Latin
squares is just the reduction followed by `graph_iso`:

```lean
example : Isotopic nautySquare cyclicSquare := by
  apply isotopic_of_isomorphic
  graph_iso

end LatinSquareExample
```

# Performance
%%%
tag := "hex-graph-iso-performance"
%%%

The Lean implementation runs the same algorithm as nauty in the
strictest sense: conformance testing pins the visited-node counters, so
both programs traverse exactly the same search tree on every
conformance case. Every timing difference is therefore a per-node
constant factor of the implementation, never an algorithmic
difference, and the one way that factor could grow with the vertex
count would be a loop over vertices where nauty runs a word
operation. The search keeps its vertex sets packed sixty-three to a
word, so a least-squares fit of per-node cost against `n` on the
benchmark corpus gives hex the same exponent as nauty on every family:
`n^1.7` to `n^1.9` on grids, Paley graphs, circulants and random
graphs, `n^1.3` on Kneser graphs and `n^1.0` on Johnson graphs, in
each case within `0.2` of nauty's, and the hex/nauty ratio is `7.9`
below 64 vertices and `7.2` above. CI refits every recorded sweep and
fails when a family's hex exponent exceeds nauty's by more than `0.2`.
The table shows the factor on four parametrised families: grids, where
refinement discretizes quickly; Paley graphs, refinement's hard case
among the sparse families; and the dense Latin-square and Kneser
graphs. The `hex` column is `canonicalize`, which carries the theorems
of this chapter as it stands: no certificate is produced or replayed
on that path.

:::table +header
* * graph
  * vertices
  * nauty (ms)
  * hex (ms)
* * `Families.grid 5 5`
  * 25
  * 0.014
  * 0.086
* * `Families.grid 15 15`
  * 225
  * 0.86
  * 3.9
* * `Families.paley 29`
  * 29
  * 0.019
  * 0.14
* * `Families.paley 229`
  * 229
  * 1.1
  * 6.9
* * `Families.latinSquare 5`
  * 25
  * 0.019
  * 0.20
* * `Families.latinSquare 13`
  * 169
  * 0.78
  * 6.6
* * `Families.kneser 7 2`
  * 21
  * 0.013
  * 0.16
* * `Families.kneser 22 2`
  * 231
  * 3.4
  * 39
:::

Measured on chungus2, 2026-09-05, minimum over repeated runs;
regenerate with `scripts/bench/graphiso_cactus_sweep.sh`. On
ten-vertex pairs like the examples of this chapter, the kernel-checked
`graph_iso` proof costs roughly 20 milliseconds on a positive goal and
0.7 to 0.9 seconds on a negative one. That price is separate from the
table and does not shrink with it: a kernel proof still replays a
certificate inside the kernel, whereas `canonicalize` runs no replay
at all. For breadth across the whole benchmark corpus, see the cactus
plots in `reports/figures/` in the repository.

# The Mathlib correspondence
%%%
tag := "hex-graph-iso-mathlib"
%%%

`HexGraphIsoMathlib` relates the executable coloured graphs to Mathlib's
{name}`SimpleGraph` and extends the same `graph_iso` syntax to closed
ground `SimpleGraph` terms. The two families below are parametrised and
deliberately have different vertex types (`Fin 2 × Fin p`, a rim/spoke
coordinate, for the generalized Petersen graph, and the two-element
subsets of `Fin 5` for the Kneser graph), so the positive goal genuinely
enumerates two unrelated finite types and returns a `SimpleGraph.Iso`,
rather than recognizing a definitional equality. `graph_iso` is a
decision procedure on closed ground instances, so the parameters must be
literals at the use site.

{docstring Hex.GraphIso.Mathlib.Colored}

{docstring Hex.GraphIso.Mathlib.encode}

{docstring Hex.GraphIso.Mathlib.colored_iso_iff_canon_eq}

```lean
open Hex.GraphIso.Mathlib

namespace HexGraphIsoMathlibChapterExample

def gpetersen (p q : Nat) :
    SimpleGraph (Fin 2 × Fin p) where
  Adj v w :=
    v ≠ w ∧
      ((v.1 = 0 ∧ w.1 = 0 ∧
          (w.2.val = (v.2.val + 1) % p ∨
            v.2.val = (w.2.val + 1) % p)) ∨
       (v.1 = 1 ∧ w.1 = 1 ∧
          (w.2.val = (v.2.val + q) % p ∨
            v.2.val = (w.2.val + q) % p)) ∨
       (v.1 ≠ w.1 ∧ v.2 = w.2))
  symm := ⟨by grind⟩
  loopless := ⟨by grind⟩

instance (p q : Nat) : DecidableRel (gpetersen p q).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def kneser (m r : Nat) :
    SimpleGraph {s : Finset (Fin m) // s.card = r} where
  Adj s t := Disjoint s.val t.val ∧ s ≠ t
  symm := ⟨by grind⟩
  loopless := ⟨by grind⟩

instance (m r : Nat) : DecidableRel (kneser m r).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

example : Nonempty (gpetersen 5 2 ≃g kneser 5 2) := by
  graph_iso

example : IsEmpty (gpetersen 5 2 ≃g gpetersen 5 1) := by
  graph_iso

end HexGraphIsoMathlibChapterExample
```

Neither proof requires an external nauty installation, and no proof
path uses `native_decide` or introduces an axiom.
