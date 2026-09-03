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
identical, and prove our theorems about the Lean translation.) The exact
algorithm, including the output-relevant choices absent from the published
literature, is specified in {ref "nauty-algorithm"}[The `nauty` canonical
labelling algorithm]. The
short names (`canonicalize`, `canon`, `label`, `isIso`) run that
translation directly and are the fast surface for users who just want
answers; the `Checked` surface (`canonicalizeChecked`, `canonChecked`,
…) additionally validates every answer through a proven certificate
checker and carries the theorems. Two coloured graphs are isomorphic
exactly when their checked canonical forms are equal
({name Hex.GraphIso.iso_iff_canonChecked_eq}`iso_iff_canonChecked_eq`),
and the
`graph_iso` tactic closes both positive and negative isomorphism goals with the
kernel performing the decisive replay: positive goals through the
checked transporter, negative goals through a fully verified
individualization-refinement decision.

The separate [`nauty-ffi`](https://github.com/leanprover/nauty-ffi) package is
available for users who want direct access to the corresponding dense-nauty
operations from Lean. It is an unverified native convenience package, not a
dependency or part of the verified `HexGraphIso` library.

{docstring Hex.GraphIso.Colored}

{docstring Hex.GraphIso.canonicalize}

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
construction.

```lean
open Hex Hex.GraphIso

namespace HexGraphIsoChapterExample

def petersen : Colored 10 1 :=
  Families.plain (Families.gpetersen 5 2)

def kneser52 : Colored 10 1 :=
  Families.plain (Families.kneser 5 2)

-- The generalized Petersen numbering, concretely.
#guard Graph.ofEdges
    [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
     (5, 7), (7, 9), (6, 9), (6, 8), (5, 8),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)] =
  Families.gpetersen 5 2

-- The two canonical searches find an explicit vertex
-- permutation between the presentations; `checkIso`
-- validates it.
#guard
  (((Nauty.canonicalize? petersen).bind fun rP =>
    (Nauty.canonicalize? kneser52).map fun rK =>
      checkIso petersen kneser52
        ((rK.label.toPerm.inv).comp rP.label.toPerm))
    == some true)

-- The tactic closes the positive goal through the
-- kernel-replayed transporter check.
example : Isomorphic petersen kneser52 := by graph_iso
```

The pentagonal prism, `Families.gpetersen 5 1`, is the interesting
negative companion: like the Petersen graph it has ten vertices, every
one of degree three, so degree refinement alone does not settle the
question. The verified pairwise decision individualizes a vertex,
re-refines, and refutes every branch; the kernel replays that run.

{docstring Hex.GraphIso.Pairwise.search}

```lean
def prism5 : Colored 10 1 :=
  Families.plain (Families.gpetersen 5 1)

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

# Performance
%%%
tag := "hex-graph-iso-performance"
%%%

The Lean implementation runs the same algorithm as nauty in the
strictest sense: conformance testing pins the visited-node counters, so
both programs traverse exactly the same search tree on every input.
Every timing difference is therefore a per-node constant factor of the
implementation, never an algorithmic difference. The table shows that
factor on four parametrised families from the benchmark corpus: grids,
where refinement discretizes quickly; Paley graphs, refinement's hard
case among the sparse families; and the dense Latin-square and Kneser
graphs, where the factor is largest. The `fast` column is
`canonicalize` and the `checked` column is `canonicalizeChecked`, which
additionally validates every answer through the certificate checker.

:::table (header := true)
* * graph
  * vertices
  * nauty (ms)
  * fast (ms)
  * checked (ms)
* * `Families.grid 5 5`
  * 25
  * 0.014
  * 0.066
  * 0.25
* * `Families.grid 15 15`
  * 225
  * 0.83
  * 14
  * 38
* * `Families.paley 29`
  * 29
  * 0.019
  * 0.097
  * 0.88
* * `Families.paley 229`
  * 229
  * 1.1
  * 29
  * 180
* * `Families.latinSquare 5`
  * 25
  * 0.019
  * 0.14
  * 0.80
* * `Families.latinSquare 13`
  * 169
  * 0.77
  * 25
  * 100
* * `Families.kneser 7 2`
  * 21
  * 0.014
  * 0.12
  * 0.70
* * `Families.kneser 22 2`
  * 231
  * 3.4
  * 210
  * 1000
:::

Measured on chungus2, 2026-09-03, minimum over repeated runs;
regenerate with `scripts/bench/graphiso_cactus_sweep.sh`. On the
ten-vertex examples of this chapter, the kernel-checked `graph_iso`
proof costs roughly 20 to 30 milliseconds on a positive goal and 0.3
to 1 seconds on a negative one. The gap between the `fast` and
`checked` columns is the current price of certificate validation; the
verified search refinement programme in the SPEC is expected to remove
it, at which point the checked guarantees attach to the fast path
itself and the `checked` column disappears. For breadth across the
whole benchmark corpus, see the cactus plots in `reports/figures/` in
the repository.

# The Mathlib bridge
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

{docstring Hex.GraphIso.Mathlib.colored_iso_iff_canonChecked_eq}

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
