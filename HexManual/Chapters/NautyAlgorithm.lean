/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGraphIso

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxRecDepth 400000

#doc (Manual) "The `nauty` canonical labelling algorithm" =>
%%%
tag := "nauty-algorithm"
%%%

# Introduction

No published document specifies the exact canonical form returned by dense
nauty 2.9.3. Four sources come closest:

* Brendan D. McKay's [*Practical graph
  isomorphism*](https://users.cecs.anu.edu.au/~bdm/papers/pgi.pdf) gives
  pseudocode detailed enough to reimplement the 1981 algorithm. Later nauty
  releases changed choices that affect the output.
* Stephen G. Hartke and A. J. Radcliffe's [*McKay's Canonical Graph Labeling
  Algorithm*](https://www.math.unl.edu/~aradcliffe1/Papers/Canonical.pdf)
  explains the search tree, refinement, and the justification for pruning.
  It deliberately omits the implementation choices that decide which leaf
  wins.
* Brendan D. McKay and Adolfo Piperno's [*Practical graph isomorphism,
  II*](https://arxiv.org/abs/1301.1493) and the [nauty and Traces User's Guide,
  version 2.9.3](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf) describe a
  framework parameterized by refinement, target-cell selection, and node
  invariants. They do not select the particular instance returned by
  `densenauty`.

For exact output, the C source is the specification. It mixes choices that
determine the answer with pruning and storage choices that only affect running
time. This chapter separates them. The answer is the first maximal leaf of an
unpruned individualization-refinement tree. Its order is determined by the
refinement-code chain and the relabelled adjacency matrix. The production
search may omit a subtree only when its checked evidence shows that the
omission cannot change that leaf.

The status of the two comparisons is different. The Lean theorems below prove
that the checked implementation computes the declarative maximum described in
this chapter. Conformance tests establish that the Lean translation agrees with
dense nauty 2.9.3 under the pinned configuration. That second statement is an
empirical claim, not a theorem about the C program.

# Part one: the algorithm
%%%
tag := "nauty-algorithm-description"
%%%

## Coloured graphs and canonical forms

The input is a finite simple undirected graph together with an ordered vertex
colouring. An isomorphism must carry colour zero to colour zero, colour one to
colour one, and so on. The order of the colour classes is therefore part of the
input, even though the order of vertices within a class is not.

A canonical form assigns a labelled graph to each input so that isomorphic
inputs have equal outputs and every output is isomorphic to its input. Two
graphs are isomorphic exactly when their canonical forms are equal. There are
infinitely many rules satisfying these conditions because one may choose many
different orders on labelled graphs. The rest of this part specifies the
particular order used by dense nauty 2.9.3.

The algorithm represents an ordered partition by a vertex list cut into
consecutive cells. The list gives old vertex names in new-position order. At a
discrete partition, whose cells are all singletons, position zero receives the
first listed old vertex, position one receives the second, and so on. This list
is the resulting label.

## Equitable refinement

For cells (C) and (S), refine (C) by grouping its vertices according to
the number of neighbours they have in (S). A partition is equitable when, for
every ordered pair of cells, all vertices of the first cell have the same
number of neighbours in the second. Neighbour counts are preserved by graph
isomorphisms, so refinement commutes with every colour-preserving renaming of
the vertices.

Refinement maintains a set of active splitter cells, initially all the colour
cells. It repeatedly removes an active cell, uses it to split every
nonsingleton cell, and adds the necessary new splitters. The process stops when
the partition is discrete or no active cell remains. In the latter case the
partition is the equitable fixed point. The precise splitter order and the
ordering of new fragments are specified below because both affect the
canonical form.

### A six-vertex example

Take the path with edges 01, 12, 23, 34, and 45, starting from one colour cell:

1. The initial ordered partition is ((0,1,2,3,4,5)).
2. Use the whole cell as splitter. Vertices 0 and 5 have one neighbour in it,
   while 1, 2, 3, and 4 have two. Increasing count order gives
   ((0,5\mid1,2,3,4)). The larger fragment is the first largest fragment
   omitted from the active set, so the next splitter is ((0,5)).
3. Vertices 2 and 3 have no neighbour in ((0,5)), while 1 and 4 have one.
   Refinement gives ((0,5\mid2,3\mid1,4)).

This is equitable. The two vertices in each cell have the same neighbour count
into each of the three cells. Reflection of the path exchanges the two members
of every cell, so equitable refinement cannot separate them.

## The individualization-refinement tree

Each node first refines its partition to the equitable fixed point. If the
result is discrete, the node is a leaf. Otherwise the algorithm chooses a
target cell and creates one child for each vertex in that cell, in current cell
order. A child moves its chosen vertex to the first position of the target
cell, shifts the displaced prefix one position to the right, cuts the chosen
vertex off as a singleton, makes that singleton the sole active cell, and
refines again. Thus every root-to-leaf path alternates individualization and
equitable refinement. Every leaf supplies a relabelling of the original graph.

## Leaf keys and the selected leaf

A leaf key has two parts. The first is the sequence of refinement codes along
its root-to-leaf path, followed by the sentinel 32767. The second is the
adjacency matrix after applying the leaf's label.

Keys are compared lexicographically. Code sequences are compared first by the
usual integer order. If they are equal, adjacency rows are compared in new
vertex order. The sentinel is greater than every real code. Consequently, if
two paths have an equal code prefix and one reaches a leaf there, that
shallower leaf is greater than a path having another real code at the same
position.

The selected leaf is the first leaf with maximal key in the left-to-right tree
order. Its relabelled graph is the canonical form and its vertex list is the
canonical label. Isomorphic inputs have isomorphic refinement trees with the
same code chains and the same set of relabelled adjacency matrices, so their
maximal forms agree.

## Output-relevant choices

The preceding construction becomes one particular canonical labelling only
after the following choices are fixed.

### Refinement codes and splitter order

Every refinement produces a nonnegative integer below 32767. Start the
accumulator at the current number of cells. For a splitter occupying positions
(a) through (b), first mix in (a+b). For a nonsingleton splitter, also mix
in its size. Then inspect every nonsingleton cell in partition order. If all its
neighbour counts are the same value (d) and the cell begins at position
(c), mix in (d+c). If it splits, visit the nonempty count groups in
increasing count order and, for a group of count (d) beginning at its new
position (p), mix in (d+p). For a singleton splitter, mix in the last
position of the left fragment whenever its two-pointer pass splits a cell.
After all active splitters have been processed, mix in the final number of
cells and reduce modulo 32767.

The mixing operation is nauty's MASH arithmetic. In C notation it replaces
(l) by (((l) XOR 065435₈) + (i)) AND 077777₈. The mask 077777₈ is
32767. The final reduction makes every real refinement code at most 32766.

Initially every colour cell is active, and the preferred active position is
zero. At each round, use the preferred position if it starts an active cell.
Otherwise use the first active cell after that position, wrapping to the first
active cell if necessary. Remove the chosen cell from the active set and use it
to split every nonsingleton cell.

For a splitter containing at least two vertices, write neighbour-count groups
in increasing count order and preserve the previous vertex order within each
group. If an active cell splits, keep all its fragments active. If an inactive
cell splits, make every fragment except the first largest fragment active;
resolve ties for largest by count order. A newly created singleton fragment
becomes the preferred active position.

A singleton splitter uses a specialized two-pointer loop. For each
nonsingleton cell, scan from the left. Advance past a neighbour of the splitter
vertex. On a non-neighbour, swap the current vertex with the rightmost
unclassified vertex and move the right pointer left without advancing the left
pointer. The final boundary separates neighbours on the left from
non-neighbours on the right. Apply the same active-fragment rule. This is not
the stable counting redistribution used for a larger splitter.

### Target cells

Up to and including search level 100, consider only nonsingleton cells. For
each such cell, count the other nonsingleton cells to which it is nontrivially
joined: some but not all vertices of the other cell are adjacent to a
representative vertex. Equitability makes this test independent of the
representative. The first cell with the greatest count wins. Above level 100,
the first nonsingleton cell wins. The production search sometimes accepts a
stored target-cell hint, but only in a subtree already dominated by the current
best code chain. Hints therefore do not occur in the unpruned specification and
cannot change its maximal leaf.

### Adjacency row order

Compare adjacency rows in new vertex order. Within a row, vertex zero is the
most significant bit: at the least vertex where two rows differ, the row
containing that vertex is greater. This is the unsigned dense-setword order
used by nauty, extended row by row.

## Pruning

The production search avoids constructing the whole tree, but pruning does not
change the function just specified.

* First-path and best-path comparison tracks refinement codes by level. Once a
  node's chain is smaller at the first differing level, no descendant can win
  the lexicographic comparison.
* When two terminal labels give the same graph, their composite is an
  automorphism. The search records such automorphisms and uses them to identify
  target-cell branches with equal descendant keys.
* Orbit pruning explores one target-cell representative from each orbit of the
  automorphisms that fix the already individualized vertices. Every omitted
  branch is the image of a retained branch.
* Long pruning intersects a target cell with the least cycle representatives
  of stored automorphisms that fix the current fixed vertices. Short pruning
  performs the corresponding intersection for the most recently discovered
  automorphism when the search backtracks.

The checked search records the justification for code and automorphism prunes.
Its proof reconstructs the maximum of the omitted and retained children and
also checks that the reported label realizes that key. These arguments prove
that the prunings preserve the selected form and label; the pruning data are
not part of the definition of the canonical form.

## Exact scope

This chapter specifies dense nauty 2.9.3 on 64-bit setwords. The dense row count
is the number of 64-bit words needed for the vertex count. The call starts from
the graph defaults and changes only the following options:

| option | value |
| --- | --- |
| request a canonical graph | yes |
| directed graph | no |
| use the default partition | no |
| write automorphisms or markers | no |
| target-cell level | 100 |
| user refinement and other user callbacks | none |
| vertex invariant procedure | none |
| minimum invariant level, maximum invariant level, invariant argument | 0, 1, 0 |
| graph representation | dense undirected graph operations |
| Schreier refinement | no |

The initial vertex list is ordered first by colour and then by original vertex
number. Cell boundaries occur at the ends of the colour classes, and every
initial cell is active. No vertex invariant runs.
Sparse nauty and Traces use different searches and can return different
canonical forms. Without the dense algorithm, version, word order, and option
block, “nauty's canonical form” does not name one function.

# Part two: the Lean implementation
%%%
tag := "nauty-algorithm-lean"
%%%

The Lean implementation follows the order above. The graph context stores one
natural-number bitset per adjacency row, with bit (v) representing vertex
(v). Its row comparison reproduces the dense setword order rather than the
ordinary order on natural numbers.

## Ordered partitions and equitable refinement

A single active-cell round is
{name Hex.GraphIso.Nauty.refineStep}`refineStep`. The complete
{name Hex.GraphIso.Nauty.refine}`refine` operation repeats those rounds and
performs the final cleanup.

{docstring Hex.GraphIso.Nauty.refineStep}

{docstring Hex.GraphIso.Nauty.refine}

The six-vertex trace from part one is evaluated below.

```lean
open Hex Hex.GraphIso Hex.GraphIso.Nauty

namespace NautyAlgorithmChapterExample

private def pathSix : Colored 6 1 :=
  { graph := Graph.ofEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]
    coloring := Coloring.trivial 6 }

private def pathCtx : Ctx := { n := 6, g := rowsOf pathSix }

private def initialState : RefineSt :=
  { lab := #[0, 1, 2, 3, 4, 5]
    ptn := initPtn 6 8 [5]
    active := initActive [5]
    numcells := 1
    hint := 0
    maxpos := 0
    longcode := 1 }

private def blocks (st : RefineSt) : List (List Nat) :=
  (cells st.ptn 1 6).map fun (lo, hi) =>
    (List.range (hi + 1 - lo)).map fun i => st.lab[lo + i]!

private def firstSplit : RefineSt :=
  refineStep pathCtx 1 0 initialState

private def secondSplit : RefineSt :=
  refineStep pathCtx 1 firstSplit.hint firstSplit

private def refinementTrace : List (List (List Nat)) :=
  [blocks initialState,
   blocks firstSplit,
   blocks secondSplit]

#eval refinementTrace

#guard refinementTrace =
  [[[0, 1, 2, 3, 4, 5]],
   [[0, 5], [1, 2, 3, 4]],
   [[0, 5], [2, 3], [1, 4]]]

end NautyAlgorithmChapterExample
```

## The individualization-refinement tree

The unpruned recursion is {name Hex.GraphIso.Nauty.specNode}`specNode`.
It refines, returns a key at a discrete node, or individualizes every member of
the selected target cell and takes the maximum of the child keys.

{docstring Hex.GraphIso.Nauty.specNode}

## Keys and the declarative canonical form

The two parts of a leaf key are fields of {name Hex.GraphIso.Nauty.Key}`Key`.
The comparison {name Hex.GraphIso.Nauty.keyCmp}`keyCmp` puts the code list
before the adjacency rows. The value
{name Hex.GraphIso.Nauty.codeSentinel}`codeSentinel` is the octal sentinel from
part one.

{docstring Hex.GraphIso.Nauty.Key}

{docstring Hex.GraphIso.Nauty.keyCmp}

{docstring Hex.GraphIso.Nauty.codeSentinel}

For a coloured graph, {name Hex.GraphIso.Nauty.canonSpecKey}`canonSpecKey`
starts the unpruned tree from the ordered colour partition.
{name Hex.GraphIso.Nauty.specCanon}`specCanon` reads the adjacency rows of its
maximal key and restores the colour classes contiguously in their original
order.

{docstring Hex.GraphIso.Nauty.canonSpecKey}

{docstring Hex.GraphIso.Nauty.specCanon}

## Output-relevant implementation choices

The refinement accumulator is {name Hex.GraphIso.Nauty.mash}`mash`. Its
definition contains the two octal constants from part one.

{docstring Hex.GraphIso.Nauty.mash}

The production target-cell functions are
{name Hex.GraphIso.Nauty.bestcell}`bestcell` and
{name Hex.GraphIso.Nauty.targetcell}`targetcell`. The declarative tree uses the
same best-cell score without the production-only dominated-path hint.

{docstring Hex.GraphIso.Nauty.bestcell}

{docstring Hex.GraphIso.Nauty.targetcell}

At a production leaf, {name Hex.GraphIso.Nauty.testcanlab}`testcanlab`
compares the candidate relabelled rows with the current canonical rows.
{name Hex.GraphIso.Nauty.updatecan}`updatecan` stores a new best candidate,
reusing the known equal row prefix.

{docstring Hex.GraphIso.Nauty.testcanlab}

{docstring Hex.GraphIso.Nauty.updatecan}

## Production entry points

The transcribed search is exposed as
{name Hex.GraphIso.Nauty.canonicalize?}`Hex.GraphIso.Nauty.canonicalize?`.
The public fast entry point is
{name Hex.GraphIso.canonicalize}`Hex.GraphIso.canonicalize`; it returns the
canonical form together with the label.

{docstring Hex.GraphIso.Nauty.canonicalize?}

{docstring Hex.GraphIso.canonicalize}

## What the Lean proofs establish

The three main theorems state that the declarative form is isomorphic to its
input, is invariant under isomorphism, and decides isomorphism by equality.

{docstring Hex.GraphIso.Nauty.specCanon_iso}

{docstring Hex.GraphIso.Nauty.specCanon_invariant}

{docstring Hex.GraphIso.Nauty.iso_iff_specCanon_eq}

Theorem {name Hex.GraphIso.Nauty.checkCanon_form}`checkCanon_form` states that
an accepted result has the declarative canonical form. The certificate and
replay interfaces are described in {ref "hex-graph-iso"}`HexGraphIso`.

{docstring Hex.GraphIso.Nauty.checkCanon_form}

These theorems concern the Lean definitions. The external conformance suite is
the evidence that the transcribed splitter order, codes, target-cell rule, row
order, pruning behavior, and label tie-breaking agree with dense nauty 2.9.3.
No theorem in this chapter treats the external C implementation as a formal
object.

# References
%%%
tag := "nauty-algorithm-references"
%%%

* Brendan D. McKay, [*Practical graph
  isomorphism*](https://users.cecs.anu.edu.au/~bdm/papers/pgi.pdf),
  *Congressus Numerantium* 30 (1981), 45-87.
* Stephen G. Hartke and A. J. Radcliffe, [*McKay's Canonical Graph Labeling
  Algorithm*](https://www.math.unl.edu/~aradcliffe1/Papers/Canonical.pdf), in
  *Communicating Mathematics*, Contemporary Mathematics 479, American
  Mathematical Society (2009), 99-111.
* Brendan D. McKay and Adolfo Piperno, [*Practical graph isomorphism,
  II*](https://arxiv.org/abs/1301.1493), *Journal of Symbolic Computation* 60
  (2014), 94-112.
* Brendan D. McKay and Adolfo Piperno, [*nauty and Traces User's Guide, version
  2.9.3*](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf).
