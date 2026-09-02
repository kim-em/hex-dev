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

A canonical labelling algorithm takes a finite graph and renames its
vertices in a standard way, so that two graphs receive the same result
exactly when they are isomorphic. The most widely used program for this
task is Brendan McKay's nauty. This chapter is a complete written
specification of the exact function computed by one pinned version of
that program: dense nauty 2.9.3, run with the fixed options listed at
the end of part one. `HexGraphIso` reimplements this algorithm in
Lean, with identical behaviour.

No published document specifies this function. Three descriptions come
closest:

* Brendan D. McKay's [*Practical graph
  isomorphism*](https://users.cecs.anu.edu.au/~bdm/papers/pgi.pdf)
  (1981) gives pseudocode detailed enough to reimplement the algorithm
  as it stood in 1981. Later releases of nauty changed details that
  affect the output.
* Stephen G. Hartke and A. J. Radcliffe's *McKay's canonical graph
  labeling algorithm* (2009) explains the main ideas and why the
  algorithm is correct. It deliberately omits the implementation
  choices that decide which result is returned.
* Brendan D. McKay and Adolfo Piperno's [*Practical graph isomorphism,
  II*](https://arxiv.org/abs/1301.1493) (2014) and the [nauty and
  Traces User's Guide, version
  2.9.3](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf) describe a
  family of algorithms with several interchangeable components. Every
  member of the family computes some canonical form. These documents do
  not say which member the program `densenauty` is.

For the exact output, the C source code has previously been the only
specification. The source interleaves two kinds of code: choices that
determine the answer, and shortcuts that only make the program faster.
This chapter separates them. Part one describes a complete search that
examines every candidate ordering the program could ever consider, and
the rule that selects one of them. Part two
presents the Lean implementation of that description. The shortcuts in
the real program skip most of the search, and the Lean development
proves that skipping never changes the selected answer, so the
shortcuts need no place in the specification.

One distinction runs through the whole chapter. The statement "the Lean
implementation computes the maximum described in part one" is a
theorem, proved in Lean. The statement "the Lean implementation agrees
with the C program" is not a theorem about anything; it is an empirical
claim, supported by conformance tests that compare the two programs on
large families of inputs. The `HexGraphIso` library never treats the
C program as a formal object.

# Part one: the algorithm
%%%
tag := "nauty-algorithm-description"
%%%

## Coloured graphs and canonical forms

The input is a finite simple undirected graph on vertices numbered `0`
through `n - 1`, together with a colouring: every vertex has one of
the colours `0` through `k - 1`, and every colour is used at least
once. An isomorphism between two such graphs is a bijection between
their vertex sets that preserves both adjacency and colour: a vertex
of colour `2` must be sent to a vertex of colour `2`. Colours are
labels, so exchanging two colours throughout a graph generally
produces a different coloured graph, not another presentation of the
same one. The numerical order of the colours plays no part in the
notion of isomorphism. The algorithm does use it: the starting
partition below places the colour classes in colour order, and the
output keeps them in that order. This algorithmic use is what the
library's documentation means when it calls the colours ordered.

A canonical form is a function on coloured graphs with two properties:
isomorphic inputs receive equal outputs, and every output is isomorphic
to its input. Given such a function, deciding whether two graphs are
isomorphic reduces to computing both outputs and comparing them for
equality. Many different functions have these two properties, because
every consistent way of choosing one representative from each
isomorphism class gives one. This part describes the particular choice
made by dense nauty 2.9.3.

## Ordered partitions and labellings

The algorithm works with ordered partitions of the vertex set. An
ordered partition is a list of the `n` vertices cut into consecutive
blocks, called cells. Both the order of the cells and the order of the
vertices inside each cell matter. A partition is discrete when every
cell contains exactly one vertex.

A discrete partition is read as a relabelling of the graph: the vertex
listed first receives the new name `0`, the vertex listed second
receives the new name `1`, and so on. The algorithm's whole task is to
produce one discrete partition, and the relabelled graph it defines is
the canonical form.

The starting partition is built from the colouring. Its cells are the
colour classes, in colour order: first the vertices of colour `0`, then
the vertices of colour `1`, and so on. Inside each cell the vertices
are listed in increasing numerical order.

## Equitable refinement

For a vertex `v` and a set `S` of vertices, the count of `v` into `S`
is the number of neighbours of `v` that lie in `S`. An ordered
partition is equitable when, for every pair of cells `C` and `D`, all
vertices of `C` have the same count into `D`. In an inequitable partition,
two vertices with different counts into some cell can never be
exchanged by an isomorphism that respects the partition, so separating
them into different cells discards no isomorphism.

Refinement makes a partition equitable by repeatedly splitting cells.
The procedure keeps two pieces of bookkeeping. The first is a set of
cell positions called the active set: a cell is active while it is
still waiting to be used for splitting. At the start of refinement the
active set is prescribed by the caller; at the root of the search every
cell of the starting partition is active. The second is a single
position called the preferred position, initially `0`. Both influence
the order of events, and the order of events influences the output, so
the rules below are part of the specification.

Refinement proceeds in passes. Each pass chooses one active cell,
called the splitter, as follows: if the preferred position is the start
of an active cell, that cell is the splitter; otherwise the active cell
starting soonest after the preferred position is the splitter;
otherwise the earliest active cell is the splitter. The splitter is
removed from the active set, and every cell of the partition is then
processed against it, in partition order. The list of cells to process
is fixed at the start of the pass: when a cell splits during the pass,
its fragments are not processed again within the same pass. Cells with
a single vertex are skipped. Passes repeat until the partition is
discrete or the active set is empty. A partition produced by exhausting
the active set in this way is equitable.

How a cell is processed depends on the size of the splitter.

*Splitter with two or more vertices.* Record the splitter's vertex
set. To process a cell, compute the count of each of its vertices into
that set. If all the counts are equal, the cell does not split. If not,
the cell is rearranged into groups by count, in increasing count order,
and the order of vertices within each group is preserved. Each group
becomes a cell. The new cells are then made active or not:

* If the original cell was active, all of the new cells are active.
* If it was not, all of the new cells are active except the largest
  one; when several are equally largest, the one left inactive is the
  first of them, that is, the equally largest group with the smallest
  count.

Finally, every group other than the first that consists of a single
vertex sets the preferred position to its own position. When several
groups do this, the last of them, the one with the largest count, is
the one whose setting remains.

*Splitter with one vertex.* The single vertex's neighbours are
recorded. To process a cell, walk through it with a pointer at each
end. If the leftmost unexamined vertex is a neighbour of the splitter
vertex, move the left pointer one step right. If it is not, exchange it
with the vertex at the right pointer and move the right pointer one
step left, leaving the left pointer in place. When the pointers cross,
the cell has been rearranged into the neighbours, on the left and in
their original order, followed by the non-neighbours, on the right and
in reversed order. This reversal is deliberate and is part of the
specification; it is not the stable arrangement used for larger
splitters. If either part is empty the cell does not split. Otherwise
the two parts become cells, and:

* If the original cell was active, both parts are active.
* If it was not, the smaller part becomes active; when the parts have
  equal sizes, the non-neighbour part becomes active. Note that this
  disagrees with the tie rule for larger splitters, under which the
  earlier part would have kept its inactive status.

If the part just made active consists of a single vertex, the preferred
position is set to its position.

## The refinement code

Each run of the refinement procedure also produces a number between `0`
and `32766`, called its refinement code. The code is a number summarizing
the splitting events, in order. Comparing codes is how the algorithm
compares two runs of refinement without comparing the partitions
themselves.

The code is produced by an accumulator. To update the accumulator with
a number `i`: take the exclusive or of the accumulator with `27421`,
add `i`, and reduce modulo `32768`. (In the C source the two constants
are written in octal, as `065435` and `077777`, and the reduction is a
bitwise and.) The accumulator starts at the number of cells the
partition has when refinement begins, and is updated as follows.
Positions are counted from `0`.

* When a splitter is chosen, update with the sum of the first and last
  positions of the splitter. If the splitter has two or more vertices,
  update again with its size.
* When a cell is processed against a splitter with two or more
  vertices and all counts are equal: update with that common count plus
  the cell's starting position. This applies whether or not any other
  cell splits.
* When such a cell instead splits into groups: for each group, in
  increasing count order, update with the group's count plus the
  group's starting position.
* When a cell splits against a one-vertex splitter: update with the
  last position of the neighbour part. A cell that does not split
  against a one-vertex splitter contributes nothing.
* When refinement finishes, update with the final number of cells, and
  then reduce the accumulator modulo `32767`.

The final reduction is modulo `32767`, one less than the modulus used
inside the updates, so every finished code is at most `32766`. The
value `32767` therefore never occurs as a code; it is reserved for use
as a marker in the comparison of leaves, described below.

## A worked example

Take the path with six vertices and edges `0-1`, `1-2`, `2-3`, `3-4`,
`4-5`, with all vertices the same colour. The starting partition is the
single cell `0 1 2 3 4 5`, which is active, and the preferred position
is `0`.

1. The only active cell is the splitter. Vertices `0` and `5` have one
   neighbour in it; vertices `1`, `2`, `3`, `4` have two. Increasing
   count order gives `0 5 | 1 2 3 4`. The cell had already been removed
   from the active set when it became the splitter, so the exemption
   rule applies: the larger fragment `1 2 3 4` is exempt, and the
   fragment `0 5` at position `0` is active. No new cell is a single
   vertex, so the preferred position stays `0`.
2. Position `0` starts the active cell `0 5`, so it is the splitter.
   Vertices `2` and `3` have no neighbour in it; vertices `1` and `4`
   have one. The cell `1 2 3 4` therefore splits as `2 3 | 1 4`, giving
   the partition `0 5 | 2 3 | 1 4`. The cell `0 5` does not split: both
   of its vertices have count `0` into the splitter, which is the cell
   itself.
3. The two fragments have equal size, so the exemption goes to the
   first, `2 3`, and the fragment `1 4` becomes active. Using `1 4` as
   the final splitter splits nothing.

The partition `0 5 | 2 3 | 1 4` is equitable: within each cell, both
vertices have the same count into each of the three cells. It is not
discrete. Reflecting the path exchanges the two vertices in every cell,
so no refinement argument can separate them; making further progress
requires the search of the next section. Carrying the accumulator
through these events produces the refinement code `27540`; part two
recomputes both the partitions and this value from the implementation.

## The search tree

When the equitable partition is not discrete, the algorithm picks one
cell, called the target cell, and tries each of its vertices in turn as
a forced singleton. Each trial is one child node in a search tree.

The target cell is chosen from the cells with two or more vertices. Say
that two such cells `C` and `D` are linked when the vertices of `C`
have at least one neighbour and at least one non-neighbour in `D`.
(Because the partition is equitable, either every vertex of `C` has
this property or none does, and cells `C` and `D` are linked exactly
when `D` and `C` are.) The target cell is the cell linked to the
greatest number of other cells with two or more vertices; when several
cells are tied, the earliest of them in partition order is chosen. This
rule is used at every node of depth at most `100`, where the root has
depth `1`; at greater depths the target cell is simply the earliest
cell with two or more vertices. The depth `100` at which the rule
changes is one of the pinned options, and for graphs of ordinary size
only the first rule ever applies.

A child is created for each vertex of the target cell, in the order the
vertices are listed in the cell. To create the child for vertex `v`:
move `v` to the front of the target cell, shifting the vertices that
preceded it one place right and leaving their relative order unchanged;
cut the cell just after `v`, so that `v` becomes a cell by itself; make
that new singleton cell the only active cell; and run refinement again.
The child's refinement starts with the preferred position `0` and
produces its own refinement code.

Each node of the tree therefore has one refinement code. A node
whose refined partition is discrete is a leaf. Refinement strictly
increases the number of cells along any branch, so every branch reaches
a leaf and the tree is finite.

## Leaf keys and the selected leaf

Every leaf is assigned a key with two components. The first component
is the list of refinement codes along the path from the root to the
leaf, one per node, with the number `32767` appended at the end. The
second component is the adjacency matrix of the graph relabelled by the
leaf's discrete partition, taken as the list of its `n` rows: row `i`
lists which new vertices are adjacent to new vertex `i`.

Keys are compared as follows. First compare the code lists, position by
position, as ordinary integers; the first position where they differ
decides. The appended `32767` exceeds every real code, so if two paths
have identical codes for their entire common length and one of them
ends at a leaf there, the shorter path compares greater at the first
position where the longer path has a real code: a shallower leaf is
preferred. If the code lists are identical, compare the row
lists: find the first row where the two differ, then find the smallest
new vertex on which those two rows disagree; the row in which that
vertex is an adjacent vertex is the greater.

The algorithm's result is the leaf with the greatest key. When several
leaves share the greatest key, the result is the first of them, in the
order the tree is generated: children are visited in the order they
were created. The relabelled graph of this leaf is the canonical form,
and its discrete partition is the canonical labelling. In the output,
the vertices of colour `0` are the new vertices `0` up to the size of
that colour class, followed contiguously by the vertices of colour `1`,
and so on; this holds because refinement only ever splits cells in
place, so each colour class of the starting partition remains a
consecutive range of new names.

Isomorphic inputs produce the same canonical form. An isomorphism
matches the nodes of the two search trees, matched nodes carry equal
refinement codes, and matched leaves carry equal relabelled adjacency
matrices, so the two trees have the same set of keys. The canonical
labellings themselves are in general different: each is a renaming of
its own input's vertices.

## Pruning

The description above generates the complete tree. The real program
generates only a small part of it, using the observations below, and
this is the entire difference between them. The Lean development proves
that each observation preserves both the selected canonical form and
the selected labelling, which is why none of them appears in the
specification.

* Codes are compared during descent. If the code list along the current
  path is already less than the corresponding prefix of the best key
  found so far, no leaf below the current node can be selected, and the
  subtree is skipped. In one situation inside a subtree that this
  comparison has already ruled out, the program also reuses a stored
  target cell instead of evaluating the target-cell rule; since no leaf
  of such a subtree can be selected, this shortcut also cannot change
  the answer.
* When two leaves yield the same relabelled graph, composing one
  labelling with the inverse of the other gives an automorphism of the
  input. The program collects these automorphisms.
* If two vertices of the target cell are related by collected
  automorphisms that fix all vertices individualized so far, their two
  subtrees contain the same keys, and the later subtree is skipped.
* Two further rules of the same character, called short pruning and
  long pruning in the source, skip target-cell vertices using the
  cycles of the collected automorphisms.

The checked implementation records, for every skipped subtree, the
evidence justifying the skip, and replays that evidence through a
proven checker. The certificate format and the checker belong to the
{ref "hex-graph-iso"}[HexGraphIso chapter].

## Exact scope

This chapter specifies dense nauty 2.9.3 on 64-bit machine words. The
dense representation stores each adjacency row in the number of 64-bit
words needed for `n` bits. The pinned call supplies the ordered colour
partition and pins the following options, several of which restate
their default values:

| option | value |
| --- | --- |
| `getcanon` (request a canonical graph and labelling) | `1` |
| `digraph` (treat the graph as directed) | `FALSE` |
| `defaultptn` (ignore the supplied partition) | `FALSE` |
| `writeautoms`, `writemarkers` (print during the run) | `FALSE` |
| `tc_level` (changeover depth for the target-cell rule) | `100` |
| `userrefproc` and all other user callbacks | `NULL` |
| `invarproc` (extra vertex invariant) | `NULL` |
| `mininvarlevel`, `maxinvarlevel`, `invararg` | `0`, `1`, `0` |
| `schreier` (use the Schreier-Sims machinery) | `FALSE` |

Sparse nauty and Traces are different algorithms and can return
different canonical forms for the same input. Without naming the dense
algorithm, the version, the word size, and the options, the phrase
"nauty's canonical form" does not identify a single function.

# Part two: the Lean implementation
%%%
tag := "nauty-algorithm-lean"
%%%

The Lean implementation follows part one section by section. A graph is
stored as one natural number per vertex, used as a bitset: bit `v` of
row `u` is set exactly when `u` and `v` are adjacent. The row
comparison of part one is implemented directly on these bitsets. It is
not the numerical order on the natural numbers: in the numerical order
the largest vertex would be the most significant, while in the
comparison of part one the smallest vertex is the most significant.

## Refinement

The accumulator update is {name Hex.GraphIso.Nauty.mash}`mash`; its
definition contains the two octal constants of part one.

{docstring Hex.GraphIso.Nauty.mash}

One pass, from choosing the splitter through processing every cell, is
{name Hex.GraphIso.Nauty.refineStep}`refineStep`. Complete refinement,
which repeats passes and finishes the code, is
{name Hex.GraphIso.Nauty.refine}`refine`.

{docstring Hex.GraphIso.Nauty.refineStep}

{docstring Hex.GraphIso.Nauty.refine}

The worked example of part one, recomputed by the implementation:

```lean (name := refineTrace)
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

private def trace : List (List (List Nat)) :=
  [blocks initialState,
   blocks firstSplit,
   blocks secondSplit]

#eval trace

#guard trace =
  [[[0, 1, 2, 3, 4, 5]],
   [[0, 5], [1, 2, 3, 4]],
   [[0, 5], [2, 3], [1, 4]]]

#guard (refine pathCtx 1 #[0, 1, 2, 3, 4, 5]
    (initPtn 6 8 [5]) (initActive [5]) 1).longcode = 27540

end NautyAlgorithmChapterExample
```
```leanOutput refineTrace
[[[0, 1, 2, 3, 4, 5]], [[0, 5], [1, 2, 3, 4]], [[0, 5], [2, 3], [1, 4]]]
```

The first guard pins the three partitions displayed in part one, and
the second pins the refinement code `27540` claimed there.

## The target cell and the tree

The production target-cell rule is
{name Hex.GraphIso.Nauty.bestcell}`bestcell`, selected by
{name Hex.GraphIso.Nauty.targetcell}`targetcell` according to the
depth. The production rule tests linkage using one representative
vertex per cell; the specification tests it using the counts of every
vertex, which is the same test on equitable partitions and is
independent of vertex order.

{docstring Hex.GraphIso.Nauty.bestcell}

{docstring Hex.GraphIso.Nauty.targetcell}

The complete tree of part one is generated by
{name Hex.GraphIso.Nauty.specNode}`specNode`: refine, stop at a
discrete partition, or create the children of the target cell and take
the greatest of their keys.

{docstring Hex.GraphIso.Nauty.specNode}

## Keys and the declarative canonical form

The two components of a leaf key are the fields of
{name Hex.GraphIso.Nauty.Key}`Key`, compared by
{name Hex.GraphIso.Nauty.keyCmp}`keyCmp`. The appended marker is
{name Hex.GraphIso.Nauty.codeSentinel}`codeSentinel`.

{docstring Hex.GraphIso.Nauty.Key}

{docstring Hex.GraphIso.Nauty.keyCmp}

{docstring Hex.GraphIso.Nauty.codeSentinel}

The greatest key of the whole tree is
{name Hex.GraphIso.Nauty.canonSpecKey}`canonSpecKey`, and
{name Hex.GraphIso.Nauty.specCanon}`specCanon` turns it into the
canonical coloured graph, with the colour classes laid out contiguously
in colour order.

{docstring Hex.GraphIso.Nauty.canonSpecKey}

{docstring Hex.GraphIso.Nauty.specCanon}

For the six-vertex path, the whole computation gives:

```lean (name := pathKey)
#eval canonSpecKey NautyAlgorithmChapterExample.pathSix
```
```leanOutput pathKey
{ codes := [27540, 56, 32767], rows := [16, 32, 24, 36, 5, 10] }
```

The code list records the root refinement code `27540` from the worked
example, the code `56` of the selected leaf's second refinement, and
the marker. The rows are the relabelled adjacency bitsets: row `0` is
`16`, that is, bit `4`, so new vertex `0` is adjacent exactly to new
vertex `4`.

## The production search

The pruned search compares leaves with
{name Hex.GraphIso.Nauty.testcanlab}`testcanlab` and installs a new
best leaf with {name Hex.GraphIso.Nauty.updatecan}`updatecan`, which
reuses the rows already known to be equal.

{docstring Hex.GraphIso.Nauty.testcanlab}

{docstring Hex.GraphIso.Nauty.updatecan}

The transcribed search is exposed as
{name Hex.GraphIso.Nauty.canonicalize?}`Hex.GraphIso.Nauty.canonicalize?`.
The public entry point is
{name Hex.GraphIso.canonicalize}`Hex.GraphIso.canonicalize`; the
{ref "hex-graph-iso"}[HexGraphIso chapter] describes the public
surface, including the certificate-checked tier that carries the
theorems.

{docstring Hex.GraphIso.Nauty.canonicalize?}

{docstring Hex.GraphIso.canonicalize}

## What the Lean proofs establish

The three theorems below state that the declarative form is isomorphic
to its input, is invariant under isomorphism, and decides isomorphism
by equality.

{docstring Hex.GraphIso.Nauty.specCanon_iso}

{docstring Hex.GraphIso.Nauty.specCanon_invariant}

{docstring Hex.GraphIso.Nauty.iso_iff_specCanon_eq}

The certificate checker connects the pruned search to the
specification: {name Hex.GraphIso.Nauty.checkKey_sound}`checkKey_sound`
identifies an accepted key with
{name Hex.GraphIso.Nauty.canonSpecKey}`canonSpecKey`, and
{name Hex.GraphIso.Nauty.checkCanon_form}`checkCanon_form` identifies
an accepted result with {name Hex.GraphIso.Nauty.specCanon}`specCanon`.

{docstring Hex.GraphIso.Nauty.checkCanon_form}

All of these theorems are about the Lean definitions. The evidence that
those definitions agree with dense nauty 2.9.3, splitter order, codes,
target cells, row order, and label tie-breaking included, is the
conformance suite, which compares the two programs on every graph with
up to six vertices and on the families described in the `HexGraphIso`
conformance documentation.

# References
%%%
tag := "nauty-algorithm-references"
%%%

* Brendan D. McKay, [*Practical graph
  isomorphism*](https://users.cecs.anu.edu.au/~bdm/papers/pgi.pdf),
  *Congressus Numerantium* 30 (1981), 45-87.
* Stephen G. Hartke and A. J. Radcliffe, *McKay's canonical graph
  labeling algorithm*, in *Communicating Mathematics*, Contemporary
  Mathematics 479, American Mathematical Society (2009), 99-111.
* Brendan D. McKay and Adolfo Piperno, [*Practical graph isomorphism,
  II*](https://arxiv.org/abs/1301.1493), *Journal of Symbolic
  Computation* 60 (2014), 94-112.
* Brendan D. McKay and Adolfo Piperno, [*nauty and Traces User's Guide,
  version 2.9.3*](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf).
