# hex-graph-iso-mathlib (`SimpleGraph` correspondence and `graph_iso`)

`hex-graph-iso-mathlib` relates the executable coloured graphs from
[hex-graph-iso](../../HexGraphIso/SPEC/hex-graph-iso.md) to Mathlib's `SimpleGraph`. It provides
Mathlib-facing isomorphism theorems and extends the same `graph_iso` syntax to
closed `SimpleGraph` terms. It depends on Mathlib and `hex-graph-iso`.

The first release owns the small amount of general `SimpleGraph` conversion
it needs. There is no dependency on an unspecified `hex-graph-mathlib`
library. If several graph algorithms later need the same correspondence, that
code may be extracted without changing the surface in this SPEC.

The canonical-form algorithm, search state, certificates, and external
conformance tests remain in the Mathlib-free library. This library contains
only conversion, mathematical correspondence, reification, and tactic code.

## Scope

The first release supports:

- finite simple undirected Mathlib graphs;
- uncoloured graphs and ordered surjective vertex colours;
- graphs whose source and target vertex types differ;
- positive isomorphism goals and negative non-isomorphism goals;
- automorphism generators, vertex orbits and the group order, decoded to
  colour-preserving self-isomorphisms;
- closed ground terms whose finite enumeration and adjacency decisions can be
  checked by kernel reduction.

It does not attempt symbolic graph isomorphism, infer hypotheses about an open
adjacency relation, support infinite vertex types, or canonicalize directed
graphs and multigraphs. It does not use Mathlib's proper-colouring predicate as
the ordered partition.

## Mathlib-facing coloured graphs

`SimpleGraph.Coloring` expresses proper colouring, where adjacent vertices
must have different colours. That is not nauty's input. The required object is
an arbitrary ordered vertex partition:

```lean
namespace Hex.GraphIso.Mathlib

structure Colored (V : Type u) (k : Nat) [Fintype V] where
  graph : SimpleGraph V
  color : V -> Fin k
  onto : Function.Surjective color

variable {V W : Type*} [Fintype V] [Fintype W]

structure Colored.Iso
    (G : Colored V k) (H : Colored W k) where
  graphIso : G.graph ≃g H.graph
  map_color : forall v, H.color (graphIso v) = G.color v

def Colored.Isomorphic (G : Colored V k) (H : Colored W k) : Prop :=
  Nonempty (Colored.Iso G H)

end Hex.GraphIso.Mathlib
```

The namespace and structure names above are the public contract. The
distinction from `SimpleGraph.Coloring` is fixed. The structure requires every
colour to occur. A caller with a non-surjective map can either restrict `k`
and renumber the used colours explicitly, or use a checked helper returning
`none` and an unused colour index. The library never silently compresses or
reorders colours because that would change the canonical labelling
convention.

For uncoloured graphs over a nonempty vertex type, `onecell` returns the
one-cell `Colored V 1`. Its result is independent of any ordering of the
vertices.

## Finite encoding

For `[Fintype V] [DecidableEq V] [DecidableRel G.graph.Adj]`, choose an explicit
equivalence `e : V ≃ Fin n`, where `n = Fintype.card V`. The executable graph
has an edge between `e v` and `e w` exactly when the Mathlib graph has an edge
between `v` and `w`. The executable colour of `e v` is the original colour of
`v`.

```lean
def encode (e : V ≃ Fin n) (G : Colored V k)
    [DecidableRel G.graph.Adj] :
    Hex.GraphIso.Colored n k

def decodeLabel (e : V ≃ Fin n) (l : Label n) : V -> V

def decodePerm
    (eV : V ≃ Fin n) (eW : W ≃ Fin n) (p : Perm n) : V ≃ W
```

`decodeLabel` is an explanatory sketch rather than a promise that the public
API returns a function. Public results should retain an equivalence when
bijection is relevant.

The conversion proves:

```lean
theorem encode_adj (v w : V) :
    (encode e G).graph.adj (e v) (e w) <-> G.graph.Adj v w

theorem encode_color (v : V) :
    (encode e G).coloring.cells[e v] = G.color v

theorem encode_iso_iff
    (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H <->
      Hex.GraphIso.Isomorphic (encode eV G) (encode eW H)
```

The two directions of `encode_iso_iff` explicitly conjugate the executable
permutation by `eV` and `eW`. The proof does not rely on a chosen enumeration
being canonical. A different `Fintype` enumeration may change the input label
array, but it cannot change the isomorphism verdict or the abstract
`SimpleGraph.Iso` returned to the user.

For ordinary uncoloured graphs, analogous definitions omit the colour wrapper
and use the one-cell executable colouring. These are the definitions used by
the tactic for `G ≃g H` goals. The Mathlib-free library states the matching
uncoloured surface on `Graph n` itself
([hex-graph-iso.md § The uncoloured surface](../../HexGraphIso/SPEC/hex-graph-iso.md#the-uncoloured-surface)),
so a caller who does not need Mathlib never wraps a graph in a colouring
either.

## Mathematical correspondence

The principal Mathlib theorem states the coloured biconditional directly:

```lean
theorem colored_iso_iff_canon_eq
    (eV : V ≃ Fin n) (eW : W ≃ Fin n) :
    G.Isomorphic H <->
      Hex.GraphIso.canon (encode eV G) =
      Hex.GraphIso.canon (encode eW H)
```

It is proved by `encode_iso_iff` and the Mathlib-free
`Hex.GraphIso.iso_iff_canon_eq`. The uncoloured theorem specializes this
statement to the one-cell colouring.

The library also proves:

- a checked executable transporter decodes to `Colored.Iso G H`;
- every `Colored.Iso G H` encodes to an executable colour-preserving
  permutation;
- decoded canonical labels produce a graph isomorphic to the original
  `SimpleGraph`;
- unequal vertex cardinalities imply `IsEmpty (G ≃g H)`;
- unequal ordered cell-size vectors imply coloured non-isomorphism;
- equality of encoded canonical forms is independent of the chosen finite
  enumerations.

The automorphism surface crosses the same encoding. `autos` decodes the
generators the pinned search discovers into a list of `Colored.Iso G G`
values, one per generator, each an automorphism by the Mathlib-free
`Hex.GraphIso.autos_isIso` composed with the decoder; `sameOrbit_of_autos`
turns two vertices sharing an orbit representative into a
colour-preserving self-isomorphism carrying one to the other. `autOrder`
and `autNumOrbits` report the group order and the orbit count.
`autos_complete` proves that every `Colored.Iso G G` belongs to the subgroup
closure of the returned list. `autos_sameOrbit` upgrades the orbit statement
to a biconditional. `autOrder_card` identifies `autOrder e G` with
`Nat.card (Colored.Iso G G)`, and `autNumOrbits_card` identifies the reported
count with the cardinality of the full group's vertex-orbit quotient.
`autEquiv` and `autOrbitEquiv` transport the executable group and orbit
quotient across the finite encoding. The corresponding executable-graph
statements are `Hex.GraphIso.Aut.closure_eq_group`, `Aut.numOrbits_card`, and
`Aut.order_card`. All use the unchanged computational library; these proofs
introduce no runtime certificate construction.

The bridge supplies global `Group (Hex.GraphIso.Perm n)` and
`MulAction (Hex.GraphIso.Perm n) (Fin n)` instances, with composition acting
as forward permutation application, plus the simp lemmas `Perm.mul_get`
and `Perm.one_get`. Its `Fintype (Perm n)` instance is noncomputable, for
cardinality proofs; executable permutation enumeration must provide its
own computable enumeration. `Colored.Iso G G` also has the corresponding
group and vertex-action instances.

These are ordinary theorems, not classical choice definitions hidden behind
an executable-looking name. The compiled algorithm remains the one in
`hex-graph-iso`.

## Supported tactic goals

Importing the Mathlib library extends the existing `graph_iso` syntax rather
than adding a second tactic name. It supports these positive goal shapes:

```lean
example : G ≃g H := by
  graph_iso

example : Nonempty (G ≃g H) := by
  graph_iso

example : Colored.Iso CG CH := by
  graph_iso

example : Colored.Isomorphic CG CH := by
  graph_iso
```

It supports the corresponding negative forms:

```lean
example : IsEmpty (G ≃g H) := by
  graph_iso

example : Not (Nonempty (G ≃g H)) := by
  graph_iso

example : IsEmpty (Colored.Iso CG CH) := by
  graph_iso

example : Not (Colored.Isomorphic CG CH) := by
  graph_iso
```

`Not (G ≃g H)` is not a Lean proposition because `G ≃g H` is a type. It is
therefore not listed as a goal form.

The same two logical configuration fields as the Mathlib-free tactic are
accepted:

```lean
graph_iso
  (maxSearchNodes := 200000)
  (maxCertRecords := 200000)
```

Both default to `100000`. The Mathlib extension does not reinterpret them.
Kernel replay uses Lean's actual resource controls.

## Ground-term contract

The tactic accepts a graph term when all of the following hold:

1. The graph, vertex types, and colouring have no free variables or unresolved
   metavariables.
2. Lean can synthesize `Fintype` and `DecidableEq` for both vertex types.
3. Lean can synthesize decidability for every adjacency proposition it must
   enumerate.
4. Every adjacency and colour application on the finite enumeration reduces
   enough for the tactic to construct a kernel-checked proof of its Boolean
   value.
5. For coloured inputs, the user supplies the surjectivity proof carried by
   `Colored`.

This is a capability test, not a constructor-name list. Literal edge sets,
`SimpleGraph.fromRel`, complements, maps, induced graphs, and other transparent
closed constructors work when their decisions reduce. A new transparent
Mathlib constructor needs no tactic update. An opaque definition fails even if
the elaborator could evaluate it through an unsafe compiled shortcut.

The reifier enumerates vertices in the synthesized `Fintype` order and creates
one literal upper-triangle adjacency bit for each pair. Each bit is accompanied
by a proof of the corresponding original adjacency proposition or its
negation. The aggregate graph correspondence follows from `SimpleGraph.ext`.
The compiled evaluator may propose the bits, but the emitted proof checks them
against the original term.

On failure, diagnostics name:

- the first missing finite or decidability instance;
- the first vertex pair whose adjacency did not reduce;
- the first colour application which did not reduce;
- an unused colour when a checked colouring constructor fails;
- the first unresolved metavariable or free variable;
- the search or certificate-record limit which was exhausted, or Lean's
  resource-limit diagnostic.

The goal is unchanged on every failure.

## Positive proof path

For equal vertex cardinalities, the tactic:

1. reifies the two graphs and proves the two adjacency correspondences;
2. reifies and proves colour correspondences when colours are present;
3. runs the compiled `findIso` search under `maxSearchNodes`;
4. hands the returned literal permutation to the same witness route the
   Mathlib-free tactic uses, which ties each side's adjacency, colouring
   and the permutation to list literals and closes through
   `Kernel.checkIso` and `Kernel.isIso_of_checkIso`;
5. conjugates the permutation by the two finite enumerations;
6. constructs an explicit `SimpleGraph.Iso` or `Colored.Iso`;
7. wraps it in `Nonempty` when required.

The theorem installed in the environment contains the literal permutation,
the reification equalities, and applications of proved checker theorems. It
does not contain a trusted native computation.

If the vertex cardinalities differ, positive search is skipped and the tactic
reports the two cardinalities.

## Negative proof path

If vertex cardinalities differ, the tactic proves that an equivalence would
contradict `Fintype.card_congr`. If ordered colour-cell sizes differ, it proves
that a colour-preserving equivalence would induce equal cell cardinalities.
Neither case runs canonical search.

Otherwise the tactic:

1. reifies both inputs with kernel-checked correspondence proofs;
2. obtains executable non-isomorphism of the encodings from the shared
   Mathlib-free negative routes, the root separator and then certificate
   replay, described in
   [hex-graph-iso.md § The Mathlib-free graph_iso tactic](../../HexGraphIso/SPEC/hex-graph-iso.md#the-mathlib-free-graph_iso-tactic);
3. transports that result through the `not_encode_iso` theorems;
4. constructs `IsEmpty` or the requested negated `Nonempty`
   proposition.

Search exhaustion, certificate-limit exhaustion and Lean resource failures
never select the negative branch.

## Trust and resources

The trusted path consists of Lean definitions, proved correspondence
theorems, the Mathlib-free checker and its soundness proofs, the emitted
literal data, and kernel type checking. Compiled reification, graph search,
certificate construction, and the elaborator's preliminary self-check are
untrusted conveniences.

Search-node and certificate-record limits govern proof search and certificate
admission. Kernel replay uses Lean's heartbeat, recursion-depth and memory
controls. The literal term is rejected before emission if its certificate
record count exceeds `maxCertRecords`.

The library never uses `native_decide`. It introduces no axiom and has no
fallback to an external graph program.

## Manual example with Mathlib

The Mathlib portion of `HexManual/Chapters/HexGraphIso.lean` repeats the
Petersen example from the Mathlib-free SPEC using ground `SimpleGraph` terms.
It deliberately gives the two isomorphic presentations different vertex
types:

```lean
def petersenDrawing : SimpleGraph (Fin 10) := ...

def kneser52 : SimpleGraph {s : Finset (Fin 5) // s.card = 2} := ...

example : Nonempty (petersenDrawing ≃g kneser52) := by
  graph_iso

example : IsEmpty (petersenDrawing ≃g pentagonalPrism) := by
  graph_iso
```

`petersenDrawing` uses the outer-pentagon, inner-star, and spoke presentation.
`kneser52` joins disjoint two-element subsets. The positive goal therefore
shows that the tactic enumerates two unrelated finite vertex types and returns
a genuine `SimpleGraph.Iso`, rather than recognizing definitional equality.
The prism goal shows the negative `IsEmpty` path on the same pair of regular
ten-vertex graphs as the Mathlib-free chapter.

The chapter finishes with the two edge-marked and one nonedge-marked ordered
colourings from the Mathlib-free example. It states them as `Colored` values
over `petersenDrawing`. `graph_iso` closes a positive `Colored.Iso` goal between
the edge-marked colourings and a negative `Colored.Isomorphic` goal against the
nonedge-marked colouring. The prose explains that adjacency of the colour-zero
pair is an invariant, while the negative tactic proof is obtained from the
general canonical-form certificate rather than a handwritten special-purpose
lemma.

These examples are compiled as part of the manual. They use only ground terms,
state explicit logical limits if defaults do not suffice, and do not require
an external nauty installation.

## Tests

The library's tests cover both theorem correspondence and the tactic runtime.
They include:

- direct `SimpleGraph.Iso` and `Nonempty` positive goals;
- `IsEmpty` and negated-`Nonempty` negative goals;
- distinct vertex types of equal cardinality;
- immediate unequal-cardinality negatives;
- ordered colours preserved and deliberately violated;
- equal underlying graphs with different ordered cell sizes;
- all empty-graph goal shapes;
- transparent composed constructors;
- a deliberately opaque adjacency definition with the expected diagnostic;
- malformed or underfunded certificates rejected without changing the goal;
- a positive random `n = 12` relabelling and a negative random `n = 12` pair;
- positive and negative coloured cases at `n = 10`;
- a scheduled negative CFI pair with separately recorded limits.

Fresh-module probes separate import, reification, compiled search, literal
elaboration, kernel replay, and whole-tactic cost as required by
[benchmarking.md](../../SPEC/benchmarking.md). This Mathlib library has no ordinary
computational benchmark target. The canonical algorithm and external nauty
comparison remain in the Mathlib-free benchmark driver.

## Sparse correspondence

`HexGraphIsoMathlib.Sparse.Encode` supplies
`Hex.GraphIso.Mathlib.Sparse.encode`, `encode_adj`, `encode_color`,
`toDense_encode`, `isoOfIsIso`, `isIso_of_iso`, and `encode_iso_iff`.
The executable encoding filters the finite vertex enumeration into sorted
neighbour lists and packs them directly. Its colour vector preserves the
ordered, surjective colour map. The equality to the explicit dense encoding
is a proof bridge, not an operation performed by sparse execution. This
relation and transporter correspondence does not depend on canonical-search
correctness. `Sparse.Canonical` additionally proves production canonical and
decision correspondence from the completed sparse maximum theorem.
Automorphism, orbit and order correspondence require the further group
theorems below.
The core's canonical-storage installation and exact comparison sign and
shared-prefix semantics, complete indirect-sort ordering,
bounded-stack exhaustion, and shortest-path distance proofs establish primitive
contracts. Distance values are equivariant under relabelling, including
unreachable vertices. The canonical-form correspondence uses the proved
production maximum. Complete
refinement code and ordered-cell equivariance is proved below. The core proves
cell-index construction, scratch preservation by target selection, and exact
fresh/cached target agreement, including hints and the depth cutoff. Executed
splitter activation accounting also proves refinement's bounded-loop exhaustion
under the initial active-count bound. Exact cell accounting and the complete
certificate induction identify its result as an equitable valid partition.
Count splitting also has executed label-permutation and unchanged-exterior
proofs, preserving the vertex multiset of every incoming partition cell.
The executed splitter orders its cell by hits under its initial sentinel bound.
Under the local count bound, it closes exactly the boundaries between unequal
adjacent counts and retains the other partition values. Output cells are
exactly maximal constant-count runs; cells outside the split retain their
partition data. The executed count splitter preserves a valid partition cache,
including singleton sentinels and entries outside the split. Its hypotheses are
a valid incoming cache, a bounded partition cell, a valid label permutation,
partition allocation, and the local count bound. Native neighbour counting
proves exact counts on touched cells and bounds them by the splitter size,
including first-touch clearing and singleton skips. The full nontrivial pass
preserves the labelling permutation, partition allocation, and full cache
validity. Both full passes preserve the vertex multiset of every original
partition cell. The complete nontrivial pass also gives constant native
counts into the captured splitter on every output cell, including untouched
cells with zero semantic counts and unrestricted retained scratch.
The complete singleton pass proves the corresponding native row-count
constancy, including untouched and uniform cells. It also proves the semantic
activation rule: all fragments of an active original cell are active, and each
other original cell has at most one inactive fragment. The complete count
splitter and nontrivial pass prove the same activation rule. Saved queue
positions select interior fragments, so largest-fragment replacement cannot
change active membership outside the split cell. Accumulated native counts
are proved equal to the shared set-intersection cardinalities. Both actual
main-loop branches preserve the equitability certificate, including queue
removal and hashing, via a proof projection of the partition fields. The
projection invokes no dense algorithm. Native distance classes preserve the
same certificate, including unreachable sentinels and small graphs. The
literal distance loop and complete refinement preserve the certificate;
exact accounting and stopping give equitable output. The actual initializer
supplies the certificate and an equitable root for every nonempty sparse
coloured input.
Individualization in the actual sparse policy supplies the child certificate,
valid partition, label permutation, scratch and exact count. Its production
visit returns an equitable child. Fresh and cached target selection derive a
bounded nontrivial cell from node facts, including checked-label success.
The native target counts correspond to set-valued neighbour counts. Target
scores and the first maximum are invariant under reordering within equitable
cells, and transport under graph isomorphisms. The full fresh/cached target
position, vertex set and size satisfy both laws, including hints, depth
cutoffs and invalid-cache fallback.
The count splitter's sorted key sequence and literal output partition are
determined by the input count multiset. Each fragment contains exactly the
original vertices with its count. Ordered partition and cell contents
commute with vertex renaming and with permutations within input cells;
the two minimum keys and their cut positions are uniquely determined.
A uniform count cell changes only the hash of its start. The literal control
trace of all nonuniform branches is proved, including both distance modes
and the strict largest-fragment tie rule. The combined count-split transport
law preserves the hash, active set, ordered queue and exact cell count as well
as the partition and cell contents. Hit agreement is local to the divided
cell, allowing stale counts elsewhere. The singleton, nontrivial and distance
passes compose into full refinement code and ordered-cell equivariance below.
Valid vertex-index caches transport under renaming, including singleton
sentinels, and their endpoints agree at cell starts. The executed native
singleton marking loops return identical sorted touched-cell arrays and
transported vertex-mark predicates, allowing different generations, retained
marks and native neighbour orders.
The restored compaction fragments have exact retained-order and reversed-hit
formulas. Their cut positions, hit counts and vertex multisets transport
under a mapped permutation with the transported mark predicate.
The complete executed singleton-cell body has a proved observation contract
for its hash, active set, ordered queue, partition and counter in terms of
those class sizes, along with label-window and scratch-frame preservation,
literal fragment lists and preservation of valid incoming indices through
the executed cache writes. The actual native marking and touched-cell loops
compose these contracts into full production singleton-pass transport: ordered
partition, hash, active set, ordered queue and exact cell count agree literally,
and output cell multisets commute with vertex renaming. The input orders
within cells, native row orders, admissible caches and generations may differ.
The complete native nontrivial scans transport their neighbour multisets,
first-touch lists and exact touched-cell counts. The actual count-split loop
has a proved trace retaining pending-cell bounds. Its composition proves full
production nontrivial-pass transport of ordered partition, cell multisets,
hash, active set, ordered queue and exact cell count, leaving untouched scratch
hits unrestricted. Native BFS initialization, the complete distance-cell loop,
and the actual main loop now transport too, including first-ten preference,
swap/pop removal, hashing, dispatch and early breaks. Queue enumeration and
index rebuilding supply their invariants. `refineWith_parts` connects all
proof blocks to production by kernel definitional equality. `refineWith_equiv`
proves full code and ordered-cell transport under independently bounded
scratch, with literal partition, active-set, queue, count and hash agreement.
The computational theorem `refineWith_congr` also proves literal label-array
agreement for identical inputs with arbitrary bounded scratch. Its remaining
observations—partition, active set, ordered queue, count and hash—agree too.
The proof follows both native splitters, initial index rebuilding, native BFS,
the complete distance and main loops, and final cleanup. Exact insertion,
partition swaps and sort-stack order preserve ties when counts agree only on
the current cell. The hypotheses are a label permutation, an allocated closed
partition, active cell starts and bounded scratch; stale counts, marks and
generations need not coincide.
The singleton compaction and reverse reinsertion loops have exact order and
index-write contracts, yielding their local permutation and predicate classes.
Per-cell cache finalization is proved, including uniform and mixed cells.
Native marking agrees with adjacency and enumerates bounded nontrivial cells
without duplicates; sorting preserves its coverage. The complete singleton
pass preserves the label permutation, partition allocation, and full cache
validity through every touched cell and uniform-cell return. Its counter
increments equal new boundaries, and inherited closed values are retained
literally. It preserves a duplicate-free queue agreeing exactly with the
active bitset and containing only cell starts. The executed insertion, removal,
and replacement operations have exact membership proofs. The complete count
splitter preserves this queue contract, including the initial fragments,
bounded tail scan, and largest-fragment replacement. The active-set invariant
needed for equitability follows from the fragment activation proofs.
The full refinement preserves partition allocation and old closed boundaries.
Its root active-count bound follows from the executed initializer, whose colour
cells satisfy the shared partition-state contract and are all initially active.
That root count equals its boundary count. The executed count splitter's
counter increments equal its new boundaries under the local hit bound;
both full passes compose this relation and preserve inherited closed values.
The complete refinement now composes the combined invariant through index
rebuilding, distance initialization, first-ten queue selection, removal, and
both splitter branches. It preserves label permutations, original cell
multisets, exact cell accounting and active queues, and returns scratch
indices valid for the output partition whenever indexed. Native shortest-path
and first-touch count proofs supply its local bounds. Production visits
preserve the shared partition-state contract and return valid scratch.
The active-cardinality bound holds at every valid partition, and exact
accounting identifies the loop exits as an empty queue or a discrete
partition. Certificate preservation proves equitability at both exits;
`Reach` supplies the entry invariants at every production call.
The count splitter also retains inherited closed boundary values literally.
Recovery to an ancestor level identifies the partitions before and after that
count split. Shared recovery facts apply to the sparse storage type, and the
actual sparse child, recovery, and target transitions preserve scratch validity.
Persistent allocation and generation bounds are proved through every
splitter, the complete refinement function, and the production visit. Target
selection preserves those bounds independently of index correctness.
`SearchBounds` instantiates the shared recursion contract to carry these
bounds through every production node, sweep, nonlocal exit and final
installation, with the root premise derived from initialization. The
complete refinement loop integrates the index and first-touch count semantics;
`Reach` supplies well-formed entries throughout the production recursion.
Its contract preserves equitable parents, exact counts, original colour-cell
contents, target membership and saved-label frame effects across every child,
recovery and nonlocal exit. Root premises are derived from stable buckets.
`Fuel` proves sufficient node and packed-cursor bounds for the actual mutual
recursion. Its unconditional `runState_noFuel` includes order zero and uses
the unchanged production bounds. The actual first descent and all subsequent
returns preserve an installed, colour-respecting canonical label. `Result`
proves unconditional parser success, including order zero, and `Sparse.Ops`
extracts the total native result. Its relabelling, ordered colours, transporter
soundness and exact diagnostic agreement are proved.
Bare sparse wrappers expose the same native search for all orders, with a
zero-colour empty view and one colour otherwise. Their form and literal label
agreement, relabelling, canonical invariance, isomorphism equivalence and
both decision directions are proved using the production maximum.
Saved first-reference arrays are preserved through every off-path node and
later sibling. Their exact preparation writes, ancestor slots and allocations
are proved. Every emitted sparse refinement code is below the terminal
sentinel, and comparisons cannot advance below the saved leaf; the initialized
root supplies this sentinel and a valid, colour-respecting first label.
Native classification preserves the incumbent row prefix and supplies the
candidate prefix for every better verdict. The full production recursion
preserves this cache, initialized by its actual first leaf. Unconditional
root and final-installation theorems identify each returned working row with
the public label's relabelled neighbours, preserving raw row order during
search and covering order zero.
Every production node and sweep preserves the permutation workspace size.
Its scatter is proved to store the exact forward map between parsed labels.
Canonical ties and explicitly scanned first-reference admissions are proved
to emit coloured automorphisms, using label reachability and native row-cache
validity. Cheap first-reference admissions are justified by ancestor histories
derived in the executed-search trace induction.
The cheap-guard shapes and cell-stabilizer transitivity are established for
native equitable partitions. They persist through literal cached child
calls; whole descents transport under isomorphism. Two discrete descents
below such a node with the same target positions have equal normalized
leaf graphs. A discrete descent following a target prefix has the same depth
and graph. Saved reference codes and target slots connect this result to the
literal workspace scatter. Current histories survive within-cell reordering
and extend through actual cached child calls; their discrete labels are
literal. The native first-reference classification is a coloured automorphism
under these history premises. Selected descents transport with all codes and
target choices under isomorphism. At an open saved-target prefix the actual
unhinted target is the next stored target, including after sibling reordering.
The actual cached hint then retains the unhinted target's position, vertex set
and size, allowing its resulting scratch contents to differ.
The trace induction supplies frozen ancestors, current histories and target
agreements at each executed cheap admission.
The saved first-reference history is derived from actual initialized
execution: its selected native targets, complete code sequence, literal leaf
label/partition and sentinel are proved and retained after later siblings
and final row installation. Bounds on these executed codes and retained
canonical allocation initialize both comparison machines at the actual first
leaf. Stable incumbent storage reads the semantic native sparse key.
The comparison invariant includes parsed reference labels and the first key's
lower bound on the incumbent. Native preparation, target selection, child
entry and ancestor recovery preserve it, including recovery after a negative
row verdict with tied codes. The canonical verdict computes the exact native
key maximum and leaves settled code semantics. Native descents preserve
ancestor cells and literal individualized vertices. Guided and selected paths
with corresponding terminal labels have equal depths and complete code
sequences; a native automorphism identifies their first sentinel and graph.
These histories extend through cached child visits and recover after sibling
reordering. Together with admission soundness they establish the full
first-reference key and executed leaf maximum. The actual first child supplies
the general history, and preparation, child entry and full-call recovery retain
it. Every terminal classification returns settled comparisons and preserves or
improves the incumbent. Both comparison machines and incumbent growth are
proved through the executed node/sibling recursion; the actual first descent
initializes this result at the root. Final row installation retains the settled
comparisons and readable incumbent. Complete native calls retain canonical
reference provenance: a child keeps its incoming reference or installs one
through its literal chosen vertex, and a reference pointing above that child
remains unchanged. The canonical-reference guide preserves a covered-child
witness through permutations and recovery, consuming local child coverage
from the future coverage induction. Short-return provenance retains the exact
emitting pair and its canonical ancestor and trace entry, or the implicit
pair's cheap-boundary limit. The exact receiving level and retained capacity
are proved, and actual receiver pairs are valid for both explicit and implicit
emissions. Subtree maxima aggregate the existing unpruned leaves and have
attaining labels with sufficient fuel. They transport under native
isomorphisms, checked cell stabilizers and recovered parent frames. Both
actual filters preserve ranked child coverage, including carriers outside
earlier survivors. Coverage and reference keys survive sibling reordering;
an actual received canonical scatter covers the whole current child through
its already covered reference. Common ancestor codes preserve native key
comparisons and maxima. The complete unpruned maximum is attained by a child;
fresh-to-cached visit transport identifies actual codes, counts, partitions,
parent frames and target fields. Internal-node bounds are characterized by
the actual cached target's complete child maxima, and discrete nodes have
exactly their parsed leaf key. Exhausting ranked child coverage covers the
complete node. A negative code comparison after native preparation covers
every continuation, while actual classifier exits satisfy native incumbent
upper bounds and candidate coverage. Valid frozen native entries and their
original child keys survive parent reordering. Actual discrete exits and
nondiscrete code rejection satisfy whole-node bounds and coverage. Recorded
ancestor entries with their actual code prefixes supply nonlocal witnesses
from negative comparisons; code-supported nondiscrete rejection satisfies
the complete return contract. Received children, orbit skips, both native
filters, recovery and the next off-path sibling call compose original-window
coverage using the child's maximum result as the recursive hypothesis.
Under the cheap shape all complete native child keys coincide. Full node
coverage is identified with its original cached target, and a passing native
cheap guard makes any actual individualized child attain the whole node key,
including after sibling reordering. A suspended native parent retains its
literal chosen child; under the cheap shape their full keys coincide unless
a negative comparison already covers the parent. The ancestor-chain
invariant is initialized at the root, extends on individualization and is
preserved under incumbent growth and the native cheap-boundary counter
alternative. Given this invariant, coverage composes across cheap ancestors;
actual discrete emissions to their cheap boundary and every nondiscrete
rejection satisfy the full return contract. Actual preparation establishes
the stronger target alternative: an unhinted target or a code prefix whose
every continuation is covered. Thus hinted children satisfy the parent
upper bound. Both preparation paths establish suspended-parent validity
and child scopes; complete off-path calls retain ancestors. Actual recovery
supplies the next surviving vertex's comparison, history, target, shape and
ancestor invariants. The full off-path node/sibling upper-bound induction
is proved, including both filters, orbit skips, hinted targets and nonlocal
returns, from native entry and ancestor invariants without an assumed
subcall maximum theorem. The executed first discrete call also satisfies
its complete maximum contract: actual stored-prefix writes and allocation
initialize the code machine, and the installed native key is the complete
frozen node key. Native first-entry storage, histories and inherited shape
are derived from the root and preserved through actual first children.
At arbitrary entry depth, literal stored-prefix and suffix writes supply
the complete first-leaf comparison and the caller's recovered code prefix.
The actual first-child return supplies the next sibling's comparison,
history, target, shape and ancestor facts without assuming its maximum
result. The complete first-path upper-bound induction is also proved,
including all later siblings. Sufficient-fuel stability identifies its
root bound with the declarative maximum. `runState_upper` and `run_upper`
give the resulting unconditional bound on every installed production
key; the order-zero state has no installed code chain. Native row-cache
finalization preserves the bound.
The retained parent chain determines every suspended child frame and
preserves its closed boundaries literally. These facts place the actual
emitter inside that child and retain the chosen vertex at its exact
target position. A native automorphism's reference scatter therefore
transports full child coverage and supplies the corresponding nonlocal
witness. The covered-reference invariant initializes at the root and
extends through actual individualization. Earlier reference associations
survive complete off-path calls, terminal dispatch and both child
return/recovery paths. From that invariant and positive strict ancestor
counters, first-reference automorphism leaves satisfy the full maximum
return contract, including cheap admission and nonlocal returns.
Canonical-reference leaves satisfy it when returning to their canonical
ancestor, for either short flag. Both rules derive the actual native scatter.
Recovery now establishes both reference guides for the next sibling from
the completed child's coverage, including the first saved label's literal
descent and selected position. Ancestor order and positive receiving counters
follow from native recursion and recovery. Ranked frozen-cell coverage gives
coverage of smaller target vertices, including filtered ones; the actual
orbit trace transports the selected child to such a vertex. The coset index
is preserved by off-path recursion and associated with its suspended first
ancestor through preparation, selection and both return paths. These facts
prove the full canonical-admission return rule, including the earlier
first-ancestor coset branch, from local traversal invariants.
The computational library assembles the reference, rank, index, counter,
trace, code-history and workspace invariants through native off-path
preparation, child entry and recovery. Its frozen target is the actual
selected cell, including hinted selections. The complete later-sibling
coverage induction covers both filters, orbit skips and nonlocal returns;
all terminal classifier cases are proved. `MaxNode.node_max` combines this
with the established upper bound to prove the off-path node maximum
contract by induction on the actual recursion bound. `MaxFirstContext`
initializes the first descent, `MaxFirstPairs` and `MaxFirstNext` restore
the complete context after its first child, and `MaxFirstFilter` justifies
the emitted short-prune pair. `MaxFirstLower` and `MaxFirstNode` close the
complete first-descent coverage induction. `runState_max` and `run_max`
identify the nonempty production key with `canonSpecKey` without any
search-result premise. The computational `Sparse.Canonical` module proves
equality of the total public and declarative forms at every order, including
the unique empty graph, and derives complete canonical and decision contracts.
Cell stabilization transports between suspended ancestors. The actual orbit
pointer's trace word supplies a checked carrier and preserves ranked child
coverage when its generators stabilize the frozen partition. Native generator
soundness discharges this condition for an empty individualized path.
The native frozen-reference invariant is also preserved through the complete
mutual recursion, including truncated calls and nonlocal returns. The actual
first leaf initializes both saved references inside every suspended ancestor's
cells, and the first descent's complete returned computation retains trace
stabilization. The first child's prepared parent therefore obtains the
stabilization premise used by the actual orbit guard. The complete maximum
induction uses these proofs at actual first-child recovery and later siblings.
Frozen equitable witnesses retain their full
refinement certificates under within-cell reordering. The current descent
witness matches production arrays and count, extends through actual cached
child visits, and recovers using the established native frame effect.
Live first-code alignment retains that descent through arbitrary off-path
child returns and identifies actual cached targets with their saved slots.
Descendant calls retain the frozen ancestor and cannot enable its failed
cheap guard. The combined cheap history has preparation, child and recovery
transitions and proves both first-admission guard arms sound; its depth bound
comes directly from the saved sentinel. The first-path guard shape is
initialized and preserved through first children. Completion of the actual
first-child call supplies the recovered history and saved target. Native
automorphism verdicts append exactly their validated workspace arrays; other
leaf actions preserve the trace. Installed references and workspace validity
are derived from the first descent and preserved through complete off-path
calls. These facts combine with the histories through preparation, admission,
child entry and recovery. The mutual recursion and first-path induction prove
the unconditional root trace guarantee, including order zero and final row
installation. `generator_iso` identifies every literal emitted array with the
exact forward map of a native colour-preserving automorphism. Every final
orbit pointer descends and is connected by a word in that trace; `orbit_iso`
realizes its image by a native coloured automorphism. Pointer soundness supplies
one direction of the exact orbit correspondence proved below.
`GenerationFrame` proves target-cell preservation by true point
stabilizers and triviality at actual first discrete visits. Complete calls
retain every emitted array, and the decoded full trace realizes each array
and supplies generated carriers for orbit pointers fixing the active base.
Native first-code and all-same lower bounds, exact all-same preservation,
and unconsumed leaf-return provenance and bounds are proved. Matching
stored-target descents below a cheap ancestor have the exact saved codes;
equal native leaf graphs force actual first-reference admission with an
emitted label carrier. The complete executed cheap-reference descent and its
carrier are proved, including cached child visits after sibling recovery.
Every later first-path child returns locally, its full sibling sweep
finishes, and every actual first-path call returns normally to its parent.
Generated sibling coverage and the full first-path generation induction are
proved for the native emitted trace, including the initialized root at order
zero. Native fixed-singleton
preservation and full node/sweep fixed-point restoration are proved, including truncation
and nonlocal returns; the completed root retains no temporary fixed vertices.
Cached refinement preserves cell stabilizers, and native path invariants are
initialized and preserved through local transitions and complete child recovery.
Implicit pairs are justified at actual equitable states and preserved through
refinement, child calls and recovery. The full mutual recursion and first-path
proofs validate every pair in the final bounded pruning workspace, including
replacement of its last slot and order zero. Path transport gives checked
automorphism carriers for long-filter removals and whole-cell representatives.
The complete maximum induction integrates the reference guide, receiver
validity, filter coverage and code histories. Complete generation under
pruning and correctness of the executed stabilizer-index product are proved.
The core defines the finite unpruned sparse tree with hint-free targets and
every target child. It proves nonempty leaves, stability under increasing any
sufficient fuel bound, and a maximum with a reachable attaining label.
Executed refinement preserves ancestor cell contents and inherited boundary
values. Every unpruned leaf preserves the original ordered colour cells;
the attaining form has the canonical sorted colour sequence and normalized
native neighbour rows. Complete root, refinement and individualization
invariants support transport of every unpruned leaf and its code chain.
`canonSpecKey_map` proves maximum invariance; `specCanon_invariant` and
`iso_iff_specCanon_eq` prove the declarative canonical-form characterization,
including order zero. The proved production equality supplies correspondence
of the optimized public canonicalizer.

`HexGraphIsoMathlib.Sparse.Canonical` proves `iso_iff_canon_eq` for arbitrary
finite enumerations, `canon_encode_eq` for changes of enumeration, `isIso_iff`
and `findIso_eq_none_iff` for the complete executable decision, and
`isoOfFindIso` for its actual transporter. The sparse automorphism bridge proves
full decoded generation, exact orbit quotients and counts, and equality of the
executed group order with the full automorphism-group cardinality. The canonical
certificate and sparse tactic guarantees below are integrated. The scheduled
sparse CFI proof passes four fresh builds. The full build, conformance,
published trust/import audits and final performance checks pass; evidence is
recorded in `reports/sparse-nauty-validation.md` in the development monorepo.

Sparse computational graphs use `Hex.SparseGraph` and
`Hex.GraphIso.Sparse.Colored`, with their own sparse-nauty canonical forms.
The bridge supplies explicit sparse encoding along a finite enumeration,
adjacency and colour correspondence, and decoding of sparse transporters to
`SimpleGraph` isomorphisms. The sparse canonical-form biconditional is
independent of the chosen enumeration. It does not assert equality with
the dense canonical form after conversion.

Generation completeness identifies the subgroup generated by decoded sparse
generators with the full colour-preserving automorphism group. Sparse orbit
representatives classify that group's orbits, and the sparse order operation
computes its cardinality. These proofs follow the sparse executable and its
individualization recursion, using the shared permutation correspondence.
In particular, the order correspondence identifies the sparse search's
first-path stabilizer-index product with the group cardinality; it does not
replace that computation by a second sequence of stabilizer searches.
The computational `FirstCount` theorem supplies checked cell-stabilizing
carriers for the distinct vertices counted by the actual first sweep.
`FirstUniform` and `FirstWitness` justify the executed all-same boundary
and its stored native reference using those carriers. These facts include
the complete sparse leaf keys and target sequences, and their transport
does not assume generation completeness.
`UniformReturn` proves actual trace emission for matching uniform native
subtrees, including the checked carrier and its return ancestor.
`ReferenceOrbit` transports the richer native reference along every true
path-stabilizer orbit before generation completeness is known.
Native reference occurrences survive the actual sibling reordering,
received canonical carriers, and both checked pruning filters.
`ReferenceLoop` supplies the full off-path sweep induction from the
reference-return premise for actual smaller children. `SmallUniform`
derives complete key and target uniformity below cheap-shaped native
nodes using true cell stabilizers, independently of the emitted group.
`ReferenceComplete` proves the reference-return premise for the executed
node recursion, including nodes above the uniform boundary.
The native converse coverage theorem is proved: `GeneratedRoot.generated_iff`
identifies generated membership with being a colour-preserving sparse
automorphism. `Sparse.AutGroup.closure_eq_group` identifies the resulting
Mathlib subgroup, and its `orbitEquiv` and `numOrbits_card` prove that the
actual representatives and counter describe the full orbit quotient.
`Sparse.Automorphism.autEquiv`, `autos_complete`, `autos_sameOrbit` and
`autNumOrbits_card` transport these results through arbitrary finite
enumerations to Mathlib coloured graphs. The native `StabilizerHead`
theorem identifies every complete first-path index with its true
point-stabilizer orbit size. `OrderOps` proves accumulator preservation by
off-path calls and sibling sweeps, and `OrderStep` proves the literal
first-child multiplication. `Sparse.Order` identifies this executed product
with the full group cardinality, including order zero. Its public
`Sparse.Aut.order_card` theorem and `Mathlib.Sparse.autOrder_card` establish
exact native and decoded group orders for every finite enumeration.

Existing direct `SimpleGraph` tactic goals retain the existing dense encoding.
Explicit sparse encodings allow sparse-native `graph_iso` proofs to transfer
through the correspondence theorems. No graph-density heuristic chooses an
engine. Sparse-native proof search and replay operate on adjacency lists;
encoding a general `DecidableRel` adjacency oracle may still inspect all
vertex pairs, and that cost is documented separately.

The core sparse canonical-certificate checker proves its accepted key is the
declarative maximum. Its unlimited expansion producer is complete and retains
the optimized search's literal label; equivalent imported-module kernel replay
checks the recorded order-12 random keys and proves their negative pair.
Full result checking proves the returned form canonical and the label an
actual relabelling; unlimited certification agrees exactly with the direct
result, including its literal label. Compact replay checks automorphism and
ordered-child transport witnesses before reusing earlier checked sibling flags.
Its unlimited producer is proved complete, preserves exact direct-result
agreement, and retains full expansion when no witness is available. Equivalent
literal compact replay has kernel acceptance and malformed-reference tests.
The record-limited checker proves exact unlimited-verdict agreement and
exhaustion semantics. The native tactic backend emits kernel-checked proofs
for the empty graph, recorded order-12 positive/negative pairs and ordered-colour
Petersen order-10 pairs. Both proof routes share one bounded native search quota
across the two inputs. Its proofs count actual native visits and freeze exhausted
state. Negative candidates use bounded compact production with exact record
accounting and successful-tree agreement with unlimited production. The exact
unlimited size is proved sufficient, with exhaustion precisely below that cap;
sufficient-quota candidates retain the optimized run's key and literal label.
Boundary tests cover empty graphs, random inputs and ordered-colour Petersen inputs.
The general agreement proof identifies complete successful bounded states with
the direct runs through every callback and recursive return. Consequently the
bounded certificate pipeline retains the unlimited candidate's exact key and
literal label and is proved to replay successfully. Sparse kernel replay uses
the original literal checkers, with Lean's actual resource controls and no
operation counters or estimated replay-cost limit. Public coloured and bare
sparse `graph_iso` dispatch is integrated, including empty graphs and logical
limit exhaustion. `SparseTacticTests` checks imported kernel replay through the
explicit Mathlib sparse encoding, covering ordered-colour positive/negative
pairs, empty graphs and a nonidentity finite enumeration. Both sparse rows and
colours use Hex's kernel-transparent vector constructor, with the same encoding
and correspondence contracts.

Sparse release requires the same correspondence and kernel-replay guarantees
as dense release, including empty graphs, ordered colours, changes of finite
enumeration, positive and negative examples, and exact automorphism results.

## Release conditions

The Mathlib-facing release is complete only when:

1. `encode_iso_iff` and `colored_iso_iff_canon_eq` have no unfinished proof.
2. Every supported positive goal constructs an explicit isomorphism checked
   by the kernel.
3. Every supported negative goal ends in the Mathlib-free canonical-form
   biconditional or an exact cardinality contradiction.
4. Opaque and open inputs fail with the promised diagnostics.
5. Non-toy positive and negative tactic examples pass under their recorded
   limits.
6. The Petersen examples in both portions of the manual compile and exercise
   positive, negative, different-vertex-type, and positive and negative
   ordered-colour goals.
7. The tactic proof path contains no `native_decide`, unsafe theorem, or
   axiom.
