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

For uncoloured graphs, `Colored.singleColor` returns
`Sigma fun k => Colored V k`. It uses `k = 0` for an empty vertex type and
`k = 1` otherwise. Its result is independent of any ordering of the vertices.

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

The same three logical configuration fields as the Mathlib-free tactic are
accepted:

```lean
graph_iso
  (maxNodes := 200000)
  (maxCertNodes := 200000)
  (maxCheckerSteps := 10000000)
```

The default values remain `100000`, `100000`, and `5000000`. The Mathlib
extension does not reinterpret them.

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
- the search, certificate, or checker limit which was exhausted.

The goal is unchanged on every failure.

## Positive proof path

For equal vertex cardinalities, the tactic:

1. reifies the two graphs and proves the two adjacency correspondences;
2. reifies and proves colour correspondences when colours are present;
3. runs the compiled, bounded `findIso?` search;
4. checks the returned literal permutation with the Mathlib-free, bounded
   `checkIso?`;
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
   Mathlib-free negative engine, which selects by measured replay cost
   between the certificate route and the verified pairwise decision
   (per the core SPEC's tactic section);
3. transports that result through the `not_encode_iso` bridge
   theorems;
4. constructs `IsEmpty` or the requested negated `Nonempty`
   proposition.

Search exhaustion and checker exhaustion are errors. They never select the
negative branch.

## Trust and resource accounting

The trusted path consists of Lean definitions, proved correspondence
theorems, the Mathlib-free checker and its soundness proofs, the emitted
literal data, and kernel type checking. Compiled reification, graph search,
certificate construction, and the elaborator's preliminary self-check are
untrusted conveniences.

Reification charges every enumerated vertex, vertex pair, and colour
application against an additional elaborator-side size report. These counts
are displayed on failure but do not replace the three checker limits. The
literal term is rejected before emission if its certificate record count
exceeds `maxCertNodes`.

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
