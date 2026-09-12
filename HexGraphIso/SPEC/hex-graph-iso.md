# hex-graph-iso (coloured graph canonical labelling)

`hex-graph-iso` computes canonical forms and isomorphisms of finite simple
undirected graphs with ordered vertex colours. It depends only on
`hex-graph`. It does not depend on Mathlib or on an external graph program.
The separate [hex-graph-iso-mathlib](../../HexGraphIsoMathlib/SPEC/hex-graph-iso-mathlib.md) library relates
these operations to `SimpleGraph` and provides the Mathlib-facing
`graph_iso` tactic.

The first release has two correctness requirements which must not be
confused:

1. Lean proofs establish that two coloured graphs are isomorphic exactly
   when their canonical forms are equal.
2. Conformance tests and source review establish that the canonical form and
   returned label agree exactly with the pinned stable version of nauty.

The second requirement is not a theorem about nauty. The nauty source is an
external compatibility specification. The first requirement is independent
of nauty and remains a theorem even if a later release deliberately changes
the compatibility target.

The two requirements share one refinement-code coordinate system: the
specification's tree, the certificate checker, and the search
all seed a child node's refinement code with the parent's recomputed cell
count, exactly as nauty does. The declarative characterization behind
requirement 1 (the canonical key is the maximum leaf key of the unpruned
tree) does not depend on that seeding choice. Sharing it makes the
search's recorded codes directly comparable with the checker's.

## Dense scope

The first release includes:

- finite simple undirected graphs on `Fin n`;
- an ordered, nonempty list of colour cells;
- a total canonical-form operation and the label producing that form;
- a Boolean isomorphism decision and one isomorphism when one exists;
- a checked explicit isomorphism;
- positive and negative certificate checking;
- the automorphism generators the pinned traversal discovers, with the
  vertex orbits, the orbit count and the group order;
- the Mathlib-free `graph_iso` tactic for closed executable graphs;
- exact compatibility with the pinned dense nauty configuration below.

Directed graphs, loops, parallel edges, Traces, and user vertex invariants
are outside the supported scope. The dense search
proves complete automorphism generation and exact vertex orbits; see
[Automorphism generators](#automorphism-generators). Sparse graphs have
their own representation and sparse-nauty operations, specified below.
Explicit isomorphism cosets remain outside this API.

Worst-case canonical labelling remains exponential or factorial. No API in
this library claims a polynomial bound for arbitrary graphs.

## Required `hex-graph` interface

This SPEC can be implemented before a complete SPEC for every graph
algorithm, but it assumes the following `hex-graph` interface. The concrete
names may be placed in the `Hex.Graph` namespace when that library is
specified.

- `Graph n` is a finite simple undirected graph with vertices `Fin n`.
- Adjacency is executable, symmetric, and irreflexive.
- Equality compares the represented edge relation.
- A checked edge-list builder rejects out-of-range endpoints and loops,
  and removes duplicate undirected edges.
- Relabelling by a finite bijection is executable and has an adjacency
  correspondence theorem.

`Graph n` stores a dense Boolean adjacency matrix. `Graph.nbrs` materializes
a sorted duplicate-free neighbour array by scanning a row. `hex-graph-iso`
owns a private packed bit matrix used by dense refinement and canonical
comparison. The conversion is proved to preserve adjacency.
`SparseGraph n` is a separate compressed adjacency representation; neither
representation introduces a storage typeclass into `hex-graph`.

## Ordered colours

nauty calls a vertex colouring a partition and its colour classes cells. Its
colours are ordered. The first cell comes before the second cell in every
canonical labelling. An isomorphism preserves each colour index and may not
permute the cells.

The executable representation is a vector plus a proof that every colour is
used:

```lean
structure Coloring (n k : Nat) where
  cells : Vector (Fin k) n
  onto : Function.Surjective cells.get

structure Colored (n k : Nat) where
  graph : Graph n
  coloring : Coloring n k
```

These field names and this representation are the public contract.
`DecidableEq (Coloring n k)` compares only `cells`. Proof irrelevance handles
`onto`. Equality of `Colored n k` is equality of the graph and the colour
vector. This avoids equality on function fields and makes fixture comparison
kernel-reducible.

Surjectivity matches nauty's partition representation, which has no empty
cell. It also removes redundant colour counts from the public type.

- The empty graph is represented with `n = 0` and `k = 0`.
- A nonempty uncoloured graph uses `k = 1` and the constant zero vector,
  built by `Graph.singleColor` (see
  [The uncoloured surface](#the-uncoloured-surface)).
- No value of `Colored n 0` exists when `n > 0`.

The output colouring of a canonical form has contiguous cells in their
original order. If the cell sizes are `s₀, ..., sₖ₋₁`, the first `s₀` new
vertices have colour zero, the next `s₁` have colour one, and so on.

## Permutations, labels, and relabelling

The executable permutation data is an array of all vertices with a no-
duplicates proof. The library provides checked construction, identity,
inverse, composition, indexing, and extensional equality. Two wrappers make
the direction visible at use sites:

- `Perm n` maps an old vertex to its image. An isomorphism from `G` to `H`
  uses this direction.
- `Label n` stores the old vertex at each new position. This is nauty's
  `canonlab` convention.

For `l : Label n`, relabelling is defined by

```text
(relabel G l).adj i j     = G.adj l[i] l[j]
(relabel G l).coloring[i] = G.coloring[l[i]].
```

An isomorphism predicate has the mathematical direction:

```lean
def IsIso (G H : Colored n k) (p : Perm n) : Prop :=
  (forall i, H.coloring[p i] = G.coloring[i]) ∧
  (forall i j, H.graph.adj (p i) (p j) = G.graph.adj i j)

def Isomorphic (G H : Colored n k) : Prop :=
  Exists fun p => IsIso G H p
```

The actual definition should use bounded quantifiers and executable Boolean
checkers in addition to these propositional views. `checkIso` is sound and
complete for `IsIso`.

If canonical labels for `G` and `H` are `lG` and `lH`, the forward
transporter from `G` to `H` is `lH` composed with the inverse of `lG`, with
the conversions between label and forward-permutation conventions made
explicit in the implementation.

## Public operations

The canonical result keeps its form and label together:

```lean
structure CanonResult (n k : Nat) where
  form : Colored n k
  label : Label n
```

The public surface is one tier. The names in `Hex.GraphIso` are the
checked result of the pinned nauty-compatible search, run directly
with no certificate replay on the answer path, and they carry the
whole theorem surface.

```lean
def canonicalize (G : Colored n k) : CanonResult n k
def canon (G : Colored n k) : Colored n k := (canonicalize G).form
def label (G : Colored n k) : Label n := (canonicalize G).label
def findIso (G H : Colored n k) : Option (Perm n)
def isIso (G H : Colored n k) : Bool
```

`canonicalize` is total: termination follows from the strictly
increasing number of singleton cells along each individualization
path and finite branching, and worst-case running time can still be
factorial. The theorems reach it through the certificate checker
without running it: the proven replay accepts the search's own
answer on every input (`Nauty.certifyCanon?_isSome`, the theorem of
[Verified search refinement](#verified-search-refinement)), the
search is `Option`-valued only in its executable spelling and
answers on every input (`Nauty.searchResult?_isSome`), and
`canonicalize` is that answer with no fallback match
(`canonicalize_eq_certifyCanon`). The declarative canonical form
`Nauty.specCanon` is the anchor: `canon_eq_specCanon` identifies the
public form with it, and every statement below is the corresponding
`specCanon` theorem transported along that identity.

The required API theorems:

```lean
theorem relabel_label (G : Colored n k) :
    relabel G (label G) = canon G

theorem canon_iso (G : Colored n k) :
    Isomorphic G (canon G)

theorem canon_invariant {G H : Colored n k} :
    Isomorphic G H -> canon G = canon H

theorem iso_iff_canon_eq (G H : Colored n k) :
    Isomorphic G H <-> canon G = canon H

theorem findIso_sound (G H : Colored n k) (p : Perm n) :
    findIso G H = some p -> IsIso G H p

theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true <-> Isomorphic G H

theorem isIso_eq_true_iff (G H : Colored n k) :
    isIso G H = true <-> Isomorphic G H

theorem isIso_eq_false_iff (G H : Colored n k) :
    isIso G H = false <-> Not (Isomorphic G H)

theorem isomorphic_of_isIso (G H : Colored n k) :
    isIso G H = true -> Isomorphic G H
```

The biconditional compares canonical coloured graphs. It does not compare
labels: those arrays refer to different input vertex names and generally
differ for isomorphic inputs.

The supplied-permutation checker is `checkIso`. Kernel replay uses Lean's
heartbeat, recursion-depth and memory controls rather than an estimated
operation budget.

## Automorphism generators

The search discovers automorphisms as it runs: the generator trace
drives its own automorphism pruning and is recorded unconditionally.
That list is a supported output.

```lean
structure AutResult (n : Nat) where
  gens : List (Perm n)
  orbits : Array Nat
  numOrbits : Nat
  order : Nat

def autos (G : Colored n k) : AutResult n
```

`gens` is the traversal's own generator list in discovery order: the
`workperm` the pinned search records at each code-1 and code-2 leaf,
rebuilt as a `Perm n` and kept only after `checkIso` accepts it.
The list is deterministic and conformance-pinnable. It may contain a
code-2 automorphism whose orbit join changes nothing, which nauty omits
from its emitted list; completeness applies to the recorded list.
`orbits` is the vertex-orbit array `orbjoin` builds from
those generators, which is the array nauty reports; every entry is the
representative of its orbit, and `numOrbits` counts the
representatives. `order` is computed by the orbit-stabilizer
chain: individualize a vertex of a non-singleton orbit, whose
stabilizer is the colour-preserving automorphism group of the
individualized colouring, recurse on that, and multiply the orbit
lengths. Every level computes the full automorphism orbit partition, so
the product is the order of the full automorphism group. The stabilizer
factors come from separate runs on the individualized colourings.

The four fields are also available on their own, in the `Aut`
namespace: `Aut.gens`, `Aut.orbits`, `Aut.numOrbits` and `Aut.order`,
with `Aut.trace` the unchecked recorded list they start from, and
`Aut.gens_isIso` the membership theorem stated directly on `Aut.gens`.
A caller who wants only the generators takes `Aut.gens`, which runs one
traversal; `autos` computes `order` as well, and that runs one further
traversal per base point. The Mathlib wrappers take the projection they
need for the same reason.

The relation the orbit array reports:

```lean
def SameOrbit (G : Colored n k) (u v : Fin n) : Prop :=
  Exists fun p => And (IsIso G G p) (p u = v)
```

The required theorems:

```lean
theorem autos_isIso (G : Colored n k) (p : Perm n) :
    p ∈ (autos G).gens -> IsIso G G p

theorem size_autos_orbits (G : Colored n k) :
    (autos G).orbits.size = n

theorem autos_orbits_lt (G : Colored n k) (v : Nat) :
    v < n -> (autos G).orbits[v]! < n

theorem autos_sameOrbit (G : Colored n k) (u v : Fin n) :
    (autos G).orbits[u]! = (autos G).orbits[v]! ↔ SameOrbit G u v

theorem autos_complete (G : Colored n k) {p : Perm n} :
    IsIso G G p → Perm.Generated (autos G).gens p
```

Membership belongs to the checker, not to the producer. `autom?`
rebuilds each recorded array as a permutation of `Fin n` and runs the
same `checkIso` the isomorphism surface uses, against the graph and
itself, so a producer defect can only lose a generator and never admit
a non-automorphism. Orbit soundness descends from the search's own
orbit bookkeeping (`Nauty.orbjoin_orbConn`): every parent pointer is
justified by a forward word over the checked generators, and a word of
automorphisms composes to an automorphism.

`autos_complete` proves that every automorphism is a word in the returned
generators and their inverses. `Perm.Generated` expresses this membership
without a Mathlib dependency; `Aut.complete` states the same contract on
`Aut.gens`. The proof follows the search's first path and its stabilizers:
generated permutations cover each base-point orbit, and recursion generates
the next point stabilizer. Pruned children are accounted for by the actual
search trace and pruning ledger. This handles recorded code-2 automorphisms
even when their orbit join adds no new orbit relation.

Consequently the reported representatives classify the full automorphism
orbits, as the biconditional `autos_sameOrbit` states. The Mathlib bridge
provides `Aut.closure_eq_group`, `Aut.numOrbits_card`, and `Aut.order_card`:
the generated subgroup is `Aut.group G`, the orbit count is the cardinality
of its vertex-orbit quotient, and the order is its cardinality. The order
proof follows the executable individualization recursion, identifying each
individualized graph's group with the chosen point stabilizer.

These are proof-only additions. Canonicalization, unchecked traces, checked
generators, and the order computation keep their existing executable paths;
no caller computes a generation certificate. The completeness proof uses
private implementation imports. `Uncolored` retains the basic executable
API, and `UncoloredComplete` adds its generation and orbit-equivalence
theorems; the `HexGraphIso` umbrella exposes both. Conformance still compares all
four fields against nauty, while search counters remain conformance-pinned
observables. The intended automorphism tactic extends `graph_iso` to a
given permutation's automorphism property, a stated group-order fact,
and the corresponding Mathlib self-isomorphism and group-cardinality
goals. These goal forms are supported by the checker and theorems above;
the tactic implementation is separate work.

## The uncoloured surface

Colours are the general input, but most callers hold a bare `Graph n`.
The library therefore states isomorphism directly on `Graph n` and
mirrors the whole surface there, so an uncoloured caller neither builds
a `Colored n 1` at the call nor unwraps one from the conclusion.

```lean
def Graph.singleColor (G : Graph n) (h : 0 < n) : Colored n 1

def Graph.IsIso (G H : Graph n) (p : Perm n) : Prop :=
  forall i j, H.adj (p i) (p j) = G.adj i j

def Graph.Isomorphic (G H : Graph n) : Prop :=
  Exists fun p => Graph.IsIso G H p
```

The automorphism surface is mirrored too, with the same guarantees
transported along the one-cell correspondence:

```lean
def Graph.SameOrbit (G : Graph n) (u v : Fin n) : Prop :=
  Exists fun p => And (Graph.IsIso G G p) (p u = v)

def Graph.autos (G : Graph n) (h : 0 < n) : AutResult n
```

with `Graph.autos_isIso`, `Graph.size_autos_orbits`,
`Graph.autos_orbits_lt`, `Graph.autos_sameOrbit`, and `Graph.autos_complete`
the uncoloured readings of the five coloured theorems. Both coloured and
uncoloured APIs retain the one-way implication as `autos_sameOrbit_of_eq`;
callers using the old implication can use that name or apply `.mp` to
the new biconditional.

`n = 0` forces `k = 0`, so `Graph.singleColor` and every operation
below take `0 < n`. The hypothesis is an auto-parameter discharged by
`decide` or `omega`, so it is invisible at a concrete size. `decide`
comes first because it closes a literal size with a self-contained
term, where `omega` lifts an auxiliary theorem that is named in the
root namespace when the call sits in a command with no enclosing
declaration.

One equivalence carries the whole surface:

```lean
theorem Graph.isIso_singleColor_iff (G H : Graph n) (p : Perm n)
    (h : 0 < n) :
    IsIso (G.singleColor h) (H.singleColor h) p <-> Graph.IsIso G H p

theorem Graph.isomorphic_singleColor_iff (G H : Graph n) (h : 0 < n) :
    Isomorphic (G.singleColor h) (H.singleColor h) <->
      Graph.Isomorphic G H
```

The colour clause of `IsIso` is vacuous at one colour, which is what
makes this an equivalence rather than one implication. Every theorem
of the uncoloured surface is transported along it rather than
reproved, so the uncoloured operations make exactly the promises their
coloured originals make.

```lean
def Graph.canon (G : Graph n) (h : 0 < n) : Graph n
def Graph.label (G : Graph n) (h : 0 < n) : Label n
def Graph.findIso (G H : Graph n) (h : 0 < n) : Option (Perm n)
def Graph.isIso (G H : Graph n) (h : 0 < n) : Bool
```

The canonical form is the underlying graph of the coloured canonical
form, so the two agree by construction. The required uncoloured
theorems mirror the coloured ones:

```lean
theorem Graph.relabel_label (G : Graph n) (h : 0 < n) :
    G.relabel (Graph.label G h).get = Graph.canon G h

theorem Graph.canon_iso (G : Graph n) (h : 0 < n) :
    Graph.Isomorphic G (Graph.canon G h)

theorem Graph.iso_iff_canon_eq (G H : Graph n) (h : 0 < n) :
    Graph.Isomorphic G H <-> Graph.canon G h = Graph.canon H h

theorem Graph.canon_invariant :
    Graph.Isomorphic G H -> Graph.canon G h = Graph.canon H h

theorem Graph.findIso_sound :
    Graph.findIso G H h = some p -> Graph.IsIso G H p

theorem Graph.findIso_isSome_iff (G H : Graph n) (h : 0 < n) :
    (Graph.findIso G H h).isSome = true <-> Graph.Isomorphic G H

theorem Graph.isIso_eq_true_iff (G H : Graph n) (h : 0 < n) :
    Graph.isIso G H h = true <-> Graph.Isomorphic G H

theorem Graph.isIso_eq_false_iff (G H : Graph n) (h : 0 < n) :
    Graph.isIso G H h = false <-> Not (Graph.Isomorphic G H)

theorem Graph.isomorphic_of_isIso :
    Graph.isIso G H h = true -> Graph.Isomorphic G H
```

`Isomorphic.graph` and `IsIso.graph` forget the colours of a coloured
isomorphism at any `k`, and `Colored.ext_graph` recovers a `Colored n 1`
from its graph. The uncoloured equivalence relation carries the usual
`refl`, `symm` and `trans`.

The uncoloured canonical form of a graph is the graph of its coloured
canonical form, so the conformance fixtures, the benchmark corpus and
the nauty compatibility target are stated on the coloured surface only;
nothing about the uncoloured names needs separate pinning.

The public `canon` is the checked result of the nauty-compatible
search. Its theorems come from the certificate replay, which is proved
to accept the search's answer on every input. The `Nauty`
namespace holds that search and the declarative `canonSpecKey`
alongside it, and `canonSpecKey` is also the executable cross-check at
factorially feasible sizes.

## nauty-compatible individualization and refinement

The production search is derived from the pinned nauty source. Its state
contains an ordered partition, the active cells, the individualized vertices,
the refinement code at each level, the first-path and best-so-far data, and
the automorphisms and orbit information justified so far.

The following behavior is fixed before adding pruning:

1. Initial vertices occur in `(colour, original vertex)` order.
2. Equitable refinement uses the same splitter order, count buckets, cell
   order, and refinement-code arithmetic as dense nauty, including seeding
   each level's code with the current cell count.
3. Target-cell selection reproduces `targetcell` and `bestcell` for the
   configured `tc_level`.
4. Candidate vertices are individualized in the same order as nauty.
5. Refinement-code sequences are compared before canonical graphs.
6. `testcanlab` and `updatecan` define leaf comparison and partial-row reuse.
7. Equal canonical graphs use nauty's exact canonical-label tie-breaking.

The unpruned search must already produce the pinned nauty result. Later stages
add the pruning performed by the pinned default configuration:

1. comparison against first-path and best-so-far refinement codes;
2. verified automorphisms from equivalent leaves;
3. orbit pruning justified by those automorphisms;
4. short-prune and the remaining default dense-nauty return rules;
5. packed bitsets, reusable arrays, and iterative traversal where these do not
   alter the observable traversal.

Every pruning lemma states that the selected canonical form and selected
label are unchanged. Preserving only the isomorphism class is insufficient
for exact `canonlab` compatibility. Orbit data may omit true orbit relations,
which only loses pruning. It must never join vertices without a checked
automorphism proving the relation.

Both nauty configurations keep `schreier = false`, matching the pinned
defaults. Complete automorphism generation is proved without changing
that traversal. Enabling Schreier pruning would require a separate
compatibility amendment.

At a discrete node whose refinement codes agree with the first leaf,
`Nauty.classify` implements nauty's code-1 admission test:
`gcaFirst >= noncheaplevel || isautom ctx st.workperm`. Within a subtree
covered by the cheap guard, `descPath_leafRows_all` supplies the leaf-row
equality that validates the scatter permutation. The other branch checks
the permutation with `isautom` before admission. The accepted permutation
is recorded in the full generator trace and the bounded pruning workspace.

## Canonical certificates

The negative tactic cannot prove non-isomorphism by checking a proposed
permutation. It needs evidence that each reported form is canonical. The
certificate design follows Banković, Drecun, and Marić's
[proof system for graph (non)-isomorphism verification](https://arxiv.org/abs/2112.14303),
adapted to the exact ordered-colour and nauty-selection rules in this SPEC.

`Nauty.CertNode` is plain data. It records enough information to replay:

- the initial ordered partition;
- each deterministic refinement and its code;
- each target-cell choice and individualization;
- every surviving leaf and its label;
- every canonical comparison which discards a leaf or subtree;
- every automorphism used for an orbit or short-prune step;
- the selected form and label.

The checker reconstructs partitions, adjacency counts, codes, permutations,
and comparisons from the original graph. Cached counts and hashes in a
certificate are hints only and are recomputed before use.

```lean
def Nauty.certifyKey? (G : Colored n k) (budget : Option Nat := none) :
    Option (Nauty.CertNode × Nauty.Key n)

def Nauty.checkCanon (G : Colored n k) (cert : Nauty.CertNode)
    (B : Nauty.Key n) (lab : Array Nat) : Option (CanonResult n k)

theorem Nauty.checkCanon_sound
    (h : Nauty.checkCanon G cert B lab = some res) :
    Nauty.canonSpecKey G = B ∧ res.form = relabel G res.label ∧
      Isomorphic G res.form ∧ B.rows = Nauty.leafRows { g := rowsOf G } lab
```

`Nauty.certifyKey?` is the producer. It takes an optional node budget and
returns `none` on exhaustion. It does not search: the search
already makes every decision a certificate records, so the producer
records the walk's decisions and translates that record, and its cost is
one traversal rather than two. Everything the producer does is untrusted.
A wrong record can only make the checker reject, never make it accept a
wrong answer, and the tactic calls the checker before emitting anything.

`Nauty.checkCanon` is the single trusted replay. Its soundness theorem
identifies the certified key with `Nauty.canonSpecKey`, so nothing
downstream of it mentions the search. For a negative decision,
`Nauty.checkDiff` reports that two replayed canonical keys differ, and
the proof composes two `Nauty.checkCanon_sound` applications,
`Nauty.checkDiff`, and `iso_iff_canon_eq`.

The `graph_iso` tactic replays in the kernel rather than through the
`Array` definitions the compiled search runs, so each obligation has a
kernel-priced clone with an equality theorem back to the trusted one:

| declaration | obligation | soundness |
| --- | --- | --- |
| `Kernel.checkIso` | a literal permutation is an isomorphism | `Kernel.isIso_of_checkIso` |
| `Kernel.checkKey` (= `Nauty.checkKey` by `Kernel.checkKey_eq`) | a certificate replays to a claimed key | `Kernel.not_isomorphic_of_checkKeys` |
| `Kernel.rootCode` (= the head of `Nauty.canonSpecKey` by `Kernel.rootCode_eq`) | the two root refinement codes | `Kernel.not_isomorphic_of_rootCode` |

`Kernel.packRows` ties a graph's adjacency to one packed `Nat` literal,
which both negative obligations read, so a tactic call evaluates each
graph's definition once.

Certificate size and checker work are proportional to the justified search
tree. The SPEC makes no promise that negative certificates are short on every
input.

## Verified search refinement

The pruned production search refines the declarative canonical form.
This is the theorem behind the one-tier public surface, and it is a
release requirement (release condition 4 below is discharged by it).
It is proved. This section records how the proof is organized.

The statement is totality of the certificate pipeline:

```lean
theorem Nauty.certifyCanon?_isSome (G : Colored n k) :
    (Nauty.certifyCanon? G).isSome
```

where `Nauty.certifyCanon?` is the unbudgeted producer followed by the
single `Nauty.checkCanon` replay of the search's labelling. Its
content is the equality of the declarative key with the key the
search installs:

```lean
theorem Nauty.canonSpecKey_eq_tracedKey (G : Colored n k) (hn0 : 0 < n) :
    Nauty.canonSpecKey G = Nauty.tracedKey G
```

`Nauty.tracedKey` reads the selected key off `Nauty.runColoredTraced`,
and `Nauty.canonSpecKey` is the maximum leaf key of the unpruned
individualization-refinement tree, so the equality says exactly that
the prunings discard only dominated subtrees.

The `Nauty` namespace is organized by the part each concept plays:

| directory | content |
| --- | --- |
| `Nauty/Search/` | the search implementation: packed vertex sets (`VSet`), refinement, one flat `Search` state, and mutually recursive `node` and `sweep`. The direct recursion is proved equal to the policy-parameterized `Generic.node` and `Generic.sweep`. `Search.lean` retains the nauty correspondence table; `State.lean` holds that state and the primitive transitions used directly by both executable and proofs. |
| `Nauty/Spec/` | the declarative canonical form `canonSpecKey` and `specCanon`, its invariance under isomorphism (`specCanon_invariant`, `iso_iff_specCanon_eq`) and its achievement by a reachable labelling (`specCanon_iso`), with the equivariance and cell-permutation theory both proofs use. |
| `Nauty/Cert/` | the certificate data, the trusted `checkCanon` replay with `checkCanon_sound`, the untrusted trace-driven producer, and the replay spine proving the producer's certificate is accepted whenever the claimed key dominates the subtree and every recorded generator is a checked automorphism. |
| `Nauty/Policy/` | `Generic/` contains the recursion contracts. `Max/`, `First/`, `Reference/`, `Generated/`, `Canon/` and `Cheap/` contain their search-specific proofs; shared transition lemmas stay at the root. `Instance.lean` supplies the policy and the direct-recursion equalities. `KeyComplete` and `Complete` export unconditional key equality and generator completeness. See the [policy guide](../Nauty/Policy/README.md). |
| `Nauty/Generation/` | reusable reference occurrences, uniform subtrees, checked transport, cursor coverage, and stabilizer mathematics, independent of a particular recursive search. |
| `Nauty/Invariant/` | the per-event facts about the search state the induction applies at each arm: refinement-code comparison, leaf faithfulness, domination, orbit soundness, generator-store validity, cell reachability, and target-cell agreement. |
| `Nauty/Equitable/` | `refine` returns a partition equitable with respect to the exhausted active set. |
| `Nauty/SmallCell/` | the `cheapautom` theory: for an equitable partition passing nauty's cheap guard, the cell stabilizer in the automorphism group acts transitively on every cell (`stabilizer_transitive`), and every leaf of the subtree below such a node realizes an automorphism with the first leaf (`descPath_leafRows_all`). |

The public surface is then total with no fallback arm anywhere:

```lean
def Nauty.certifyCanon (G : Colored n k) : CanonResult n k :=
  (Nauty.certifyCanon? G).get (Nauty.certifyCanon?_isSome G)

theorem Nauty.searchResult?_isSome (G : Colored n k) :
    (Nauty.searchResult? G).isSome

def canonicalize (G : Colored n k) : CanonResult n k :=
  (Nauty.searchResult? G).get (Nauty.searchResult?_isSome G)

theorem canonicalize_eq_certifyCanon (G : Colored n k) :
    canonicalize G = Nauty.certifyCanon G

theorem canon_eq_specCanon (G : Colored n k) :
    canon G = Nauty.specCanon G
```

Totality transports from the certificate pipeline to the search
through `Nauty.searchResult?_eq_of_certifyCanon`, and the theorem
surface of [Public operations](#public-operations) is the declarative
form's theorem surface transported along `canon_eq_specCanon`. No
certificate is produced or replayed on the answer path. Certificates
and the replay checker remain as the proof layer for the `graph_iso`
tactic, whose kernel obligations must stay certificate-sized.

Label-level agreement is available only along this route. The checker
pins a labelling's rows, not the labelling itself, so an exhaustive
fallback that selects some other member of the automorphism coset
could not be identified with the search's label. The fallback
has to be proven unreachable, which is exactly the theorem.

No theorem in this library depends on the search being faithful
to nauty. `canonSpecKey` is a Lean definition, every statement above is
about it, and replacing the search with any other search that
computes the same key would leave all of them true. Faithfulness to
nauty 2.9.3 is requirement 2 at the top of this SPEC, and it is
established by conformance testing alone.

## The Mathlib-free `graph_iso` tactic

The library registers `graph_iso` for closed goals over executable
`Colored n k` values and over executable `Graph n` values:

```lean
example : Isomorphic G H := by
  graph_iso

example : Not (Isomorphic G H) := by
  graph_iso

example : Graph.Isomorphic G H := by
  graph_iso

example : Not (Graph.Isomorphic G H) := by
  graph_iso

example : Isomorphic G H := by
  graph_iso (maxSearchNodes := 200000)
```

An uncoloured goal is coloured with the single colour zero and its
conclusion transported back through `Graph.isomorphic_singleColor_iff`,
so both shapes run the same routes below. Both directions of that
equivalence are proof terms, so the uncoloured route adds nothing to
the kernel obligation beyond one decision of `0 < n`.

The configuration syntax is the parenthesized named syntax shown above.
The `maxSearchNodes` and `maxCertRecords` fields are optional and may
appear in either order. Both default to `100000`.

The four routes are `relabel`, `witness`, `root` and `certs`, and
`set_option trace.graph_iso true` names the one each call took.

A positive goal takes the `relabel` route when the right-hand graph is
syntactically a relabelling of the left-hand one, closing through
`isomorphic_relabel` with no kernel evaluation and no search. Otherwise
it takes the `witness` route: the compiled `findIso` search returns a
literal forward permutation under `maxSearchNodes`, and the tactic ties
each side's adjacency, colouring and the permutation to list literals
and closes the goal through `Kernel.checkIso` and
`Kernel.isIso_of_checkIso`. Search or replay exhaustion leaves the goal
unchanged.

A negative goal takes the `root` route when the two root refinement
codes already differ: the kernel obligation is `Kernel.rootDiff`, one
refinement per graph, and soundness is
`Kernel.not_isomorphic_of_rootCode`, which reads the code off the head
of the specification key. Otherwise it takes the `certs` route: the
compiled search produces a canonical-key certificate for each graph and
the tactic uses that route whenever both certificates fit the
configured search and certificate-record limits. The kernel replays the two Boolean certificate
checks and their key comparison, closing the goal through
`Kernel.not_isomorphic_of_checkKeys` (`Kernel.checkKey` twice plus
`checkDiff`, with no achieving labelling reified). `Kernel.checkKey`
(`HexGraphIso/Kernel/CheckKey.lean`) is the replay over kernel-priced
state: the labelling, the partition and the adjacency rows are
fixed-width fields packed into one `Nat` each, every step is spelled
with the `Nat` functions the kernel accelerates, and counted loops
run through one `Nat.rec` step per iteration; it is proven equal to
`Nauty.checkKey`, so the soundness theorems keep mentioning the `Array`
definitions the compiled search runs. The adjacency of each graph is
tied to one packed literal (`Kernel.packRows`), one sequential kernel
evaluation of the graph's definition per side, shared by both negative
routes. When certificate production fails or a certificate exceeds the
configured budgets the tactic reports the limit that ran out and leaves
the goal unchanged: exhaustion never proves non-isomorphism.
No result relies on compiler trust. All routes share an
irreducible kernel cost evaluating the goal's graph definitions
themselves, so family-style definitions with expensive adjacency set a
floor no route can undercut. The certificate obligations replay only
while their whole reduction closure stays exposed to the module-mode
kernel; the regression ladder in
`HexGraphIso/ModuleBoundaryTests.lean` pins that closure (it caught
missing exposure on two refinement helpers and on core's `Array.map`,
worked around per `HexBasic.OfFn` pending the upstream exposure fixes).

The library builds with `precompileModules`, so the compiled search
the tactic runs at elaboration time runs compiled rather than
interpreted whenever the library's shared objects are loaded (a
downstream `lake build`, or `lake lean` on a file; `lake env lean`
interprets). The kernel cost of the negative routes is measured by
`scripts/bench/graphiso_kernel_cost.py`, which reports type-checking
time per certificate record and its exponent in the vertex count over
the cactus corpus; its records live under `reports/bench-results/`
as `hexgraphiso-kernel-*.json`, and every change to the replay is
judged against them.

Malformed data, a failed check, an open term, or any exhausted limit leaves
the goal unchanged and reports which phase and logical limit failed. Search
exhaustion never closes a negative goal. No implementation or test uses
`native_decide`, and no theorem is introduced as an axiom.

## Manual example: the Petersen graph three ways

The first manual chapter, `HexManual/Chapters/HexGraphIso.lean`, includes one
substantial example rather than only small path and cycle demonstrations. It
defines the following Mathlib-free graphs locally from their edge predicates:

- the generalized Petersen presentation `G(5, 2)` on `Fin 10`;
- the Kneser presentation `K(5, 2)`, obtained by listing the two-element
  subsets of `Fin 5` in lexicographic order on `Fin 10` and joining disjoint
  pairs;
- the pentagonal prism on `Fin 10`.

The chapter states the positive and negative claims on bare `Graph 10`
values, through `Graph.Isomorphic`, since neither claim mentions
colours. It checks that the canonical searches compose into an explicit
vertex transporter between the two presentations,
then uses `graph_iso` to prove that the first two presentations are isomorphic.
The text explains how an outer pentagon, inner star, and spokes become disjoint
pairs. It then uses the same tactic to prove that the Petersen graph is not
isomorphic to the pentagonal prism. This negative example is
interesting because both graphs have ten vertices and every vertex has degree
three. Degree refinement alone does not settle it.

The chapter also gives the Petersen graph three ordered two-colourings with
identical cell sizes, which is where the coloured surface enters. Two
colourings mark different edges as colour zero.
`graph_iso` proves them isomorphic and returns a colour-preserving transporter.
The third marks a nonadjacent pair as colour zero. `graph_iso` proves it is not
isomorphic to either edge-marked colouring. This is the manual's compact
illustration that ordered colours constrain isomorphisms and are not merely
refinement hints.

The chapter also works the automorphism surface on the two examples it
already has. On the Petersen graph it evaluates `Graph.autos` and reports
the generator list, the single vertex orbit, and the group order 120,
reusing the family generators the chapter defines rather than introducing
a new graph, and it checks one returned generator against
`Graph.autos_isIso` so the reader sees the theorem and not only the
number. On the Latin-square encoding it evaluates `autos` on the coloured
incidence graph, where the automorphism group is the isotopy group of the
square, so the generators are the row, column and symbol permutations of
the isotopy the reader has already met; the chapter says which is which
and reports the group order. The orbit count and group order have the
exact meanings proved in [Automorphism generators](#automorphism-generators),
and conformance also compares them against nauty.

All constructors used by the chapter are ordinary Lean definitions in the
chapter or public graph operations. The example is compiled with the manual,
records explicit logical limits, and does not depend on an external nauty
installation. The Mathlib companion presents the same positive and negative
claims through `SimpleGraph`. Its requirements are stated in
[hex-graph-iso-mathlib.md](../../HexGraphIsoMathlib/SPEC/hex-graph-iso-mathlib.md#manual-example-with-mathlib).

## Manual chapter: the nauty canonical labelling algorithm

`HexManual/Chapters/NautyAlgorithm.lean` is a standalone manual chapter
titled "The `nauty` canonical labelling algorithm". It appears in the
table of contents directly after the `HexGraphIso` chapter, and the
`HexGraphIso` introduction links to it. Its subject is the function
this library computes: the canonical form and label returned by dense
nauty 2.9.3 under the pinned configuration of the
[compatibility target](#nauty-compatibility-target). No published
document specifies that function, so the chapter states it, first in
natural language with no Lean identifiers and then against the Lean
declarations, quoted through Verso's `{name}` and `{docstring}` roles
so a rename or a docstring change fails `lake build HexManual`. It
also states its own epistemic status, mirroring the two correctness
requirements at the top of this SPEC: the chapter agrees with the Lean
implementation by theorem and by the Verso build, and the Lean
implementation agrees with nauty 2.9.3 by conformance testing, not by
theorem.

## nauty compatibility target

The first compatibility target is nauty 2.9.3, the stable release current when
this SPEC was written:

- source: <https://users.cecs.anu.edu.au/~bdm/nauty/nauty2_9_3.tar.gz>;
- SHA-256:
  `9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b`;
- manual: <https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf>.

The development monorepo vendors the dense-nauty subset of this archive at
`vendor/nauty-2.9.3` (unmodified files; per-file hashes in that directory's
README), so conformance and benchmarking build against the pinned source
without a network fetch.

The tarball's `nauty.c`, `nautil.c`, `naugraph.c`, and `nauty.h` are normative
for implementation details. The manual and McKay and Piperno's
[Practical graph isomorphism, II](https://arxiv.org/abs/1301.1493) explain the
algorithm, but they do not specify all code-level choices needed for exact
output compatibility.

The oracle uses 64-bit dense `densenauty`, `m = SETWORDSNEEDED(n)`, and
`DEFAULTOPTIONS_GRAPH`. It changes only the fields required for canonical
labelling and a caller-supplied partition:

| field | value |
| --- | --- |
| `getcanon` | `1` |
| `digraph` | `FALSE` |
| `defaultptn` | `FALSE` |
| `writeautoms`, `writemarkers` | `FALSE` |
| `tc_level` | `100` |
| `userrefproc`, all user callbacks | `NULL` |
| `invarproc` | `NULL` |
| `mininvarlevel`, `maxinvarlevel`, `invararg` | `0`, `1`, `0` |
| `dispatch` | `dispatch_graph` |
| `schreier` | `FALSE` |

`getcanon = 1` is used because it is the documented canonical-labelling mode.
The 2.9.3 header still marks `LABELONLY = 2` as unimplemented, so the oracle
does not claim that mode avoids group work.

For every input, `lab` is initialized by increasing colour and then increasing
original vertex. `ptn` ends exactly at the last position of each colour cell.
Passing no active set to `densenauty` makes it activate every initial cell.
The oracle serializes the upper-triangle bits in row-major order and the
integer `lab` array. It never compares raw C setwords.

The compatibility target is frozen per SPEC revision. Advancing to a later
stable nauty release requires a deliberate SPEC amendment, review of the new
source, and full conformance. If the observable form or label changes, that is
a breaking public change. The project keeps no compatibility branches for old
nauty versions.

## Conformance

The oracle follows [the project oracle protocol](../../SPEC/testing.md#adding-a-new-oracle).
A Python JSONL driver rebuilds each original graph and partition and calls a
small project-owned C program compiled against the vendored nauty source in
`vendor/nauty-2.9.3`: unmodified files from the pinned archive,
version-controlled in the development monorepo with per-file SHA-256 hashes
recorded in that directory's README, alongside the upstream `COPYRIGHT` and
`LICENSE-2.0.txt` (Apache 2.0) files. The compiled program is cached keyed by
the SHA-256 of its source together with every vendored file it links. A
compile failure, nauty error, or output mismatch fails the run. The vendored
source and both nauty comparators are development tooling only: they are not
managed paths of any released repository, and the production library never
links nauty.

Each record contains the original graph, colour vector, Hex canonical form,
Hex label, search counters, and schema version. The oracle independently
computes and compares:

- ordered colour-cell sizes;
- the canonical upper-triangle adjacency bits;
- every entry of `canonlab`.

A second record kind, `graphisoautos`, pins the automorphism surface. It
carries every field of a `graphiso` record, so a consumer reading the
whole stream for canonical forms needs no knowledge of the second kind
and the canonical comparisons above run on it too, and it adds the
recorded generator list,
the generator count the search reports, the orbit array, the
orbit count and the group order. The shim collects nauty's own generators
through `options.userautomproc`, so the comparison is against the
traversal's emissions rather than a recomputation, and it also reports
nauty's `orbits`, `stats.numorbits` and `stats.grpsize`. The oracle
compares:

- the orbit array, entry by entry;
- the orbit count;
- the group order, as `grpsize1 * 10 ^ grpsize2`;
- the generator count, against the number of generators nauty emitted;
- nauty's generator list, which must appear in the recorded list as an
  ordered subsequence, and must agree with it entry by entry whenever
  the two have the same length.

The subsequence relation rather than equality is what the two emission
rules permit. nauty emits a generator at every code-1 leaf and at every
code-2 leaf that grows the orbit partition, while the recorded trace
takes both kinds unconditionally, so the trace can carry an
orbit-redundant code-2 automorphism nauty discards. Both lists come from
one traversal, so nauty's is always the subsequence of the trace at the
emitting events, and the generator count pins how many those are. The
recorded list itself is pinned by the committed fixture, so a change in
the traversal is a fixture diff even where the subsequence relation
alone would tolerate it.

The driver must not canonicalize Hex's answer before comparing it with nauty.
Doing so would test only isomorphism of the outputs and could conceal a wrong
canonical representative.

The committed merge-CI fixture is at most 16 MiB and contains:

- all 1,100 labelled uncoloured graphs for `0 ≤ n ≤ 5`;
- all 4,912 graph and ordered-surjective-partition pairs for `0 ≤ n ≤ 4`;
- deterministic relabellings and colourings of named larger examples;
- positive and negative isomorphism pairs;
- graphs whose automorphism groups are trivial, small, and large.

The counts include labelled graphs. The 1,044 commonly listed graphs on seven
vertices are unlabelled isomorphism classes and are not this fixture count.

The campaign adds all 32,768 labelled graphs at `n = 6`, larger
deterministic random cases, and the hard families below. The existing CI
oracle step runs it against the pinned nauty comparator on every change.
The emitters share the corpus in `conformance/HexGraphIso/Cases.lean` and
read labels and canonical forms from the public operations.

`hexgraphiso_emit_trace` records the full traversal for the fixture,
automorphism and campaign corpora, plus the 120-vertex pruning regression.
`scripts/oracle/graphiso_trace.py` compares those records with the committed
`conformance-fixtures/HexGraphIso/trace.jsonl.gz`. It checks labels, canonical
rows, all seven statistics, generators in discovery order, path codes, final
orbits and normal root exit. Missing, duplicate, additional and changed cases
fail with the case and differing field. The metadata records the source
commit, case counts, corpus digest and trace digest.

CI checks the expected records without rewriting them. To review an intentional
traversal change, emit a candidate and run:

```sh
lake exe hexgraphiso_emit_trace > /tmp/graphiso-trace.jsonl
python3 scripts/oracle/graphiso_trace.py /tmp/graphiso-trace.jsonl
# Explicitly replace expectations only alongside the intended change:
python3 scripts/oracle/graphiso_trace.py /tmp/graphiso-trace.jsonl \
  --record --source "$(git rev-parse HEAD)"
```

The committed trace records are a regression baseline. The nauty oracle
independently checks the canonical answer and graph-isomorphism results.

Property checks independent of nauty include:

- `relabel G (label G) = canon G`;
- invariance under deterministic random relabelling;
- colour preservation and contiguity;
- agreement with the declarative canonical form at factorially feasible
  sizes: `Nauty.specCanon G = canon G` and the isomorphism verdict read
  off `Nauty.canonSpecKey`, which is the only cross-check of the public
  answer this library still carries;
- agreement of the public traced output and internal return control with
  the frozen records on every fixture, campaign and pruning-regression case;
- rejection of a changed edge, colour, permutation entry, refinement record,
  automorphism, prune record, leaf comparison, or difference position in a
  certificate;
- search-node and certificate-record exhaustion is inconclusive; resource
  exhaustion during kernel replay leaves no accepted theorem.

## Reproducible generators

There is no single maintained nauty benchmark collection. The published
nauty and Traces experiments use families from the bliss benchmark
distribution. This project reproduces the mathematical constructions instead
of vendoring an archive with unclear redistribution terms. The family choices
are informed by the
[Traces performance pages](https://pallini.di.uniroma1.it/StronglyRegular.html)
and the graph classes generated by nauty's `genspecialg`.

All pseudo-random generation uses SplitMix64 with wrapping `UInt64`
arithmetic:

```text
state := state + 0x9E3779B97F4A7C15
z := state
z := (z xor (z >> 30)) * 0xBF58476D1CE4E5B9
z := (z xor (z >> 27)) * 0x94D049BB133111EB
output := z xor (z >> 31)
```

The corpus seeds start with `0x243F6A8885A308D3` and
`0x13198A2E03707344`. `nextBelow` uses rejection sampling rather than `%`, so
the generator is independent of modulo bias and implementation language.

- `G(n, 1/2)` consumes one low bit for each pair `(i,j)` with `i < j` in
  lexicographic order.
- Random relabelling uses Fisher-Yates from the last array position down.
- An onto `k`-colouring starts with `i mod k` and shuffles that vector.
- A random cubic graph shuffles three copies of every vertex, pairs adjacent
  entries, and rejects a trial containing a loop or duplicate edge. The next
  trial continues the same SplitMix64 stream. Only named seeds which terminate
  under the recorded trial cap enter the corpus.

The deterministic families are:

- empty, complete, path, cycle, complete bipartite, complete multipartite,
  circulant, and repeated-component graphs;
- grids, hypercubes, Johnson, Kneser, triangular, lattice, and Paley graphs;
- incidence graphs of cyclic Latin squares, Sylvester Hadamard matrices, and
  projective planes over small prime fields;
- CFI/Fürer pairs over `K4`, the triangular prism, and the cube;
- Miyazaki and multipede instances from their published constructions;
- ordered-colour variants which expose or break natural symmetries.

Each generator has a mathematical definition, parameter validation, and a
stable vertex-numbering rule in its module docstring. The initial parameter
manifest includes:

| family | parameters |
| --- | --- |
| basic and random | `n = 8, 12, 16, 24, 32, 48, 64, 96, 128` |
| grid | side `4, 6, 8, 12, 16` |
| hypercube | dimension `3` through `8` |
| Johnson and Kneser | ambient size `5` through `16`, supported `k` |
| Paley | `q = 13, 17, 29, 37, 53` |
| Latin | order `4` through `10` |
| Hadamard | order `8, 16, 32, 64` |
| projective plane | `q = 2, 3, 5, 7` |
| CFI | `K4`, triangular prism, cube |

Large rungs stop at the existing benchmark wallclock limit. The manifest is
still recorded even when a retained implementation cannot complete its upper
rungs.

## Benchmarks

The Mathlib-free benchmark driver registers:

- `Nauty.canonSpecKey`, the unpruned declarative key, on factorially
  feasible sizes;
- public `canonicalize`, `findIso`, and `isIso`;
- the automorphism surface: the generator list and the vertex orbits,
  which cost one traversal, and the whole `autos` result including the
  orbit-stabilizer chain for the group order, which costs one further
  traversal per base point, so the gap between the two registrations is
  the price of the order;
- an automorphism agreement check, which fails whenever a returned
  generator is not accepted by `checkIso` against the graph itself or
  the orbit array is not constant on the orbits it records; the
  comparison against pinned nauty's own generators, orbits and
  `grpsize` lives in conformance, which has the external nauty;
- dense conversion, one complete refinement, relabelling, canonical graph
  comparison, certificate generation, and certificate replay;
- the pinned nauty comparator through a benchmark-only in-process FFI
  binding (`Hex.BenchOracle.Nauty` over
  `Hex/BenchOracle/ffi/nauty_canon.c`), statically linked against the
  vendored nauty 2.9.3 source in `vendor/nauty-2.9.3`, following the FFI
  pattern of
  [benchmarking.md](../../SPEC/benchmarking.md#external-comparators). The
  vendored source and the comparator are development-monorepo tooling
  only and ship with no released library.

A comparator reports the time of the thing it stands in for, so nothing
it does that nauty does not may sit inside a timed region. Marshalling a
graph across the FFI boundary and reading a canonical form back are both
`O(n²)`, so the comparator splits them off: `prepare` marshals, and is
called before the timer starts, `canonPrepared` is the timed call and
decodes only the `O(n)` labelling and the node count, and the canonical
form comes back packed one bit per entry and is compared with `sameForm`
rather than rendered. A driver that calls `canon` inside a timing loop is
measuring the binding, not nauty; on the family sweeps that mistake
inflated nauty's reported time by a median factor of three.

Every canonicalization result is hashed from its ordered cell sizes,
upper-triangle adjacency bits, and label. `compare` therefore checks exact
result agreement as well as timing. The nauty comparator is `gating` in the
terminology of [benchmarking.md](../../SPEC/benchmarking.md#external-comparators), but
the first release sets no speed-ratio requirement. Its required result is
exact output agreement.

The registrations report wallclock, allocation, result hash, visited nodes,
refinement calls, canonical updates, automorphisms checked, branches pruned,
certificate records and bytes. `relabel` and graph
comparison declare quadratic bit-matrix models. A full dense refinement
declares a conservative cubic model. Canonical search declares no polynomial
model in `n`. Reports use node count and per-node work to explain its cost.
Certificate replay reports measured time and allocation alongside graph and
certificate sizes.

Merge CI runs a small deterministic subset and keeps the complete `Bench
verify` invocation inside its existing time limit. Hard families and full
nauty timing comparisons are collected manually under the shared-host policy.

The published cactus figures must stay current with the code. The
per-instance sweep data lives under `reports/bench-results/` keyed by
a content fingerprint of the source it measured, alongside the
manifest that fingerprint hashes; the figures under `reports/figures/`
are rendered from it, and any change to hex-graph-iso implementation
source must regenerate both in the same pull request
(`scripts/bench/graphiso_cactus_sweep.sh` does the whole
regeneration). `scripts/bench/check_graphiso_sweep_freshness.py` is
the required check: it fails whenever the implementation, the graph
substrate, the sweep driver, or the plot script differs from what any
committed sweep measured. The relevant set is deliberately tight and
regeneration takes minutes, so this family declares no exemption
directory at all: re-measuring is the only way past the check, with the
one exception that the check establishes for itself rather than taking
on trust, a `.lean` path whose two versions are equal once their
comments are removed. Editing a docstring under `HexGraphIso/` therefore
costs no sweep, while any change to code or to indentation does. The
fingerprinting mechanism is shared with the other published figure
families; see [SPEC/benchmarking.md](../../SPEC/benchmarking.md)
§Figure freshness.

The recorded sweep also fixes the per-node asymptotics. Because the
search visits nauty's tree node for node, the hex/nauty wallclock ratio
is a per-node constant factor, and the only way the implementation can
fall behind nauty asymptotically is for that factor to grow with `n`:
an elementwise loop over vertices where nauty runs a word operation
shows up as a larger exponent in a power-law fit of per-node cost
against `n`. `scripts/bench/graphiso_pernode_fit.py --check 0.2` is the
required check that prevents this: it fits `cost per node ~ n^e` per
family for hex and for nauty from the most recent recorded sweep and
fails when, on any family with at least five sizes, the hex exponent
exceeds nauty's by more than `0.2`. It is a growth check, not a
constant-factor check: a slowdown uniform in `n` is the per-library
bench's business. The vertex sets of the search are packed sixty-three
vertices to a word (`Nauty.VSet`), so every set operation is a loop
over `⌈n/63⌉` limbs, the same shape as nauty's `setword` loops.

The `search` mode of `hexgraphiso_cactus` measures raw canonical search
on the same instances as the public-pipeline sweep. Its columns are
`search_ns`, `nauty_ns` and `nodes`. The `read run` mode uses the same search
timing column for external corpora. `scripts/bench/graphiso_compare.py`
compares explicitly supplied baseline and candidate files for the same
operation. It requires matching family names, case names and vertex counts,
reports candidate/baseline time ratios, and lists changed node counts
separately. `--require-same-nodes` rejects traversal changes. Historical
column interpretation is confined to `graphiso_archive.py`, which does not
rewrite the recorded evidence. Named-case agreement assumes the same corpus
generator; source provenance must accompany comparisons across revisions.

`bench/HexGraphIso/Profile.lean` profiles raw search, trace production,
certificate translation, replay and public canonicalization separately on
paley61, kneser72 and circulant64. The allocation and CPU profiling tools
remain available for investigating unexpected results. Comparisons on the
shared host retain every completed sample and record placement and activity
as context. They do not wait for a quiet machine.

Recorded sweeps accumulate: each regeneration adds its data,
tactic-timing snapshot, and a `.meta.json` (fingerprint, host, date,
label) under `reports/bench-results/` without removing predecessors.
A change to the instance corpus itself is a series break: it lands as
its own pull request whose frame label says so, and curve comparisons
(the before/after tables, the animation's fixed axes) are only
meaningful between sweeps on the same corpus. The first such break
adds the irregular negative pairs, whose absence had made every
corpus negative regular and the separator tiers invisible.
The second break extends every deterministic family to large hard
instances up to the nauty comparator's `n ≤ 255` bound (Paley to 229,
Kneser/Johnson to `m = 22`, hypercube to `q7`, circulants and the
random ladder to 255, grids to 15×15), adds the Latin-square family
with the classic strongly regular negative `paley25` versus `latin5`
at shared parameters `(25, 12, 5, 6)`, and adds same-degree regular
and vertex-transitive negatives at scale; large negatives whose
kernel replay exceeds the tactic timeout count as unsolved in the
tactic curve, which is the honest frontier of that tier. nauty
cross-checks for the new sizes run in the streamed campaign, not the
committed fixture set, keeping merge-CI oracle time unchanged.
Every pull request that improves the measured performance of any
layer (canonical labelling or tactic) posts a before/after comparison as a
pull-request comment: `scripts/plots/hexgraphiso-before-after.py`
renders the overlay figure and prints the per-layer markdown delta
table from two recorded sweeps, the figure is committed under
`reports/figures/` and embedded in the comment by its raw URL at the
pull request's head commit.
`scripts/plots/hexgraphiso-cactus-animation.py` assembles the
accumulated sweeps, in recorded-date order with fixed axes, into
`reports/figures/hexgraphiso-cactus-animation.gif`.

The tactic has fresh-module probes for reification, compiled search, literal
elaboration, kernel replay, and the complete tactic. Before release, the
following cases must close within their logical limits:

- a positive random `n = 12` pair related by a recorded relabelling;
- a negative pair from the two recorded `G(12, 1/2)` seeds;
- positive and negative ordered-colour pairs at `n = 10`;
- a scheduled negative CFI pair under separately recorded larger limits.

Measured wallclock requirements are added only after these probes exist and
must satisfy the repository's matched fresh-build protocol. Compile-time toy
examples alone do not complete the tactic milestone.

## Release conditions

Each release preserves the following guarantees and checks:

1. No `sorry`, axiom, or `native_decide` occurs in the library or tactic
   correctness path.
2. The declarative biconditional `Nauty.iso_iff_specCanon_eq` and the
   public biconditional `iso_iff_canon_eq` are both complete.
3. `Nauty.checkCanon_sound` has the conclusion stated above.
4. The pruned search is proved to compute the declarative canonical key
   (`Nauty.canonSpecKey_eq_tracedKey`). Operational output agreement is
   checked separately by the frozen trace and nauty corpora.
5. The exhaustive merge fixture and extended `n = 6` campaign agree exactly
   with nauty 2.9.3. Both legs run in merge CI, together with the complete
   frozen traversal records. Historical measurements retain their provenance
   in the [evidence archive](../../reports/hex-graph-iso-evidence.md).
6. The non-toy positive and negative tactic cases replay through the kernel.
7. The benchmark driver reports the declarative key, the public
   operations, the automorphism surface, the certificate stages and the
   nauty comparator without importing Mathlib.

Complete automorphism generation and exact orbits are required for both
representations. Checking each returned permutation establishes soundness;
the separate completeness theorem accounts for every automorphism through
the search and its stabilizers.

## Sparse graphs and sparse nauty

The native executable, total coloured canonicalization and isomorphism-search
operations, and the proof surface described below are implemented.
`searchResult?` is proved to succeed unconditionally and to return exactly the
total API's relabelled graph and label. Production maximum correctness,
canonical invariance and decision completeness are proved, including the
empty public graph. Complete automorphism generation, exact orbits and group
order, and literal fresh/cached refinement agreement are proved. The canonical
certificate checker, unlimited expansion producer and equivalent kernel replay
are proved, as is certified canonical-result packaging with exact direct-result
agreement. Checked automorphism records and unlimited compact production are
proved, including equivalent literal replay. Native search-node and certificate
production limits are integrated into the proof backend. Public sparse tactic
dispatch and imported Mathlib replay are integrated, and all required kernel,
conformance, build, trust and performance checks pass. Kernel replay has no
operation counter or estimated cost limit. The following contracts describe
the completed library and its proved theorem surface.

### Representation and public operations

`Hex.SparseGraph n` represents a simple undirected graph on `Fin n` by
compressed adjacency arrays: `n + 1` offsets and a flat array of neighbours.
The first offset is zero, offsets are nondecreasing, and the last offset is
the neighbour-array length. Each row is strictly increasing, has no diagonal
entry, and contains the reverse of every listed edge. The representation
uses `O(n + |E|)` storage. Equality is equality of the represented adjacency
relation, so duplicate or reordered input edges cannot change equality.

The checked edge builder rejects loops and endpoints outside `Fin n`,
normalizes orientations, and removes duplicates. General edge input may
require `O(|E| log |E|)` sorting. Neighbour access and degree read the compressed
rows; relabelling maps edges and normalizes rows without building a matrix.
The compiled relabeller uses proved equivalent row normalization and packing.
For row length `d` with `n ≤ 8d`, a temporary membership array
emits mapped neighbours in vertex order; other rows retain merge sort.
There is no minimum graph order for this replacement.
The vertex scan is therefore bounded by the row's work, rather than adding
an unconditional quadratic scan on sparse inputs. Packing appends each row
directly into the neighbour array and records its starting offset in the same
pass. Both replacements have equality theorems for their original definitions.
Explicit `Graph.toSparse` and `SparseGraph.toDense` conversions preserve
adjacency and isomorphism. Conversion from a dense matrix inspects `n²`
entries, and materializing a dense result uses `n²` storage.

`Hex.GraphIso.Sparse.Colored n k` pairs a sparse graph with the existing
`Coloring n k`. It shares `Perm`, `Label`, ordered-colour semantics, and
logical limit types with the dense API. Sparse graphs have their own
`canonicalize`, `canon`, `label`, `findIso`, `isIso`, permutation checker,
`autos`, and `Aut` projections, with sparse results. The bare `SparseGraph`
surface wraps the coloured operations, including the empty graph with zero
colours. The representation determines the search engine; no runtime switch
between engines, including a switch based on density, is part of this contract.

The canonicalization, soundness, completeness, generator-generation, exact
orbit, and group-order theorems stated for dense graphs also apply to the
sparse operations. Sparse results are computed directly by the sparse Lean
search, without dense fallback or mandatory certificate replay.

Conversions need not commute with canonicalization. On vertices `0..3`
with edges `{0,3}` and `{1,2}`, the pinned dense label is `[0,3,1,2]` and the
sparse label is `[0,1,2,3]`; their canonical adjacency matrices differ.
Canonical forms are compared within one representation. Isomorphism
verdicts agree across explicit conversions.

### Compatibility and executable structure

The sparse target is `sparsenauty` from the same vendored 2.9.3 archive and
SHA-256 as the dense target. Normative sources additionally include
`nausparse.c`, `nausparse.h`, and `sorttemplates.c`. Initialize
`DEFAULTOPTIONS_SPARSEGRAPH`, with `getcanon = 1`, `defaultptn = FALSE`,
`digraph = FALSE`, `tc_level = 100`, `invarproc = NULL`, and
`schreier = FALSE`. Other options retain their defaults. Passive oracle
callbacks may record diagnostics, generators, and level indices without
changing search decisions. Vertices initially occur in increasing colour
then original-vertex order; input neighbour lists are sorted; passing the
null active set activates every initial cell. The pruning workspace holds
500 pairs and overwrites the last slot when full.

The port shares nauty's node/sweep traversal and representation-independent
partition, orbit, and return operations. Its graph dispatch supplies the
sparse refinement, target selection, automorphism test, canonical comparison,
and canonical update. Sparse conformance is not defined by agreement with
the dense engine. Every executable source decision has a correspondence
entry, including the following sparse-specific behaviour:

- The active-cell array checks its first ten entries for a singleton,
  otherwise pops its last entry; touched cells are processed in sorted order.
- At levels at most two, a single active singleton and at most `n / 8`
  cells trigger `distvals` refinement. Unreachable vertices have distance `n`.
- Singleton splitting, count splitting, fragment activation, largest-fragment
  ties, and `MASH`/`CLEANUP` reproduce the C ordering and arithmetic.
- Indirect sorting preserves the upstream permutation of equal-key entries,
  including its small-partition and median-selection cutoffs.
- Sparse target selection includes its own nontrivial-join calculation,
  valid hints, and the first nontrivial cell beyond `tc_level`.
- Canonical rows compare by degree first, preferring smaller degree, then
  by the first differing neighbour, preferring adjacency there. Canonical
  update preserves the prefix of already equal rows.

Working adjacency and canonical stores remain sparse. Reusable counting,
marking, and queue arrays prevent a dense scan for each splitter. Sorting
public canonical rows normalizes storage only; it does not change the
canonical label or run canonicalization again.

The working input view shares the native offset and `Fin n` neighbour arrays;
reading a neighbour erases its proof without allocating a converted adjacency
array. Initial colour buckets similarly read the native colour array directly.
The canonical store remains an array of raw neighbour numbers in nauty's order.

Refinement retains counts and generation marks across nodes. Vertex-to-cell
indices and cell endpoints are rebuilt on entry, maintained at every split,
and reused by target selection. Individualization and partition recovery
invalidate the cached indices. An empty active set leaves the cache invalid
and uses independent target-cell scanning. Target selection may reuse the
count array only because subsequent refinement clears every first-touched
cell before counting its neighbours; generation stamps never reset between
nodes. No stored count or index is a new search heuristic.

Touched-cell starts retain ascending numeric order. For arrays of at most
three entries, compiled sorting uses direct comparisons; larger arrays keep
the existing merge sort. `sortCells_eq_fast` proves equality for every input
array, including repeated entries. This replacement does not alter the
separate indirect count sort or its tie order.

The source correspondence is:

| Lean module or operation | nauty 2.9.3 source |
|---|---|
| `Nauty.Sparse.Graph`, native input view; `Rows`, raw canonical rows | `nausparse.h`: `sparsegraph`, unweighted simple-graph configuration |
| `Sparse.isautom`, `testcanlab`, `updatecan` | `nausparse.c`: `isautom_sg`, `testcanlab_sg`, `updatecan_sg` |
| `Sparse.distvals` | `nausparse.c`: `distvals` |
| `Sparse.Sort` | `sorttemplates.c` instantiated as `sortindirect`, `SORT_OF_SORT = 3` |
| `Sparse.sortCells`, proved small-array replacement | `nausparse.c`: ascending ordering of touched-cell starts in `refine_sg` |
| `Sparse.RefineSt`, `indexCells`, `splitCounts`, `splitSingleton`, `splitNontrivial`, `refineWith`, `refine` | `nausparse.c`: initialization, distance branch, singleton/count branches, and active loop of `refine_sg` |
| `Sparse.bestcell`, `bestcellCached`, `targetcell`, `maketargetcell`, `maketargetCached` | `nausparse.c`: `bestcell_sg`, `targetcell_sg`; shared target-cell materialization |
| Shared `cheapautom` | `nausparse.c`: `cheapautom_sg`, identical partition-only undirected test |
| `Sparse.Search`, generic `node`/`sweep`, `SearchState` | sparse dispatch into `nauty.c`: `firstpathnode`, `othernode`, `processnode`, and shared search bookkeeping |
| `Sparse.initialPartition`, `initialPartitionWith` | ordered initial partition supplied by the caller, stable within each colour |
| `Sparse.finish`, checked label, native relabelling | pending canonical-row update and public result construction; public row normalization occurs after the search |

Generation marks use unbounded natural numbers. They preserve the equality
tests performed by C's resettable mark arrays without an overflow branch.
Array loops have explicit bounds: each distance-queue entry represents a
new vertex; each refinement activation is initial or charged to a new cell;
each sort partition removes a nonempty pivot class. Their proofs must
establish that these bounds never truncate a valid run.

The sparse proof surface is imported by `HexGraphIso.Sparse`. Its primitive
contracts include inverse scatter and inverse-label direction (`Inverse`),
packed-row cursor bounds and partial canonical storage (`Rows`), fixed
allocation sizes and the undirected fixed-vertex omission (`GraphProps`),
soundness and completeness of the executed sparse automorphism test (`Autom`), and
permutation preservation for the exact insertion, partition, and indirect
sorts (`SortProps`). `Sort.indirect_perm` assumes the input segment is inside
the array; `partition_bounds` proves that the work stack stays inside it.
`SortOrder` proves sorted indirect keys for the executed insertion branch,
unchanged entries outside that branch's segment, and membership of both
median-of-three and median-of-nine pivots in their nonempty source segment.
`SortPartition` proves that the executed partition's two recursive fragment
lengths have strictly smaller sum than the original nonempty segment and
that its swaps preserve the exterior. `SortStack` proves
`Sort.indirect_induction` for the actual bounded work-stack loop with an empty
final stack: total pending segment length decreases at every processed entry,
so the fixed iteration bound cannot truncate pending work. Its corollaries
prove unchanged exterior and permutation preservation of the selected segment.
`SortBlocks` and `SortFinal` establish the final partition's strict lower,
equal-pivot, and strict upper regions, including scan exhaustion and the
literal block swaps. `SortSorted` proves `Sort.indirect_sorted` by composing these contracts
through the executed stack: every valid segment is sorted by its indirect
keys, including repeated keys and both pivot thresholds.

`BfsRun` proves `distvals_correct`: the executed packed-adjacency BFS
computes shortest paths from every valid root. Every finite value has an
attaining walk and is at most every walk length; the sentinel `n` occurs
exactly at unreachable vertices. Its proof tracks unique queue entries,
allocation bounds, first discovery, completed edge scans, and the distance
band of the pending frontier. Both queue exhaustion and the early exit when
all vertices are discovered imply the same contract. The root has distance
zero, and `distvals_relabel` proves equivariance despite changes in queue and
neighbour order. The primitive requires a valid root; order-zero graphs are
handled by the search entry point without invoking BFS.

`Update` proves that the executed `updatecan` loops install native relabelled
adjacency from a checked label and a valid shared prefix. The proof tracks
the allocated buffer, every copy cursor, and the terminal row offset; rows
are permutations of the normalized target rows, without a sorting assumption
on the working store. It also proves literal preservation of entries before
the shared prefix boundary. Native relabelling preserves each corresponding
degree and the total neighbour allocation, so installation from the initial
blank buffer has the same guarantee, including order zero.

`CompareKey` proves `testcanlab_fst` and `testcanlab_eq_zero`: the executed
comparison returns the sparse graph-key sign, and a tie is exactly equality
of the normalized native graphs. `Compare.Result` identifies the first
unequal row, with equal preceding rows, or the terminal index `n` for a tie.
The proofs track all packed-row cursors, generation marks, and the least
unmatched neighbour through the actual comparison loops. The working rows
may be unsorted. `ComparePrefix` proves that the returned prefix is valid
for candidate installation when its edge allocation matches the store;
this allocation equality follows automatically when comparing two labels
of the same graph. `testcanlab_update` composes comparison and installation,
including order zero, without an additional shared-prefix hypothesis.

`Nauty.Sparse.isautom_iff` in `Autom` proves that a raw image
array tied entrywise to a typed permutation passes exactly when that permutation
preserves adjacency. The proof covers degree checks, generation freshness,
marked row images, rejection, and skipped fixed vertices. Colour preservation
is a separate search invariant.

`IndexRun` proves that the actual bounded `indexCells` loop visits every cell
of a closed partition with a bounded injective labelling. `Index.Valid`
describes its endpoints and vertex-to-cell indices, with `n` precisely as
the singleton-cell value. `IndexProps` derives the array bounds and containing
cell from each nonsentinel lookup. `Scratch.Valid` records allocation sizes,
generation bounds, and cache validity conditional on the indexed flag.
`Scratch` proves that target selection preserves those invariants while
borrowing the count array; invalidation permits a changed labelling and
partition. `TargetBest` proves the executed cached selector's complete score
sequence and selection fold, including cell-walk exhaustion, first-touch
initialization, repeated neighbours in a joined cell, and clearing between
representative vertices. `TargetMaximum` and `TargetCache` prove the first
maximum rule and independence from arbitrary initial hit values and unused
cache entries. Joins include the selected cell itself. `TargetFresh` follows
the fresh selector's rank scatter, parallel cell sizes, neighbour passes, and
selection fold to prove the same score sequence and first maximum.
`bestcellCached_eq` gives fresh/cached agreement even for empty partitions.
`TargetDispatch` proves that each dispatch arm selects a nontrivial cell when
one exists. `maketargetCached_eq` gives the exact position, vertex set, and size
for admissible scratch, including hints, the depth cutoff, and invalidation.
Refinement preserves scratch admissibility. Search must supply it at every
reachable call. Complete code and ordered-cell refinement equivariance is
proved by `refineWith_equiv` below.

`RefineBudget` and `SplitBudget` prove directly that each splitter adds at most
one activation per new cell, including distance splitting and replacement of
the largest fragment. `ActiveScan` describes the ordered, duplicate-free packed
active-set walk. `refineWith_saturated` in `RefineFuel` proves that the actual
`n`-iteration refinement loop reaches an empty queue or its cell-count stopping
condition, provided the initial active cardinality is at most `numcells`.
This operational exhaustion result combines with exact cell accounting and
certificate preservation below to establish equitability.
`CountFrame` proves that all count-splitting branches preserve the hit and mark
arrays, generation stamp, cache flag, and label, partition, and index array
sizes. `CountValid` supplies the updated index-content contract described below.
`ScratchSearch` composes this with persistent scratch bounds and proves the
actual search storage invalidation valid for an individualized or recovered
partition. Canonical-row installation preserves the current scratch validity.
`CountPerm`, `CountOutside`, and `CountCells` prove that the actual count splitter
permutes labels only inside its nonempty bounded cell window. When that window
is a cell of the incoming partition, every old cell retains its vertex multiset.
The proof accounts for sequential source reads and coinciding insertion cuts,
and uses the executed indirect sort's permutation and exterior theorems.
`CountOrder` proves that the executed splitter orders the entire cell by hit
values when its initial key is below the `n + 2` second-minimum sentinel.
`Minima` and `MinimaSort` follow the equal-count scan, the five insertion arms,
and sorting of the larger-count tail. `CountPartition` and `CountPattern` prove
that the executed count splitter writes exactly the boundaries between unequal
adjacent counts, retaining every other partition value. This includes the
existing tail-loop fuel bound. Native neighbour counting and shortest paths
supply the local count and distance bounds. `CountRuns` identifies output cells with maximal constant-count
runs and proves that cells are only subdivided inside the original window.
`SortedKeys` proves uniqueness of the sorted key sequence and its literal
partition array. `CountClasses` identifies the exact vertex multiset of each
fragment by filtering the original cell by count. `CountInvariant` and
`CountTransport` prove ordered partition and cell-content agreement under
within-cell permutations and vertex renaming. Other scratch contents may
differ. `MinimaUnique` identifies both minimum keys and cut positions from
the input count multiset. `CountUniform` proves that a uniform cell only
hashes its start, with every other state field unchanged. `CountExecution`
derives the literal hash and queue trace from all nonuniform branches,
including both distance modes and the strict largest-fragment tie rule.
`CountCompare` and `CountControl` prove exact hash, active-set and ordered-queue
agreement from the input count multiset and initial control. Combined with
the partition and counter contracts, this proves transport of every
count-split observation under renaming and within-cell permutations. Hit
agreement is required only inside the divided cell; stale counts elsewhere
and independently allocated scratch remain unrestricted.
`IndexTransport` proves that admissible vertex-index caches transport under
renaming and within-cell permutations, with literal endpoint agreement at
cell starts. `RowTransport`, `TouchCompare` and `MarkTransport` derive literal
agreement of the sorted touched-cell arrays returned by native singleton
marking. The returned vertex-mark predicates commute with renaming even when
the two executions use different generations and retained mark arrays.
`CompactTransport` and `CompactClasses` prove equal cuts and hit counts and
transport of both restored fragment multisets. The fragment formulas retain
the exact source order for unmarked vertices and its reversal for marked
vertices, matching the executed compaction and reinsertion loops.
`BinaryControl` and `BinaryStep` prove the exact hash, active-set, ordered-queue,
partition and counter observations of a complete executed singleton-cell
body from its predicate-class sizes, including both uniform cases. The
contract also preserves the label window and scratch frame and gives both
literal fragment lists. `BinaryIndex` composes the executed final cache
writes with the compaction cache proof, giving per-cell index preservation.
`BinaryPass` and `SingletonTrace` compose these contracts through the actual
native marking and touched-cell loops, including their initial hash.
`SingletonEquiv` proves transport of the complete production singleton pass:
the ordered partition, hash, active set, ordered queue and exact cell count
agree literally, and output cell multisets commute with renaming. The input
orders within cells, native row orders, admissible caches and generations
may differ. These laws compose in full refinement equivariance below.
`RowsTransport` and `ScanTransport` transport complete native nontrivial scans,
including first-touch clearing and exact counts throughout touched cells.
`CountPass` and `NontrivialTrace` derive the executed count-split loop's trace
and its pending-cell bounds. `NontrivialEquiv` gives the corresponding full
production nontrivial-pass law for ordered partition, cell multisets, hash,
active set, ordered queue and exact cell count. Untouched scratch hits remain
unrestricted. `DistanceMap`, `DistanceTransport` and `RefineDistance` transport
the shallow branch from its actual queued singleton through native BFS and
the complete distance-cell loop. `RefineSelect`, `RefineBranches` and
`RefineLoop` handle exact queue preference, swap/pop removal, hashing,
dispatch and early breaks. `RefineInitial` establishes queue enumeration and
rebuilt indices, and `refineWith_parts` identifies the proof blocks with
production by kernel definitional equality. `refineWith_equiv` proves complete
code and ordered-cell equivariance under independently bounded scratch,
including empty queues and final cleanup. The partition, active set, ordered
queue, cell count and hash agree literally; corresponding cell label multisets
transport. `refineWith_congr` proves literal label, partition, active-set,
ordered-queue, count and hash equality for identical inputs with arbitrary
bounded scratch on either side. Incoming indices are rebuilt, and retained
counts, marks and generations may differ. `splitSingleton_lab`,
`splitCounts_lab` and `splitNontrivial_lab` establish literal equality through
both native splitter branches. `Sort.indirect_congr` follows insertion,
pivot sampling, partition swaps and the explicit stack, preserving exact tie
order under key agreement only inside the requested segment. `RefineCongr`,
`DistanceCongr` and `RefineLiteral` compose these results through native BFS,
the full distance and main loops, and final cleanup. The hypotheses require
a label permutation, an allocated closed partition, active cell starts and
bounded scratch; no sortedness, zeroed stale hits or output-equality premise
is required.
`IndexRuns`, `IndexTwo`, and `IndexFrame` establish run-by-run cache scatter,
singleton sentinels, the first two fragments, and preservation outside the
window. `IndexFinish` derives full index validity from those local properties.
`Window` and `MinimaPerm` retain bounded, injective label permutations through
the actual insertion writes. `CountIndex` proves `splitCounts_cache`, composing these
properties through every executed branch, including the first two fragments,
constant-cell returns, bounded tail scan, and final queue replacement.
`CountValid` proves `splitCounts_index`, preserving `Index.Valid` from an
incoming valid cache, a bounded partition cell, a permutation of `range n`,
partition allocation, and hits below `n + 2` on that cell. No bound or zero
condition is imposed on counts outside the cell. `CellClear`, `Counts`, and
`CountScan` track exact counts in touched cells without restricting untouched
scratch values. `CountNeighbors` follows the native nested loops, including
first-touch clearing and skipped singleton neighbours. `CountBound` derives
the splitter-size bound from simple native rows. `NontrivialIndex` composes
these facts through the complete nontrivial pass, preserving the label
permutation, partition allocation, and full cache validity. `WindowCells` lifts
local cell permutations through successive cuts; both full passes preserve
the vertex multiset of each original cell. `CountConstant` interprets each
output fragment through its incoming counts. `CountSemantics` handles touched
counts and untouched semantic zeros; `CountPending` follows the remaining
touched cells. `splitNontrivial_constant` proves that every output cell has
constant native neighbour count into the captured splitter cell.
`SingletonPending` supplies the corresponding binary-fragment argument,
including untouched zero counts and uniform cells; `splitSingleton_constant`
proves constant native row counts on every output cell of the singleton pass.
`CompactRun` and `FillRun` prove the singleton splitter's literal compaction and
reverse reinsertion loops. They retain the unmarked order, collect marked
vertices in order, and reinstall those vertices in reverse order with their new
cell start. `CompactFinish`, `CompactKeys`, and `FillIndex` derive the local
label permutation, predicate separation, and exact index scatter. `CompactIndex`
proves complete cache validity after the conditional partition, endpoint, and
sentinel writes for one nontrivial cell, including both uniform-predicate cases.
`SingletonMarks` derives exact adjacency marks and a sorted, duplicate-free list
of bounded nontrivial cells from the native graph and valid incoming cache.
`Touched` gives first-occurrence coverage, while `CellCut` proves that each new
boundary preserves all disjoint cells. `SingletonIndex` proves the complete
executed singleton pass preserves the label permutation, partition allocation,
and full cache validity, including every touched cell and uniform-cell return.
`splitSingleton_state` also proves that counter increments equal new boundaries
and inherited closed values are retained literally. It preserves `CellQueue`: a
duplicate-free queue agreeing exactly with the packed active set, whose members
are cell starts. `splitSingleton_active` also proves the semantic activation
rule: every fragment of an active original cell is active, and at most one
fragment of each other original cell is inactive. `ActiveCells` composes local
activation proofs across disjoint original cells. `ActiveQueue`, `QueueRemove`, and `QueueReplace` prove the
executed insertion, removal, and replacement operations, including removal at
the final position. `CountQueue` proves that the complete count splitter
preserves this exact queue contract through both initial fragments, the
bounded tail scan, and largest-fragment replacement. The active-set invariant
needed for equitability follows from the fragment activation proofs. The shared `certInv_transport`
theorem reduces its preservation to partition refinement, constant counts
into the retired splitter, and the per-cell fragment activation rule. The
dense proof now uses this same graph-independent transport argument; the
singleton and nontrivial passes supply native count and fragment activation
facts. `CountActive` proves the complete count splitter's activation rule and
unchanged outside membership, including largest-fragment replacement;
`CountActivation` composes it through the touched-cell fold. `ActiveSpan`
tracks the interior fragments and bounds every appended queue entry inside
the split cell. `NativeCounts` identifies accumulated native row counts with
set-intersection cardinalities. `SplitterConst` interprets both complete
splitter passes through the shared cell predicate. `CertState` projects only
partition fields for proof reuse; `PassCert` proves certificate preservation
for both actual main-loop branches, including queue removal and hashing.
Neither projection invokes a dense algorithm. `DistanceAdj` relates native
neighbours to distance-one vertices, including unreachable sentinels and small
graphs. `DistanceRun` proves constant distance classes and fragment activation
for the literal distance loop; `DistanceCert` transports its certificate.
`RefineCert.refineWith_cert` preserves the certificate through the complete
executed refinement. `refineWith_equitable` combines it with exact counting
and stopping, covering both exhausted queues and discrete exits. `initial_cert`
and `initial_equitable` establish the certificate and equitable root refinement
from the actual initializer for every nonempty sparse coloured input.
`ChildEntry` derives the next certificate from parent equitability for the
actual sparse child policy, together with label, partition, scratch and exact
count invariants. `Descent` connects it to the production visit and proves
equitable children. `TargetValid` derives nontrivial-cell existence and a
checked label from node facts; fresh and cached target selection return a
bounded nontrivial cell without extra parser-success or cache assumptions.
`IndexSet` and `TargetCounts` identify cached membership and native partial-join
counts with their set-valued meanings. `TargetInvariant` proves that changing
the representative by reordering an equitable cell preserves its score and
the first-maximum target. `ContextMap` and `TargetEquiv` prove graph-renaming
transport. `TargetTransport` proves the complete fresh/cached position, set
and size laws, including hints, depth cutoffs, arbitrary admissible scratch,
and invalid-cache fallback. Its fresh-selector index witnesses are constructed
by the proved indexer.

`Boundary` and `RefineBoundary` prove that the full executed refinement retains
partition allocation and changes values only to the current level, preserving
every existing closed boundary. This covers the distance pass and all three
splitters. `Root` supplies the actual initializer's active-cardinality bound,
so the root's operational exhaustion theorem is unconditional. It also proves
the sparse initial partition satisfies `NodeOk` and activates every colour
cell, using the adjacency-independent ordered-partition correspondence.
The root's passed cell count equals its boundary count. `CountSize` proves
that every counter increment of the executed count splitter closes exactly
one new boundary. `MinimaBound` retains the local hit bound and sentinel
through all five insertion arms, so a nonconstant split has two nonempty
minimum fragments. Scratch values outside that cell are unrestricted.
`Cuts` tracks increasing boundary writes and the untouched suffix. Full
singleton and nontrivial passes compose this relation: `splitSingleton_state`
and `splitNontrivial_state` return the complete `Cuts` contract alongside label
permutation and cache validity. `RefineState` combines the splitters' label,
partition, scratch, queue, and counter contracts. `RefineIndex.refineWith_state`
proves them through the complete distance pass and main refinement loop,
including index rebuilding, first-ten queue selection, removal, and both
splitter branches. It retains every original cell's vertex multiset and
returns a scratch cache valid for the output partition whenever indexed.
`RefineVisit` derives exact output cell accounting and preserves `NodeOk`
and scratch validity for the executed production visit. `RefineStop` bounds
active cardinality by the cell count for every valid partition and identifies
the loop exits as an empty active queue or a discrete partition. This
structural stopping result supplies the exit condition of `refineWith_equitable`.
`splitCounts_closed` retains old closed values literally, including ancestor
boundaries; it follows from the same executed cut sequence as the count theorem.
The shared recovery projections are polymorphic in search storage. `Recover`
proves that count splitting preserves the partition seen after recovery to an
ancestor level. `PolicyScratch` proves scratch validity for the actual sparse
child, recovery, and full target transitions, including index invalidation and
borrowed count storage. Full refinement now supplies their allocation,
generation, and index invariants for a well-formed input node. `Reach`
carries these contracts through every recursive production call.
`Marks`, `SplitBounds`, and `RefineBounds` establish the allocation and generation
part through every executed splitter, index rebuilding, distance initialization,
the complete refinement loop, and the production visit. Incrementing the stamp
makes all retained marks stale. Target selection preserves allocation and
generation bounds independently of index correctness. The full refinement
state theorem integrates the proved cache and first-touch count semantics.

`Nauty.Sparse.initialPartition_eq` in `Initial` proves that
the sparse initializer's stable bucket loops equal the ordered-colour partition
specification. Its corollaries prove vertex permutation and size, exactly `k`
cells, strictly increasing bounded endpoints, and the terminal endpoint for
nonempty inputs. The dense graph appearing in this equality is a proof bridge;
the executable initializer reads only the native colouring.

`Sparse.IsIso` and `Sparse.Isomorphic` describe forward transporters and
isomorphism directly on native coloured graphs. Their explicit conversion
theorems preserve the dense isomorphism relation. `Sparse.checkIso` is a
proved decision procedure for a supplied permutation, implemented by native
relabel-and-compare. `SparseGraph` has the corresponding bare-graph relations
and checker, including order zero, and a positive-order `singleColor` bridge.
These checkers do not depend on canonical-search correctness.

`Sparse.Kernel.checkIso` verifies literal neighbour rows and colour lists.
It sorts each mapped row with the exposed, verified merge sort, checks exact
row equality, and has soundness, completeness, and equality theorems to the
native checker. Soundness requires a typed permutation and equalities tying
every literal to its source graph; arbitrary unattached literals are not a
certificate. Kernel reduction across an import boundary is part of this
contract. The edge-list builder exposes row normalization to the kernel and
uses its proved compiler replacement to retain the native array-map path.

### Specification, proofs, and certificates

`SpecTree` defines the finite unpruned sparse tree with fresh executed
refinement, hint-free sparse targets, every target member, and typed leaf
labels. `SpecFuel` proves nonempty leaves at every valid input and coloured
root, including order zero. `SpecBound` proves that increasing a sufficient
fuel bound changes no leaf, so all branches are complete. `SpecMax` defines
`canonSpecKey` and `canonSpecLabel`, proves that the selected leaf belongs to
the tree and dominates every other leaf, and identifies its graph with the
native relabelling by its attaining label. `RefineFrame` preserves every
ancestor cell's contents and inherited boundary values through executed
refinement. `SpecColors` carries original colour-cell contents through every
unpruned descendant, proves the attaining form's sorted colour sequence, and
records normalized native neighbour rows. `SpecNode` derives the complete
unpruned root, refinement and child invariants. `SpecTransport` proves `specLeaves_map`, which
transports every executed leaf, including its full code chain, under an
isomorphism and within-cell reordering. `SpecIso` proves `canonSpecKey_map`, giving
maximum invariance by transporting attaining leaves in both directions.
`SpecCanon` proves `specCanon_invariant` and `iso_iff_specCanon_eq`, establishing invariance
and the canonical-form characterization of isomorphism, including order zero.
`MaxResult` and `Sparse.Canonical` prove equality with the production key
and public form, respectively.

The sparse declarative key is the maximum leaf key of its unpruned tree:
sparse refinement codes ending in the existing sentinel, then the sparse
canonical graph in the order above. It is distinct from `Nauty.Key`.
Refinement proofs establish partition preservation, progress, equitability,
and equivariance, including the distance shortcut. The ordering is lawful,
the specification is invariant under isomorphism, and a reachable label
attains its value. Production-search correctness identifies the selected
key with this specification. Automorphism completeness accounts for pruned
children and the point stabilizers along the first path.

The proof contracts describe the optimized executable. Raw canonical storage
has allocated capacity and a valid prefix of `samerows` rows; blank storage
is not a complete graph. Cached refinement agrees with fresh refinement on
labelling, partition, active set, cell count, and code, rather than on scratch
contents. Equitability requires the active-splitter invariant, including the
empty-active case. Every array access and explicit loop bound is justified
under reachable-state hypotheses.

The shared recursive proof engine is `Generic.Contract` and `SoundPolicy`.
`SearchBounds` instantiates its persistent-invariant rules, proving scratch
allocation and generation bounds through every production node, sweep and
exit, with unconditional root initialization and final-installation results.
`Reach` instantiates the full sparse partition contract. Its mutual recursion
carries valid node entries, equitable parents, exact cell counts, original
colour-cell contents, valid target membership and reference-label frame
effects through individualization, pruning, recovery and nonlocal exits.
Root premises follow from stable colour buckets. This frame theorem also
applies to truncated calls. `Fuel` instantiates the stronger mutual contract
and proves that the unchanged node and packed-cursor bounds cannot be
exhausted. `runState_noFuel` derives this unconditionally at the actual root,
including order zero. `FirstPath` constructs the actual first descent from
identity orbits and nonempty native targets. `FirstResult` carries its
installed label through all remaining siblings and returns. `Result` proves
unconditional `searchResult?_isSome`, including order zero. `Sparse.Ops`
extracts the total `canonicalize` result from that proof and exposes `canon`,
`label`, `findIso` and `isIso`. Relabelling, ordered colours, transporter
soundness and exact diagnostic agreement are proved. `MaxResult` establishes
production maximality, and `Sparse.Canonical` proves equality with the
declarative form, invariance and complete isomorphism decisions at all orders.
`Reference` preserves the saved first leaf, code array and target array in
every off-path node and later sibling. `FirstFields` identifies native
preparation's exact depth-indexed writes, unchanged ancestor slots and
allocations. `Depth` proves that all emitted refinement codes lie below the
terminal sentinel and that first-code agreement cannot advance below the
saved leaf. `ReferenceResult` derives the retained sentinel, depth bound and
valid colour-respecting first label from the actual initialized root.
`ClassifyStore` proves incumbent-prefix preservation and the candidate prefix
supplied by every native better verdict. `StoreSearch` carries this through
the actual mutual recursion, including partial stores, shared leaf actions,
recovery and nonlocal exits. `FirstStore` seeds the invariant at the first
leaf using the retained blank row allocation. `StoreResult` proves
unconditional root validity and final row completion: the working rows are
permutations of the corresponding normalized neighbours of the public
label's relabelling. This store theorem includes order zero and retains raw
neighbour order throughout search.
`WorkSize` proves that every actual node and sweep retains its permutation
workspace allocation, with size `n` at the initialized root. `Scatter`
identifies all workspace entries with the forward map from the reference
label to the current label. `CanonAutom` proves that a canonical-tie verdict
has equal native relabelled graphs and emits exactly that map. `LeafAutom`
proves ordered-colour preservation and automorphism soundness for canonical
ties and first-reference admissions using an explicit scan. These local
theorems consume valid parsed labels, colour reachability and the row-cache
invariant. The cheap first-reference branch uses the ancestor histories
derived by the production trace induction below.
`SmallCell` interprets a native equitable partition for the shared
cell-stabilizer transitivity theorem. `SmallStep` proves that both cheap-guard
shapes survive actual child and refinement operations. `RefinedNode`, `Path`
and `PathTransport` cover literal cached child calls and entire corresponding
descents, retaining each call's bounded scratch argument. `CheapLeaves`
proves equal normalized leaf graphs for two discrete descents below a
cheap-shaped node with the same target positions. `CheapPrefix` strengthens
this to matching target prefixes, proving equality of leaf depths as well.
`ReferenceLeaf` connects the saved reference, code bound and exact scatter.
`FollowsPerm` retains a current history through within-cell reordering and
actual cached child calls; at a discrete leaf its label is literal.
`CheapAdmission` proves that the native first-reference verdict emits a
coloured automorphism under those history premises. `CodeTransport` preserves
selected target paths and their complete code sequences under isomorphism.
`CheapTarget` proves agreement with the next selected target along an open
prefix; `ReferenceTarget` identifies that target with its saved array entry,
including after sibling reordering. `TargetHint` proves equality of the
actual cached hinted and unhinted target position, vertex set and size under
those premises, allowing different resulting scratch contents. The trace
induction derives frozen ancestors, current histories and matching targets
at every executed cheap admission.
`Preparation` and `FirstChoice` identify the literal cached visit, child call
and unhinted target of each first-path step. `FirstHistory` constructs the
selected descent with its executed code sequence and literal terminal
label/partition. `FirstRef` preserves its saved target slots, code slots,
first label and sentinel after all later siblings; `RootHistory` derives
the complete reference from initialization and retains it through final
row installation. `CodeBounds` proves every recorded code is below the
sentinel; `CodeFields` retains canonical code allocation throughout the first
descent. `FirstCodes` derives both comparison machines at the actual first
leaf from initialization. `CodeRead` gives the native sparse key represented
by stable incumbent storage. `Comparison` includes valid parsed references
and the first key's lower bound on the incumbent, with proved initialization,
visit, code comparison, target and child transitions. `ComparisonOps` proves
off-path preparation and recovery of both ordinary settled codes and negative
row verdicts after code equality. `CodeOrder` connects the executed code
machine to native key order. `Canonical.canonVerdict_max` proves exact
incumbent/candidate maximum selection and settled code semantics for every
canonical verdict, including all sparse row outcomes. `PathFrame` and
`Positions` prove preservation of ordered ancestor cells and literal selected
vertices through native cached descents. `Guided` proves equality of depth
and complete codes for selected and guided paths with corresponding terminal
labels; `GuidedLeaf` derives their common ancestor's stabilizer and the saved
first sentinel and graph from a native automorphism. `GuidedPerm` and `RouteAt`
retain these histories through label reordering, actual child visits and native
partition recovery. `RouteKey` uses them with proved admission soundness to
identify the full first-reference key and prove the executed leaf maximum.
`RouteHistory` preserves the general history through preparation, children and
full-call recovery; `FirstRoute` derives it from the actual first child.
`LeafCodes` proves settled comparisons and incumbent growth at terminal
classifications. `CodeState` and `CodePrepare` provide both histories, recorded
target choices and the nonempty target required by a positive comparison.
`CodeSweep` and `CodeNode` carry recoverable comparisons and monotone native
incumbents through the executed mutual recursion. `FirstCompare` connects the
actual first leaf to every ancestor's remaining siblings. `CodeResult` derives
settled comparisons and a readable incumbent from root initialization and
retains them through final row installation. The native `CanonFrame`,
`CanonNode`, `CanonSweep` and `CanonCalls` proofs track the canonical reference
through complete calls. `CanonSource` proves that a child either retains its
incoming reference or installs one through its literal chosen vertex, and
that references pointing above the child remain unchanged. `CanonGuide`
preserves a covered-reference witness through sibling permutations and actual
child recovery, with local child coverage supplied by the coverage induction.
`CanonScatter` identifies the classifier's literal forward scatter.
`ReturnOrigin` transports the emitting leaf's last pruning pair through all
intervening calls: an explicit pair retains its canonical ancestor and trace
entry, while an implicit pair retains its cheap-boundary limit. These are
provenance results. `ExitBound` determines the exact receiving level, and
`Capacity` retains the pinned workspace capacity. `CanonPair` and `ShortPair`
prove actual receiver pair validity for explicit and implicit emissions.
`SubtreeKey` aggregates the existing unpruned leaves and proves attainment
with sufficient fuel. `SubtreeMap`, `VertexKey` and `VertexFrame` establish
maximum transport under native isomorphisms, checked cell stabilizers and
recovered parent frames. `FilterCover` and `FilterPrune` prove ranked coverage
preservation by both actual filters, including representatives lost by earlier
filters. `CoverFrame` transports coverage and reference keys together through
sibling reordering. `CanonCover` proves that an actual received canonical
scatter covers the entire current child using its already covered reference.
`PrefixKey` preserves native key comparisons and maxima under common ancestor
codes. `SubtreeSplit` characterizes internal-node maxima by their complete
children and proves attainment by one child. `VisitKey`, `VisitTarget` and
`VisitSplit` transfer this decomposition to actual cached visits and targets;
discrete visits have exactly their parsed leaf key. `VisitCover` turns exhausted
ranked coverage into full node coverage with its ancestor codes. `CodeBound`
proves that a negative code comparison after actual preparation covers every
continuation of the complete node. `Maximum` composes native incumbent upper
bounds and exit coverage. `LeafBound` derives upper bounds and candidate
coverage from the actual classifier and exit. `MaxFrame` and `MaxCell` retain
valid native entries and original child keys through reordered parent frames.
`MaxEmit` proves whole-node bounds and coverage for actual discrete exits and
nondiscrete code rejection. `CodeScope` records valid ancestor entries with
their actual code prefixes; descent, truncation and negative-prefix rejection
preserve and resolve those witnesses. `MaxReject` proves the complete return
contract for code-supported nondiscrete rejection, including nonlocal exits,
and exposes the separate cheap-boundary alternative. `CursorCover` connects
received children and orbit skips to the literal cursor. `FrozenPrune`,
`ResumeCover` and `ReceiveCover` compose actual short and long filtering,
recovery and the next off-path sibling call with its recursive child result.
`SmallKey` identifies all complete native child keys under the cheap shape.
`MaxTarget` identifies full node coverage with its original cached target;
a passing native cheap guard makes any actual individualized child attain
the whole node key, including after sibling reordering. `MaxParent` retains
the literal chosen child of each suspended native entry and identifies its
key with the parent's under the cheap shape, unless an earlier negative
comparison already covers the parent. `MaxScope` initializes the ancestor
chain at the root, extends it on individualization and preserves it under
incumbent growth and the native cheap-boundary counter alternative.
`MaxCheap` composes coverage through that chain and proves the full return
contract for an actual discrete emission to its cheap boundary and every
nondiscrete rejection, given this ancestor invariant. `MaxChoice` derives
the target alternative from actual preparation: either the target is
unhinted or a negative comparison covers every continuation of its code
prefix. This bounds hinted children as well as the parent. `MaxPrepare`
establishes the suspended-parent invariant on both preparation paths;
`MaxDescent` establishes the child scopes and retains ancestors through
complete off-path calls. `MaxRecover` and `MaxResume` derive the recovered
comparison, history, target and ancestor facts for every surviving next
vertex from the actual child call. `MaxUpperSweep` and `MaxUpperNode`
close the complete off-path node/sibling upper-bound induction, including
both filters, skipped vertices, hinted targets and nonlocal returns.
The result requires native entry and ancestor invariants but no assumed
subcall maximum theorem. `MaxFirstLeaf` derives the first leaf's code
machine from its actual stored prefix and allocation, identifies its
installed native key with the full frozen node key and proves the complete
maximum contract for the executed first discrete call. `MaxFirstEntry`
derives native first-entry storage, histories and inherited shape from the
root initializer and preserves them through actual first children.
`MaxFirstCodes` derives the complete first-leaf comparison from stored
prefix and suffix writes at arbitrary entry depth, then recovers the
caller's exact code prefix after the full call. `MaxFirstResume` supplies
the next sibling's comparison, history, target, shape and ancestor facts
from that actual first-child return, without assuming a maximum result.
`MaxFirstSweep` and `MaxFirstUpper` close the complete first-path
upper-bound induction through the actual first child and every later
sibling. `MaxUpperResult` identifies the root's depth-derived bound with
the declarative maximum using sufficient-fuel stability. `runState_upper`
and `run_upper` prove that every installed native production key is at
most `canonSpecKey`, without assumed search-correctness contracts. The
order-zero state has no installed code chain. Finalizing the native row
cache retains this key bound.
`MaxScatter` identifies the actual selected child's whole key and
transports coverage from a reference child using a native automorphism.
`MaxAncestor` derives every ancestor's child frame from the retained
parent chain; `MaxRetain` proves literal preservation of its closed
boundaries through preparation, individualization and later entries.
`MaxEmitter` consequently derives cell containment and the selected
vertex's exact position at the actual emitter, then constructs the
nonlocal coverage witness from a covered reference and its scatter.
`MaxGuides` records previously covered reference children at suspension
and associates earlier reference counters with their literal stored
labels. It initializes at the root and extends through actual
individualization. `MaxGuideReturn` retains those associations through
complete off-path calls, terminal dispatch and either native child
return/recovery path. `MaxAutoFirst` proves the full maximum return
contract for first-reference automorphism leaves, including cheap
admission and nonlocal returns, from the covered-reference invariant and
positive strict ancestor counter. `MaxAutoCanon` proves the corresponding
contract whenever canonical admission returns to its canonical ancestor,
for either short flag. Both rules derive the literal native automorphism
scatter and emitter geometry. `MaxGuideFrame` transports reference coverage
to the recovered label ordering. `MaxGuideBack` and `MaxGuideFirst` establish
both guides for the next sibling from the completed child's coverage and
native reference provenance. `FirstFrame` derives the first saved label's
cell containment and selected position from the literal first descent.
`AncestorOrder` preserves canonical lower bounds and ancestor order through
the native recursion. `MaxControl` derives positive ordered counters on
recovery, and sets both counters exactly to the parent after its first child.
It also preserves references through actual preparation and initializes the
new sweep's vacuous guides when its ancestors are strictly older.
`MaxRank` derives coverage of every smaller target vertex from ranked
frozen-cell coverage, including filtered vertices and hinted targets. The
actual trace word then covers a selected child with a smaller orbit pointer.
`Coset` proves that off-path recursion retains the selected index;
`MaxCosetState` associates it with its actual suspended first ancestor through
preparation, child selection and both return paths. `MaxCoset` combines these
facts into the full canonical-admission maximum rule, including the earlier
first-ancestor coset return. Its rank, index, reference and trace premises
are local traversal invariants, not an unconditional production maximum.
`MaxTrace` derives and retains stabilization for every suspended first
ancestor. `SelectedCell` and `MaxLoop` identify the complete actual native
target, including hinted selections, and its literal child entries.
`LoopCover` transfers ranked coverage and canonical guides between frozen
and recovered cell orderings. `MaxContext`, `MaxStart` and `MaxNext` assemble
the full off-path context through native preparation, child entry and
recovery. `MaxSweep.lower_sweep` proves the complete later-sibling coverage
induction, including both filters, orbit skips and nonlocal returns.
`MaxTerminal` handles every terminal classifier case. `MaxNode.node_max`
combines these results with the unconditional upper bound to prove the
complete off-path node maximum contract by induction on the actual recursion
bound. Its premises are the assembled local traversal invariants.
`MaxFirstContext` establishes the initial first-descent context and preserves
it at each actual first cursor. `MaxFirstPairs` restores pruning-pair validity,
and `MaxFirstNext` assembles the full sibling context from the returned child's
coverage. `MaxFirstFilter` justifies the first child's actual short filter.
`MaxFirstLower` covers the complete first sweep, and `MaxFirstNode` closes the
first-descent induction. `MaxResult.runState_max` and `run_max` prove that the
actual nonempty production key is exactly `canonSpecKey`, deriving the root
context from stable colour initialization and using the unchanged sufficient
fuel bound. No search-result premise remains. `Sparse.Canonical` proves
`canon_eq_specCanon` at all orders, treating the unique empty graph explicitly.
`AncestorStab` transports cell stabilizers between suspended ancestors and
derives them from reference scatters. `OrbitCover` constructs the literal
trace-word carrier for a skipped pointer and preserves ranked child coverage
when the trace stabilizes the frozen partition. The empty-path case derives
stabilization from native generator soundness. `TraceFrame` records containment
of both saved labels in the frozen cells and stabilization by every emitted
generator. Its leaf, operation and mutual-recursion proofs preserve this
invariant through complete calls, truncated calls and nonlocal returns.
`FirstTraceFrame.firstPath_stabilizes` derives its initialization from the
actual first leaf, without assuming reference containment before that leaf.
`TraceOrbit.firstChild_stabilizes` establishes it for the first child's
prepared parent, and `TraceFrame.skip_cover` supplies the orbit guard's
stabilization premise. `MaxSweep` and `MaxFirstNext` integrate these facts
into complete maximum coverage and its first-child initialization.
`ReadyPerm` retains the full frozen node
and refinement certificate under within-cell label reordering. `DescentAt`
matches the production label, partition and count to that witness, extends
it through actual cached child visits, and restores it using the established
native recovery frame effect. `Alignment` retains that witness while first-code
agreement remains live, including recovery after arbitrary off-path child
calls. `AlignedTarget` identifies the actual cached target with its stored
slot. `Controls` proves preservation of the first ancestor and persistence of
failed ancestor guards through descendant calls. `CheapHistory` proves local
preparation, child and return transitions for the frozen reference and current
descent. Its `first_iso` theorem proves both first-admission guard arms sound
from that history, using the saved sentinel independently of incumbent
comparison. `FirstCheap` establishes inherited guard shapes from initialization
and retains them through first children. `FirstReturn` derives the recovered
history and saved target from completion of the actual first-child call.
`Trace` identifies the literal arrays appended by native automorphism verdicts
and proves their soundness from the retained histories and row prefix. `Saved`
preserves installed reference and workspace validity through complete off-path
calls and derives it from the actual first descent. `TraceState` combines these
with histories through preparation, admission, child entry and recovery.
`TraceSweep`, `TraceNode` and `FirstTrace` prove soundness through the complete
mutual recursion and first descent. `TraceResult.runState_trace` and
`runColored_trace` derive the root guarantee from initialization, including
order zero and final row installation. `generator_iso` proves that every
literal emitted array has size `n` and is the exact forward map of a native
colour-preserving automorphism. `Orbits` proves that every final orbit pointer
descends, stays in range and is connected by a word in the literal emitted
trace. `orbit_iso` realizes that pointer by a native coloured automorphism.
The pointer proof follows the actual joins and full recursion; exact orbit
completeness follows from the generation theorem below. The native `Fixed` proofs preserve fixed
singleton cells and show that every node and sweep restores its incoming
fixed-point bitset, including truncation and nonlocal exits; `runColored_fixed`
proves that the completed root has removed all temporary fixed vertices.
`Stabilize` transports cell stabilizers through actual cached refinement.
`PathState` initializes the root path invariant and preserves it through local
transitions and recovery after complete native child calls.
`CheapBoundary` validates implicit pairs at actual equitable states and
preserves frozen pairs through refinement, child calls and recovery;
`FirstBoundary` covers first-path completion. `Pairs` validates explicit and
implicit admissions and bounded workspace replacement. The pair-state node,
sweep and first-path proofs establish `PairsResult.runColored_pairs`:
every pair retained by the initialized search has checked root-colour-preserving
realizers, including order zero. `Prune` transports the workspace along the
current path and justifies native long-filter removals and whole-cell
representatives by checked automorphism carriers. The completed production
maximum induction integrates the canonical-reference guide, receiver validity
and local filter coverage. Full generation from the emitted trace is also proved.
Both comparison machines and incumbent growth are established through actual
nonlocal returns.
Sparse contracts discharge its local obligations for the sparse graph
dispatch, code histories, frozen ancestor frames, and cache invalidation.
Generator validity and ancestor stabilizer properties justify pruning;
generator completeness must not be an assumption in that justification.
The direct public canonicalization theorem is independent of certificate
replay. The optional diagnostic result remains available with an unconditional
success theorem and equality to the total public result.
`Sparse.UncoloredOps` exposes total bare `SparseGraph.canonicalize`, `canon`,
`label`, `findIso` and `isIso` without a positivity premise. Its native coloured
view has one colour for nonempty graphs and zero colours at order zero.
The wrappers retain the exact native form and label array; relabelling and
returned-transporter soundness are proved. Both coloured and bare sparse APIs
prove canonical invariance and idempotence, `iso_iff_canon_eq`,
`findIso_complete`, `findIso_isSome_iff`, `findIso_eq_none_iff` and both Boolean
decision directions. These contracts include order zero and rely on the
proved production maximum, independently of certificate replay.

The sparse public automorphism order uses the existing exact product in the
search state. Its proof identifies each first-path sweep index with the orbit
size for the corresponding point stabilizer. The full generator trace, rather
than the bounded pruning workspace, generates the full automorphism group.
Sparse order does not repeat the search on additional individualized graphs.
`GenerationFrame` proves native target-cell preservation by true point
stabilizers and triviality at actual first discrete visits. `TraceContains`
proves that both kinds of complete native calls retain every emitted array.
`GenerationTrace` decodes the unbounded trace as forward permutations,
establishes their soundness and realization of each emitted array, and
supplies generated orbit-pointer carriers fixing the active base.
`FirstBounds`, `EarlyReturn` and `FirstSweep` prove the native first-code
and all-same bounds, unconsumed leaf-return provenance and lower bounds,
and exact all-same preservation through later siblings. `CodePrefix`
identifies the saved codes reached along stored targets below a cheap
ancestor; `ReferenceEmit` connects equal native leaf graphs to the actual
first-reference admission and emitted label carrier. `ReferenceCode`,
`ReferenceStep` and `ReferenceDescent` prove the complete executed cheap
reference descent, including child visits after sibling reordering and the
emitted carrier. `FirstTail` proves local return of later first-path children
and completion of the native sibling sweep through both pruning filters and
orbit skips. `FirstComplete` proves that every actual first-path call returns
normally to its immediate parent. `ReferenceReturn` extracts checked label
carriers or orbit-pointer evidence from actual nonlocal returns.
`ReferenceSweep` bounds the canonical carrier's source by the current cursor;
`GeneratedReceipt` uses this evidence to advance generated orbit coverage.
`FirstSuffix` identifies the literal continuation after the guiding child.
`FirstCount` proves that every increment counts a distinct original target
vertex with a checked cell-stabilizing carrier to the guide, and that reaching
the target size supplies carriers for every original vertex. `FirstDrop`
identifies the exact counter guard that lowers the all-same boundary.
`LeafPath` describes selected literal cached descents with their complete
sparse keys and proves transport in both directions under isomorphism.
`FirstUniform` derives uniformity of every such descendant from the actual
returned all-same boundary and counted carriers. `RefPath` retains this
uniformity through checked cell-stabilizer transport. `Matching` identifies
the saved code, target and parsed-label arrays, and `FirstWitness` derives
the richer matching reference from the complete first call. `LeafPath`
also proves that every valid native refined state has a selected discrete
descendant. `MatchingTarget` and `UniformStep` retain stored matching through
the actual minimum child and its independent cache. `UniformReturn` proves
that a uniform matching subtree's executed recursion emits a checked
first-reference carrier and returns to that ancestor. `ReferenceOrbit`
transports the richer reference to every child in the true path-stabilizer
orbit, independently of completeness of the emitted group. Reference
transport through checked cell stabilizers is proved in both directions.
`ChildPath` transports frozen reference occurrences to the exact cached
children entered after sibling recovery. `PathCover` preserves those
occurrences through descending filters. `ReferenceVisit` handles actual
canonical returns through their earlier source; `ReferenceFilter` derives
both filters' witnesses from the returned child's checked workspace.
`ReferenceResume` reconstructs the full next-sibling context after the
literal filters and recovery. `ReferenceLoop` proves the complete off-path
sweep induction, with reference completion of its actual smaller child
calls as the recursive premise. `SmallUniform` proves that every selected
descent below a cheap-shaped native node has the same full key and targets,
using true cell-stabilizer transitivity and independent bounded scratch.
`ReferenceComplete` discharges the smaller-child premise by induction on
actual node calls, including reference completion above the uniform boundary.
`GeneratedVisit` and `GeneratedTail` prove generated coverage through actual
child returns and orbit skips. `GeneratedHead` constructs the guiding child's
reference and base premises; `GeneratedComplete` proves the full first-path
stabilizer induction. `GeneratedRoot.runColored_generates` proves that the
actual emitted trace generates every native colour-preserving automorphism,
including at order zero. `generated_iff` combines this with soundness to
identify the generated subgroup exactly. `OrbitReplay` identifies the actual
pointer array and count with the emitted join sequence. `OrbitExact` proves
least representatives, the full orbit biconditional and the exact root count.
Coloured `Sparse.autos`, bare `SparseGraph.autos`, and the `Sparse.Aut` projections
expose these single-traversal results with generation and orbit correctness
theorems. `OrbitClosure` proves that every intermediate orbit array is closed
under its current emitted generators; later joins preserve earlier
connections. `OrbitMark` identifies the literal counter test with membership
in the true point-stabilizer orbit. `StabilizerTail` and `StabilizerHead`
prove that each executed first-path index is the exact stabilizer orbit
size, including both visited and skipped siblings. `OrderOps` proves that
off-path nodes and later siblings retain the actual order accumulator.
`OrderStep` proves the executed first-child multiplication and terminal
value. The Mathlib `Sparse.Aut.order_card` theorem identifies this product
with the full group cardinality, including order zero. It uses the actual
first-path stabilizers and performs no additional searches.

The sparse `CertNode` has discrete-leaf, strict-code-prune, checked automorphism
reference and complete child-list records. The expansion checker's
`checkNode_valid` proves that acceptance bounds every leaf
of the actual sparse tree and exactly records attainment. `checkKey_sound`
therefore identifies the claimed key with `canonSpecKey`. `produceNode_replays`
and `produceRoot_replays` prove unlimited expansion completeness from the
native root and child invariants. `produceCand` runs the optimized search once
and expands proof subtrees against its installed key. `produceCand_eq` proves
that this is the exact declarative maximum and that the candidate retains the
literal production label; `certifyKey?_eq` proves unconditional producer/checker
success. `not_isomorphic_of_checkKeys` derives non-isomorphism from two accepted,
differing keys. `checkCanon_sound` proves that a checked label attains the
canonical graph and its ordered colour sequence. `certifyCanon?_eq` proves
unconditional certification success and exact agreement with the total direct
API's form and literal production label, using one search and one replay.

`Compact.checkNode_valid` extends replay soundness to automorphism references.
`Replay.checkAutom_sound` checks a full permutation, sparse adjacency preservation
and transport of every ordered child cell. `Replay.scan_valid` proves that a
reference can only reuse an earlier successfully checked flag, including chains
of references. `Compact.checkKey_sound` still identifies the full declarative
maximum. `Compact.produceCand` uses the optimized search's key, literal label
and generator trace from one run. Generator filtering and orbit-witness BFS
only propose witnesses; each emitted reference passes the exact sparse replay
predicate, and its subtree is not expanded. `Compact.produceNode_replays` and
`produceRoot_replays` prove unlimited success, with full expansion when a
witness is unavailable or rejected. `Compact.certifyCanon?_eq` proves exact
agreement with the total direct form and label.

`Literal.checkKey_eq` proves equality of the imported-module kernel replay
with the specification checker. The replay retains native sparse adjacency
and uses exported list recursion for bounded ranges, the existing exported
array mapping for label parsing, and exported function tabulation for sparse
relabelling. Every replacement has equality with its executed counterpart;
the production search is unchanged. `SparseCertTests` checks the recorded
order-12 random canonical keys and negative pair in the kernel and rejects
malformed child lists, leaf records, labels and terminal codes.
`Literal.Compact.checkKey_eq` and `checkCanon_eq` establish the same equality
for compact replay. Kernel tests accept the endpoint-swap reference and reject
forward/self references, malformed permutations, graph non-automorphisms and
incorrect ordered-child transport. `CertNode.stats` counts proof records,
automorphism records and permutation payload entries in one traversal.
`Compact.checkRecords?` checks the record cap before replay;
`checkRecords?_eq_some` proves exact verdict agreement and admission within the
cap, and `checkRecords?_none` identifies exhaustion. Equivalent literal replay
has zero-limit, exact-boundary and rejected-record kernel tests.
`Quota.collect` threads unused quota through actual sibling production, and
`Quota.emit` charges each checked reference before emitting it. The bounded
`Compact.produceNode?` and `produceRoot?` stop when the record quota is exhausted.
Their budget theorems identify the exact size of returned certificates; their
agreement theorems identify successful trees with unlimited compact production.
`Compact.candidate?` retains a supplied search's literal label without repeating
that search. `produceNode?_complete` and `produceRoot?_complete` prove success
when the exact unlimited tree size fits. `produceRoot?_none` characterizes
exhaustion as a strictly smaller record cap. `candidate?_complete` identifies
the resulting key, literal label and tree with the unlimited candidate from the
optimized native run.

Sparse kernel replay calls the literal checkers directly. It has no operation
counters or estimated replay-cost preflight. Ordinary Lean resource controls
govern replay.

`Sparse.TacticSupport` supplies the native proof-producing backend: optimized
searches propose transporters, and reified sparse literals supply positive and
compact-certificate negative kernel proofs. `SparseTacticTests` checks the
empty graph and both recorded order-12 and ordered-colour Petersen order-10
positive/negative pairs across an import boundary. Both routes use the native
`Limited.runPair?`, sharing one search-node quota across the input graphs;
negative candidates use bounded compact production. `node_budget` proves quota
conservation through the whole executed recursion. `node_exhausted` proves
that exhausted state is unchanged by subsequent calls. `node_counted` identifies
admitted visits with the native `numnodes` field, and `node_nodes` bounds that
field even for exhausted returns. `runPair?_nodes` bounds the combined native
visits. `SparseLimitTests` covers zero, insufficient, exact and surplus quotas,
including exhaustion between searches, and compares successful native outputs
and diagnostics with the direct run. `LimitAgreement.node_eq` and `sweep_eq`
prove exact projection through every native callback, filter and nonlocal return.
`runColored?_eq` and `runPair?_eq` identify complete successful states with
the direct runs, including scratch, generator traces and diagnostics. The proof
also establishes that a successful return had a non-exhausted input.
`Compact.candidate?_from_run` identifies the actual bounded pipeline's candidate
with unlimited production; `candidate?_replays` proves acceptance, and the
existing candidate theorems identify its declarative key and literal label.
`Sparse.Tactic` registers coloured and bare sparse goals with the existing
`graph_iso` extension mechanism. Bare graphs use the zero-or-one-colour view,
including the empty graph. Both routes reject open terms and use the native
search and sparse literal checkers.

`HexGraphIsoMathlib.SparseTacticTests` checks correspondence-based sparse
replay across an import boundary, including ordered colours, an empty graph
and a changed enumeration. Fresh-module sparse proof probes live under
`bench/HexGraphIso/SparseProofProbe`; their external runner retains adjacent
import baselines, whole-build and kernel times, peak RSS, axiom sets and source
hashes.

The imported CFI proof closes with the ordinary sparse `graph_iso` route.
Four fresh builds use only `propext`, `Classical.choice` and `Quot.sound`;
the raw samples and adjacent import baselines are retained in
`reports/bench-results/hexgraphiso-sparse-replay-unlimited.jsonl`.

Sparse certificates and checker entrypoints distinguish sparse keys from
dense keys. The checker recomputes sparse refinement and comparisons and
verifies every pruning justification. It never trusts cached codes, counts,
or proposed permutations. The compiled producer is untrusted. Kernel-oriented
sparse literal checkers have equality theorems back to the specification
checkers and do not materialize dense graphs. Search-node and certificate-record limits
count actual visits and emitted records. Exhaustion is inconclusive, never a
negative isomorphism result.

`graph_iso` dispatches on the native graph type. Sparse positive goals check
an explicit transporter; negative goals use a verified invariant separation
or replay sparse canonical certificates. The core remains Mathlib-free and
has no C runtime dependency, new axiom, or `native_decide` path.

### Sparse validation and release

The sparse oracle independently rebuilds original inputs, and compares
canonical adjacency, colours, labels, all seven search statistics, generator
emissions, and exact orbits. Full recorded generator traces retain the dense
API's emission/subsequence convention. Exact group order is the product of
nauty's level indices, calculated using integer arithmetic; rounded
`statsblk` group-size fields are not the exact oracle.

Separate sparse fixtures mirror all labelled uncoloured graphs through five
vertices, all graph/ordered-surjective-partition pairs through four vertices,
and the six-vertex extended campaign. Targeted cases cover the distance
shortcut, sorting cutoffs, target levels beyond 100, marking resets, pruning
workspace saturation, disconnected graphs, and packed vertex-set boundaries.
Malformed certificates must be rejected. Existing dense fixtures remain
regression requirements.

Merge CI replays the committed dense and sparse fixture streams through
`scripts/ci/run_oracles.sh`. Release validation additionally runs
`scripts/oracle/graphiso_sparse_check.py --trace-corpus`: exact sorting,
refinement and 45,491 complete searches with integer group-order checks.
This extended differential campaign is collected manually.

Benchmarks distinguish native sparse construction, prepared search, public
canonicalization through normalized sparse output, automorphism operations,
and certificate production/replay. Extend the published 333-instance corpus
with the Hex sparse implementation, and compare its traversal and per-node
scaling with C sparse nauty. The existing `0.2` exponent tolerance applies
where sufficient matched sizes are available. A separate large bounded-degree
corpus is generated directly from edges to detect quadratic storage and
preprocessing. Record memory and output costs; no linear-time claim applies
to arbitrary canonical search or complete refinement. Use the shared-host
protocol in the repository benchmarking SPEC and retain historical data.
`runSparseBuild` registers native path construction at 1,024 through 65,536
vertices with lean-bench's linear model. Edge preparation is outside the
timer; construction and consuming both compressed arrays are inside it.
The measured scaling agrees with this model. The final two-pass six-way
refresh retains 2,486 process outcomes, solves 310/333 cases with Hex sparse,
and passes the 0.2 per-node exponent check against C sparse on all 20 families.
Separate automorphism, certificate-production and certificate-replay sweeps
pass on 38 native inputs. The full build, published trust/import audits,
exact C conformance, imported kernel probes and performance-freshness checks
pass; `reports/sparse-nauty-validation.md` records their evidence.

The published comparison contains six series: Hex dense, Hex sparse, dense
nauty, sparse nauty, Traces, and IsoGraph. Preserve its corpus, measurement
protocol, timeouts and historical samples. Its report identifies the proved
sparse guarantees and the provenance of each series. The representation
choices follow measured construction, search, checked-label and output costs.
Further improvements to array ownership, storage, iteration or specialization
must preserve the pinned algorithmic decisions and exact conformance results.
Compare candidates with adjacent AB/BA arms under the shared-host protocol,
retain the baseline and every completed sample, and prove replacements for
already verified helpers. Refresh affected figures after selecting the
improvements and whenever later executable changes warrant it.

Release requires the unconditional sparse theorem surface, exact C
conformance, kernel replay on non-toy coloured and uncoloured goals,
preserved dense behaviour, published-library build coverage, and recorded
performance evidence. Sparse representation files ship through the existing
`HexGraph` managed directory in `hex-graph-iso`; the library pair and CI job
structure do not change.

## References

- Brendan D. McKay,
  Practical graph isomorphism, Congressus Numerantium 30 (1981), 45-87.
- Stephen G. Hartke and A. J. Radcliffe,
  McKay's canonical graph labeling algorithm,
  Communicating Mathematics, Contemporary Mathematics 479 (2009), 99-111.
- Brendan D. McKay and Adolfo Piperno,
  [Practical graph isomorphism, II](https://arxiv.org/abs/1301.1493).
- Brendan D. McKay and Adolfo Piperno,
  [nauty and Traces User's Guide, version 2.9.3](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf).
- Milan Banković, Ivan Drecun, and Filip Marić,
  [A proof system for graph (non)-isomorphism verification](https://arxiv.org/abs/2112.14303).
- Adolfo Piperno,
  [nauty and Traces performance families](https://pallini.di.uniroma1.it/StronglyRegular.html).
