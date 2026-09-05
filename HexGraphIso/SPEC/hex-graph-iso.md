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
specification's tree, the certificate checker, and the transcribed search
all seed a child node's refinement code with the parent's recomputed cell
count, exactly as nauty does. The declarative characterization behind
requirement 1 (the canonical key is the maximum leaf key of the unpruned
tree) does not depend on that seeding choice. Sharing it makes the
search's recorded codes directly comparable with the checker's.

## Scope

The first release includes:

- finite simple undirected graphs on `Fin n`;
- an ordered, nonempty list of colour cells;
- a total canonical-form operation and the label producing that form;
- a Boolean isomorphism decision and one isomorphism when one exists;
- a replay-bounded check of a proposed isomorphism;
- positive and negative certificate checking;
- the automorphism generators the pinned traversal discovers, with the
  vertex orbits, the orbit count and the group order;
- the Mathlib-free `graph_iso` tactic for closed executable graphs;
- exact compatibility with the pinned dense nauty configuration below.

The first release does not include directed graphs, loops, parallel edges,
sparse-nauty compatibility, Traces, user vertex invariants, or a general
permutation-group implementation. Every returned generator is proved to be
an automorphism, and the orbit array is proved sound, but the release makes
no claim that the returned generators generate the complete automorphism
group; see [Automorphism generators](#automorphism-generators). Stabilizer
chains and explicit isomorphism cosets are later work.

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
- A checked edge-list builder rejects out-of-range endpoints, removes
  duplicate undirected edges, and produces sorted duplicate-free adjacency
  arrays.
- Relabelling by a finite bijection is executable and has an adjacency
  correspondence theorem.

The public graph stays in that representation. `hex-graph-iso` owns a private
dense bit matrix used by refinement and canonical comparison. The conversion
to the bit matrix is proved to preserve adjacency. The private representation
does not introduce a storage typeclass into `hex-graph`.

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
checked-label transcription of the pinned nauty search, run directly
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
without running it: the proven replay accepts the transcription's own
answer on every input (`Nauty.certifyCanon?_isSome`, the theorem of
[Verified search refinement](#verified-search-refinement)), the
transcription is `Option`-valued only in its executable spelling and
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

The replay-bounded permutation check charges its work against a single
limit structure:

```lean
structure ReplayLimits where
  maxKernelSteps : Nat := 5000000

def checkIso? (replay : ReplayLimits) (G H : Colored n k)
    (p : Perm n) : Option Bool
```

Replay work charges one step for each proof-rule record, vertex or
permutation entry inspected, and dense adjacency word inspected. All
counters use checked `Nat` arithmetic. An implementation may account
conservatively (refuse up front by charging an upper bound on a
counter, or charge whole-certificate record counts) provided accepted
work never exceeds the declared budget. Exhaustion may therefore be
reported for inputs an exact counter would have admitted. Exhaustion
returns `none` and is not evidence of non-isomorphism.

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
Because the transcription replays nauty's traversal exactly, the list
is deterministic and conformance-pinnable, not merely the group it
generates. `orbits` is the vertex-orbit array `orbjoin` builds from
those generators, which is the array nauty reports; every entry is the
representative of its orbit, and `numOrbits` counts the
representatives. `order` is computed by the orbit-stabilizer
chain: individualize a vertex of a non-singleton orbit, whose
stabilizer is the colour-preserving automorphism group of the
individualized colouring, recurse on that, and multiply the orbit
lengths. It is the order of the automorphism group exactly when each
level's orbit array is the true orbit partition, and a lower bound
otherwise, since a computed orbit is always contained in the true one.
It is not the order of the group generated by the reported generators
either: the stabilizer factors come from separate runs on the
individualized colourings, not from that list.

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
    (autos G).orbits[u]! = (autos G).orbits[v]! -> SameOrbit G u v
```

Membership belongs to the checker, not to the producer. `autom?`
rebuilds each recorded array as a permutation of `Fin n` and runs the
same `checkIso` the isomorphism surface uses, against the graph and
itself, so a producer defect can only lose a generator and never admit
a non-automorphism. Orbit soundness descends from the search's own
orbit bookkeeping (`Nauty.orbjoin_orbConn`): every parent pointer is
justified by a forward word over the checked generators, and a word of
automorphisms composes to an automorphism.

Generation is a further contract, and it is not yet proved. The
intended statement is that the returned set generates the whole
automorphism group, so that no automorphism lies outside the group it
generates, distinct orbit representatives really are distinct orbits,
and `order` really is the order of the automorphism group rather than
a lower bound obtained from orbits that may be too fine. That direction is a counting argument: a verified
orbit-stabilizer chain for the returned set establishes the exact
order of the group it generates, and the matching count of the full
automorphism group comes from the search's leaf and orbit accounting,
so membership gives a subgroup and equal cardinality gives equality.
Until that argument is in place, `numOrbits` and `order` stand exactly
where the search counters stand: conformance-pinned observables, which
the external nauty oracle compares exactly on every automorphism
fixture and which no Lean theorem states.

A tactic for automorphism goals waits on the same argument. Proving a
given permutation is an automorphism needs nothing beyond `checkIso`,
but a stated group-order fact, and its Mathlib counterpart about the
order of the automorphism group of a `SimpleGraph`, is exactly the
statement generation supplies, so the goal forms are settled here and
the tactic follows the theorem.

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
`Graph.autos_orbits_lt` and `Graph.autos_sameOrbit` the uncoloured
readings of the four coloured theorems.

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

The public `canon` is the checked-label transcription of the nauty
search. Its theorems come from the certificate replay, which is proved
to accept the transcription's answer on every input. The `Nauty`
namespace holds that transcription and the declarative `canonSpecKey`
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

The first release keeps `schreier = false`, matching the pinned defaults. A
later complete automorphism-group API may add a permutation-group dependency,
but it must not silently change `canon` or `label`.

One known divergence from the pinned source remains, and it is to be
removed rather than adopted. At a discrete node whose refinement codes
agree with the first leaf's along the whole path, `nauty.c:934-940`
admits the code-1 automorphism when
`gca_first >= noncheaplevel || isautom(..)`, skipping the `isautom` scan
inside a subtree the cheap guard has already cleared. The Lean search
(`Nauty.processnode` in `HexGraphIso/Nauty/Search/Search.lean`) instead
requires the refinement code at the next level to be `codeSentinel`, and
always runs `isautom`. The two tests admit the same leaves except on a
collision of the fifteen-bit refinement code, which neither the committed
fixture corpus nor the campaign exercises, so no conformance run
distinguishes them. The Lean search pays one `isautom` scan per code-1
leaf inside a cheap subtree for the difference. Restoring nauty's test
needs the all-leaves theorem for a cheap subtree, which is proved
(`Nauty.descPath_leafRows_all`).

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
returns `none` on exhaustion. It does not search: the transcribed search
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
single `Nauty.checkCanon` replay of the transcription's labelling. Its
content is the equality of the declarative key with the key the
transcription installs:

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
| `Nauty/Search/` | the executable transcription: packed vertex sets (`VSet`), `refine`, `processnode`, and the four mutually recursive functions `firstPathNode`, `firstChildLoop`, `otherNode` and `otherChildLoop`. This is the hot path and the only part a caller's run touches. |
| `Nauty/Spec/` | the declarative canonical form `canonSpecKey` and `specCanon`, its invariance under isomorphism (`specCanon_invariant`, `iso_iff_specCanon_eq`) and its achievement by a reachable labelling (`specCanon_iso`), with the equivariance and cell-permutation theory both proofs use. |
| `Nauty/Cert/` | the certificate data, the trusted `checkCanon` replay with `checkCanon_sound`, the untrusted trace-driven producer, and the replay spine proving the producer's certificate is accepted whenever the claimed key dominates the subtree and every recorded generator is a checked automorphism. |
| `Nauty/Correct/` | the induction proving `canonSpecKey_eq_tracedKey`. It runs over the executable recursion's fuel, with the first-path and off-path node statements proved together, and it carries the unwinding and sweep-coverage bookkeeping the imperative return codes need. |
| `Nauty/Invariant/` | the per-event facts about the search state the induction applies at each arm: refinement-code comparison, leaf faithfulness, domination, orbit soundness, generator-store validity, cell reachability, and target-cell agreement. |
| `Nauty/Equitable/` | `refine` returns a partition equitable with respect to the exhausted active set. |
| `Nauty/SmallCell/` | the `cheapautom` theory: for an equitable partition passing nauty's cheap guard, the cell stabilizer in the automorphism group acts transitively on every cell (`stabilizer_transitive`), and every leaf of the subtree below such a node realizes an automorphism with the first leaf (`descPath_leafRows_all`). |
| `Nauty/Model/` | an abstract pruned evaluator of `canonSpecKey`, proved to compute the pairwise maximum of an incumbent and an unpruned subtree key. No declaration on the theorem path uses it. It is kept as a source of lemmas about pruning stated without the imperative state. |

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

Totality transports from the certificate pipeline to the transcription
through `Nauty.searchResult?_eq_of_certifyCanon`, and the theorem
surface of [Public operations](#public-operations) is the declarative
form's theorem surface transported along `canon_eq_specCanon`. No
certificate is produced or replayed on the answer path. Certificates
and the replay checker remain as the proof layer for the `graph_iso`
tactic, whose kernel obligations must stay certificate-sized.

Label-level agreement is available only along this route. The checker
pins a labelling's rows, not the labelling itself, so an exhaustive
fallback that selects some other member of the automorphism coset
could not be identified with the transcription's label. The fallback
has to be proven unreachable, which is exactly the theorem.

No theorem in this library depends on the transcription being faithful
to nauty. `canonSpecKey` is a Lean definition, every statement above is
about it, and replacing the transcription with any other search that
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
  graph_iso (maxSearchNodes := 200000) (maxKernelSteps := 10000000)
```

An uncoloured goal is coloured with the single colour zero and its
conclusion transported back through `Graph.isomorphic_singleColor_iff`,
so both shapes run the same routes below. Both directions of that
equivalence are proof terms, so the uncoloured route adds nothing to
the kernel obligation beyond one decision of `0 < n`.

The configuration syntax is the parenthesized named syntax shown above.
Each of `maxSearchNodes`, `maxCertRecords`, and `maxKernelSteps` is
optional and may appear in any order. Bare `graph_iso` uses all three
defaults.

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
configured budgets. The kernel replays the two Boolean certificate
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
and reports the group order. Both examples state, where the number is
used, that the orbit count and the group order are conformance-pinned
against nauty rather than theorems, per
[Automorphism generators](#automorphism-generators).

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
the generator count the transcribed search reports, the orbit array, the
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

The scheduled and local campaign adds all 32,768 labelled graphs at `n = 6`,
larger deterministic random cases, and the hard families below. These cases
stream directly to the oracle. Only failures are retained as replay records.
`conformance/HexGraphIso/EmitCampaign.lean` is the emitter, and
[reports/hex-graph-iso-campaign.md](../../reports/hex-graph-iso-campaign.md)
records the current run: machine, date, toolchain, comparator version, case
count, what was compared, runtime, and outcome. A campaign re-run replaces
that report in place. Conformance runs in the existing single Ubuntu job. It
does not add a job, matrix, or workflow.

The emitters and the twin runner read one shared corpus,
`conformance/HexGraphIso/Cases.lean`, so every driver runs the same
cases in the same order. `conformance/HexGraphIso/EmitFixtures.lean`
writes the committed fixture, `conformance/HexGraphIso/EmitCampaign.lean`
streams the campaign, and both take an `--engine` mode that reads each
record off the second canonical search instead of the transcription, so
the external nauty oracle pins either search on the same cases.
`conformance/HexGraphIso/EngineTwin.lean` builds the executable
`hexgraphiso_engine_twin`, which runs both searches on every fixture,
automorphism and campaign case and compares the whole traversal rather
than only its answer: the label, the canonical graph, the seven run
statistics, the accepted automorphisms in discovery order, and the best
path's refinement codes. The first disagreement is printed with the
differing fields and the case, and the run exits non-zero. Until the
structured search exists the second search is the transcription itself,
so the twin and the `--engine` modes compare it with itself.

Property checks independent of nauty include:

- `relabel G (label G) = canon G`;
- invariance under deterministic random relabelling;
- colour preservation and contiguity;
- agreement with the declarative canonical form at factorially feasible
  sizes: `Nauty.specCanon G = canon G` and the isomorphism verdict read
  off `Nauty.canonSpecKey`, which is the only cross-check of the public
  answer this library still carries;
- agreement between the transcription and the second canonical search on
  every case of the fixture corpus and the campaign, through the twin
  runner above;
- rejection of a changed edge, colour, permutation entry, refinement record,
  automorphism, prune record, leaf comparison, or difference position in a
  certificate;
- `none`, never `false`, after search or replay exhaustion.

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

Every canonicalization result is hashed from its ordered cell sizes,
upper-triangle adjacency bits, and label. `compare` therefore checks exact
result agreement as well as timing. The nauty comparator is `gating` in the
terminology of [benchmarking.md](../../SPEC/benchmarking.md#external-comparators), but
the first release sets no speed-ratio requirement. Its required result is
exact output agreement.

The registrations report wallclock, allocation, result hash, visited nodes,
refinement calls, canonical updates, automorphisms checked, branches pruned,
certificate records and bytes, and checker steps. `relabel` and graph
comparison declare quadratic bit-matrix models. A full dense refinement
declares a conservative cubic model. Canonical search declares no polynomial
model in `n`. Reports use node count and per-node work to explain its cost.
Certificate replay is modelled against certificate records plus the charged
vertex, permutation-entry, and adjacency-word visits.

Merge CI runs a small deterministic subset and keeps the complete `Bench
verify` invocation inside its existing time limit. Hard families and full
nauty timing comparisons run in the existing scheduled performance workflow
on dedicated hardware.

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

The `engine` mode of `hexgraphiso_cactus` times the two canonical
searches against each other on the same materialized instance and
records `lit_ns`, `eng_ns`, `nauty_ns`, `nodes` and `eng_nodes` for
every instance of the sweep corpus.
`scripts/bench/graphiso_engine_compare.py` reads that run and prints,
per family, the geometric mean of `eng_ns/lit_ns` and of
`eng_ns/nauty_ns` together with each search's per-node cost exponent,
so a constant-factor difference and a difference that grows with `n`
are reported apart. Two searches with the same traversal visit the
same nodes, so any instance whose `eng_nodes` differs from its `nodes`
fails the run whatever the timings say. This is how a replacement
search is measured before any proof about it is written.
`bench/HexGraphIso/Profile.lean` times the same pair as its `run` and
`erun` stages on the paley61, kneser72 and circulant64 instances, next
to the certificate stages, and
`scripts/bench/graphiso_perf_side_by_side.sh` attributes the samples of
one `perf record` of `hexgraphiso_cactus` to compiled Lean search code,
instance construction, bignum arithmetic, the Lean runtime and the
vendored nauty.

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

The first release requires all of the following:

1. No `sorry`, axiom, or `native_decide` occurs in the library or tactic
   correctness path.
2. The declarative biconditional `Nauty.iso_iff_specCanon_eq` and the
   public biconditional `iso_iff_canon_eq` are both complete.
3. `Nauty.checkCanon_sound` has the conclusion stated above.
4. The pruned search is proved to compute the declarative canonical key
   (`Nauty.canonSpecKey_eq_tracedKey`), so every prune it performs
   preserves the selected form and the selected label.
5. The exhaustive merge fixture and extended `n = 6` campaign agree exactly
   with nauty 2.9.3. The fixture leg runs in merge CI. The campaign leg is
   recorded in
   [reports/hex-graph-iso-campaign.md](../../reports/hex-graph-iso-campaign.md).
6. The non-toy positive and negative tactic cases replay through the kernel.
7. The benchmark driver reports the declarative key, the public
   operations, the automorphism surface, the certificate stages and the
   nauty comparator without importing Mathlib.

Complete automorphism generators are not a release condition. If later work
adds them, checking that each permutation is an automorphism is only
soundness. A completeness theorem must show that the reported generators
generate every automorphism, using the same canonical search tree or an
equivalent complete argument.

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
