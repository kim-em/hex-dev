# hex-graph-iso (coloured graph canonical labelling)

`hex-graph-iso` computes canonical forms and isomorphisms of finite simple
undirected graphs with ordered vertex colours. It depends only on
`hex-graph`. It does not depend on Mathlib or on an external graph program.
The separate [hex-graph-iso-mathlib](hex-graph-iso-mathlib.md) library relates
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

## Scope

The first release includes:

- finite simple undirected graphs on `Fin n`;
- an ordered, nonempty list of colour cells;
- a total canonical-form operation and the label producing that form;
- a budgeted canonical-form operation;
- a Boolean isomorphism decision and one isomorphism when one exists;
- positive and negative certificate checking;
- the Mathlib-free `graph_iso` tactic for closed executable graphs;
- exact compatibility with the pinned dense nauty configuration below.

The first release does not include directed graphs, loops, parallel edges,
sparse-nauty compatibility, Traces, user vertex invariants, or a public
permutation-group implementation. It may discover automorphisms internally
for pruning, but it makes no claim that the discovered automorphisms generate
the complete automorphism group. Complete generators, stabilizer chains, and
explicit isomorphism cosets are later work.

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
- A nonempty uncoloured graph uses `k = 1` and the constant zero vector.
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

def canonicalize (G : Colored n k) : CanonResult n k
def canon (G : Colored n k) : Colored n k := (canonicalize G).form
def label (G : Colored n k) : Label n := (canonicalize G).label

def findIso (G H : Colored n k) : Option (Perm n)
def isIso (G H : Colored n k) : Bool
```

`canonicalize` is total. Termination follows from the strictly increasing
number of singleton cells along each individualization path and finite
branching. Its worst-case running time can still be factorial.

The resource-bounded surface separates search limits from replay limits:

```lean
structure SearchLimits where
  maxNodes : Nat := 100000
  maxCertNodes : Nat := 100000

structure ReplayLimits where
  maxCheckerSteps : Nat := 5000000

def findIso? (search : SearchLimits) (G H : Colored n k) :
    Option (Option (Perm n))

def checkIso? (replay : ReplayLimits) (G H : Colored n k)
    (p : Perm n) : Option Bool

def canon? (search : SearchLimits) (replay : ReplayLimits)
    (G : Colored n k) : Option (CanonResult n k)
```

`maxNodes` counts every refined partition visited, including the root.
`maxCertNodes` counts every proof-rule record emitted. Replay work charges one
step for each proof-rule record, vertex or permutation entry inspected, and
dense adjacency word inspected. All counters use checked `Nat` arithmetic.
An implementation may account conservatively — refuse up front by charging an
upper bound on a counter, or charge whole-certificate record counts — provided
accepted work never exceeds the declared budget; exhaustion may therefore be
reported for inputs an exact counter would have admitted.
For `findIso?`, outer `none` means exhaustion, `some none` is a completed
non-isomorphism result, and `some (some p)` is a found transporter. For the
other bounded operations, exhaustion also returns `none`. Exhaustion is not
evidence of non-isomorphism.

The required API theorems include:

```lean
theorem relabel_label (G : Colored n k) :
    relabel G (label G) = canon G

theorem canon_iso (G : Colored n k) :
    Isomorphic G (canon G)

theorem canon_invariant {G H : Colored n k} :
    Isomorphic G H -> canon G = canon H

theorem iso_iff_canon_eq (G H : Colored n k) :
    Isomorphic G H <-> canon G = canon H

theorem findIso_isSome_iff (G H : Colored n k) :
    (findIso G H).isSome = true <-> Isomorphic G H

namespace FindIso

theorem some_sound (search : SearchLimits)
    (G H : Colored n k) (p : Perm n) :
    findIso? search G H = some (some p) -> IsIso G H p

theorem none_sound (search : SearchLimits)
    (G H : Colored n k) :
    findIso? search G H = some none -> Not (Isomorphic G H)

end FindIso

theorem isIso_eq_true_iff (G H : Colored n k) :
    isIso G H = true <-> Isomorphic G H

theorem isIso_eq_false_iff (G H : Colored n k) :
    isIso G H = false <-> Not (Isomorphic G H)
```

The biconditional compares canonical coloured graphs. It does not compare
`label G` and `label H`: those arrays refer to different input vertex names
and generally differ for isomorphic inputs.

## Reference canonical form

`Hex.GraphIso.Reference` contains the first implementation. It first constructs
the colour-sorting label, which lists vertices by increasing colour and then
by original vertex. It enumerates all permutations of the label entries within
each contiguous output cell, relabels the graph, and selects the largest
serialized coloured adjacency matrix under an explicitly defined lexicographic
order. The order compares cell sizes first and then upper-triangle adjacency
bits in row-major order.

This definition has its own proofs of `relabel_label`, `canon_iso`, and
`iso_iff_canon_eq`. It is suitable for exhaustive small tests and for checking
later implementations. It is not used as a production fallback and is not
required to return nauty's label or canonical form.

The public `canon` is backed by the certificate-checked nauty-semantic
canonicalization: an untrusted branch-and-bound producer whose output is
validated by the proven certificate replay, with a provably total
exhaustive fallback. Development namespaces (`Reference`, `Nauty`)
remain available as the cross-check and the transcription layer.

## nauty-compatible individualization and refinement

The production search is derived from the pinned nauty source. Its state
contains an ordered partition, the active cells, the individualized vertices,
the refinement code at each level, the first-path and best-so-far data, and
the automorphisms and orbit information justified so far.

The following behavior is fixed before adding pruning:

1. Initial vertices occur in `(colour, original vertex)` order.
2. Equitable refinement uses the same splitter order, count buckets, cell
   order, and refinement-code arithmetic as dense nauty.
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

## Canonical certificates

The negative tactic cannot prove non-isomorphism by checking a proposed
permutation. It needs evidence that each reported form is canonical. The
certificate design follows Banković, Drecun, and Marić's
[proof system for graph (non)-isomorphism verification](https://arxiv.org/abs/2112.14303),
adapted to the exact ordered-colour and nauty-selection rules in this SPEC.

`CanonCert` is plain data. It records enough information to replay:

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
def certify? (limits : SearchLimits) (G : Colored n k) : Option CanonCert

def checkCanon (limits : ReplayLimits) (G : Colored n k)
    (cert : CanonCert) : Option (CanonResult n k)

theorem checkCanon_sound
    (h : checkCanon limits G cert = some result) :
    result.form = canon G ∧ relabel G result.label = result.form

theorem canon?_eq_some
    (h : canon? search replay G = some result) :
    result.form = canon G ∧ relabel G result.label = result.form
```

The producer/checker agreement theorem states that a successful in-Lean
producer result is accepted when its replay limit is at least the work count
reported by the producer. The tactic nevertheless treats compiled producer
output as untrusted and calls `checkCanon` before emitting anything.

For a negative decision, `DiffCert` names the first differing field in the
canonical encodings. `checkDiff` verifies the two encodings agree before that
position and differ there. The proof is exactly the composition of two
`checkCanon_sound` applications, `checkDiff`, and `iso_iff_canon_eq`.

Certificate size and checker work are proportional to the justified search
tree. The SPEC makes no promise that negative certificates are short on every
input.

## The Mathlib-free `graph_iso` tactic

The library registers `graph_iso` for closed goals over executable
`Colored n k` values:

```lean
example : Isomorphic G H := by
  graph_iso

example : Not (Isomorphic G H) := by
  graph_iso

example : Isomorphic G H := by
  graph_iso (maxNodes := 200000) (maxCheckerSteps := 10000000)
```

The configuration syntax is the parenthesized named syntax shown above.
Each of `maxNodes`, `maxCertNodes`, and `maxCheckerSteps` is optional, may
appear in any order, and may appear at most once. Bare `graph_iso` uses all
three defaults.

For a positive goal, compiled `findIso?` search returns a literal forward
permutation under `maxNodes`. The tactic emits that permutation and closes the
goal through replay-bounded `checkIso?` and its soundness theorem. It need not
compute complete canonical certificates. Search or replay exhaustion leaves
the goal unchanged.

For a negative goal, the tactic's primary path is the certificate
route: the compiled search produces a canonical-key certificate for
each graph, and the kernel replays the two Boolean certificate checks
and their key comparison, closing the goal through
`not_isomorphic_of_checkKeys` (`checkKey` twice plus `checkDiff`, with
no achieving labelling reified). When certificate production fails or
a certificate exceeds the configured budgets, the tactic falls back to
replaying the fully verified pairwise individualization-refinement
decision (`decideIso?_not_isomorphic`) under `maxNodes`; the fallback
also anchors the exhaustion semantics. No result relies on compiler
trust. The pairwise replay was the original primary path; measurement
retired it: kernel-replaying the pairwise search costs tens of seconds
on twenty-vertex regular pairs, while certificate replay scales with
certificate size once the producer emits automorphism prunes
(code-prune-only certificates measured thousands of records against
nauty's tens of visited nodes on the same graphs).

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

The chapter evaluates `findIso?` to display the explicit vertex permutation,
then uses `graph_iso` to prove that the first two presentations are isomorphic.
The text explains how an outer pentagon, inner star, and spokes become disjoint
pairs. It then uses the same tactic to prove that the Petersen graph is not
isomorphic to the pentagonal prism. This negative example is
interesting because both graphs have ten vertices and every vertex has degree
three. Degree refinement alone does not settle it.

The chapter also gives the Petersen graph three ordered two-colourings with
identical cell sizes. Two colourings mark different edges as colour zero.
`graph_iso` proves them isomorphic and returns a colour-preserving transporter.
The third marks a nonadjacent pair as colour zero. `graph_iso` proves it is not
isomorphic to either edge-marked colouring. This is the manual's compact
illustration that ordered colours constrain isomorphisms and are not merely
refinement hints.

All constructors used by the chapter are ordinary Lean definitions in the
chapter or public graph operations. The example is compiled with the manual,
records explicit logical limits, and does not depend on an external nauty
installation. The Mathlib companion presents the same positive and negative
claims through `SimpleGraph`. Its requirements are stated in
[hex-graph-iso-mathlib.md](hex-graph-iso-mathlib.md#manual-example-with-mathlib).

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

The oracle follows [the project oracle protocol](../testing.md#adding-a-new-oracle).
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
Conformance runs in the existing single Ubuntu job. It does not add a job,
matrix, or workflow.

Property checks independent of nauty include:

- `relabel G (label G) = canon G`;
- invariance under deterministic random relabelling;
- colour preservation and contiguity;
- agreement with `Reference.canon` on the isomorphism verdict;
- agreement among all retained implementation stages on their common domain;
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

- `Reference.canon` on factorially feasible sizes;
- the unpruned implementation and every retained pruning stage on common
  inputs;
- public `canonicalize`, `findIso`, and `isIso`;
- dense conversion, one complete refinement, relabelling, canonical graph
  comparison, certificate generation, and certificate replay;
- the pinned nauty comparator through a benchmark-only in-process FFI
  binding (`Hex.BenchOracle.Nauty` over
  `Hex/BenchOracle/ffi/nauty_canon.c`), statically linked against the
  vendored nauty 2.9.3 source in `vendor/nauty-2.9.3` — the FFI
  pattern of
  [benchmarking.md](../benchmarking.md#external-comparators). The
  vendored source and the comparator are development-monorepo tooling
  only and ship with no released library.

Every canonicalization result is hashed from its ordered cell sizes,
upper-triangle adjacency bits, and label. `compare` therefore checks exact
result agreement as well as timing. The nauty comparator is `gating` in the
terminology of [benchmarking.md](../benchmarking.md#external-comparators), but
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
2. The reference and production biconditional theorems are complete.
3. `canon?_eq_some` and `checkCanon_sound` have the conclusions stated above.
4. Every implemented prune has an answer-and-label preservation proof.
5. The exhaustive merge fixture and extended `n = 6` campaign agree exactly
   with nauty 2.9.3.
6. The non-toy positive and negative tactic cases replay through the kernel.
7. The benchmark driver reports every implementation stage and the nauty
   comparator without importing Mathlib.

Complete automorphism generators are not a release condition. If later work
adds them, checking that each permutation is an automorphism is only
soundness. A completeness theorem must show that the reported generators
generate every automorphism, using the same canonical search tree or an
equivalent complete argument.

## References

- Brendan D. McKay and Adolfo Piperno,
  [Practical graph isomorphism, II](https://arxiv.org/abs/1301.1493).
- Brendan D. McKay and Adolfo Piperno,
  [nauty and Traces User's Guide, version 2.9.3](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf).
- Milan Banković, Ivan Drecun, and Filip Marić,
  [A proof system for graph (non)-isomorphism verification](https://arxiv.org/abs/2112.14303).
- Adolfo Piperno,
  [nauty and Traces performance families](https://pallini.di.uniroma1.it/StronglyRegular.html).
