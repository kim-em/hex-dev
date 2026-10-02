# Sparse nauty verification plan

The target is the native, optimized port of sparse nauty 2.9.3. Preserve its
pinned algorithmic choices and the dense API and traversal. Traces remains a
comparator. The six-way performance publication and optimization pass are
established dependencies; verification follows the measured executable.
Publication through the monorepo release mechanism is separate from completing
this plan.

## Established dependencies

The native sparse representation, builders, equality, conversions, relabelling,
optimized normalization and packing, inverse-label semantics, executed
adjacency automorphism checker, and exact stable initial partition have proofs.
The supplied-transporter checker and its literal kernel replay have soundness
and completeness theorems. Production maximum correctness and the total
coloured and bare canonicalization/decision contracts are proved. The full
emitted sparse generator trace generates exactly the colour-preserving
automorphisms, including at order zero. Native orbit representatives and
counts are exact; coloured and bare `autos` expose the actual single-traversal
results. Every first-path index is the exact full stabilizer-orbit size,
and the executed order accumulator equals the full group cardinality. The Mathlib
bridge supplies direct encoding, adjacency and colouring correspondence,
enumeration-independent canonical forms, complete decisions and transporter decoding,
full decoded automorphism generation, exact orbit quotients and their cardinalities,
and the order of the full decoded automorphism group.
`refineWith_congr` proves complete literal refinement-result equality for
identical inputs with arbitrary bounded scratch, including label order,
partition, active set, ordered queue, count and hash.
The sparse canonical certificate checker is sound for discrete leaves,
strict code pruning and full child expansion. Its unlimited expansion producer
is complete and consumes the optimized production key and literal label from
one search. Literal replay equals the specification checker, with exported
iterator, parser and relabelling operations. Imported-module kernel tests check
the recorded order-12 random keys and prove the negative pair, as well as
rejecting malformed child lists and terminal codes. Compact automorphism
records and certified canonical-result packaging are proved, with equivalent
literal replay. The bounded native search counts actual visits, shares a quota
across input pairs and stops native callbacks after exhaustion. Bounded compact
production charges exact emitted records and preserves the unlimited producer's
tree on success. Its exact unlimited size is proved sufficient; exhaustion occurs
exactly below that size. Both tactic proof routes use these bounded producers.
Public coloured and bare sparse tactic dispatch is integrated. Imported Mathlib
sparse replay examples cover ordered-colour positive/negative pairs, empty
graphs and changed finite enumerations. Imported CFI replay passes four fresh
builds with the ordinary sparse tactic. All acceptance checks pass, including
the full build, published trust/import audits, exact C conformance, fresh
six-way plots, native path scaling, and separate automorphism/certificate
measurements. The evidence is in [the validation report](sparse-nauty-validation.md).
Sparse kernel replay uses
Lean's actual resource controls; there is no separate replay-cost estimate.

The sparse key order is lawful. Partial canonical storage describes row
permutations and allocated capacity. Canonical installation preserves the
literal shared prefix and installs native relabelled adjacency, including
from the initial blank buffer; relabelling preserves degrees and total
neighbour allocation. The exact sort has permutation and size contracts,
sortedness and unchanged exterior for its insertion branch, and membership
of both pivot schemes in the sampled segment. The executed partition's
recursive fragments strictly decrease total pending length. The induction
principle for the actual bounded stack loop establishes exhaustion and
supports full-sort exterior and segment-permutation theorems. The partition
scans exhaust their unclassified interval; the final block swaps put equal
pivot keys between the strict lower and upper fragments. Full indirect-sort
key ordering follows through the actual work stack.

The executed canonical comparison returns the sparse graph-key sign and
the exact equal-row prefix. Its tie criterion is native graph equality.
The cursor, mark, and least-unmatched-neighbour invariants establish these
results for unsorted working rows. Comparison between two labels of the
same graph supplies the prefix and capacity needed by canonical installation,
including for order zero.

The executed cell-index builder has bounded-loop exhaustion and full cache
correctness proofs. Nonsentinel lookups identify their complete containing
cell and array bounds. Scratch validity records allocation and generation
bounds with conditional partition-index correctness. Target selection preserves
that validity while borrowing counts; invalidation permits a changed partition.
These contracts do not assume that stale counts are zero.

The executed cached target selector computes the first maximum of all partial
join counts, including self-joins. The proof follows both neighbour passes:
counts accumulate correctly, each joined cell contributes at most once, and
its entry is cleared before the next representative. The enumeration's fixed
bound exhausts the ordered nontrivial cells. Two valid caches agree on the
chosen target despite arbitrary initial hits and unused endpoint entries.
The fresh selector's compact-index scatter and count loops compute the same
scores and first maximum. Fresh/cached best-cell equality includes empty
partitions. Complete dispatch agreement gives the exact position, vertex set,
and size when a nontrivial cell exists, including hints, the depth cutoff,
and invalidated-cache fallback.

The executed count, singleton, and nontrivial splitters add at most one
activation per new cell. This includes distance splitting and replacing the
largest fragment's queue entry. The packed active scan has ordering,
uniqueness, coverage, and cardinality bounds. If the initial active cardinality
is at most the cell count, the actual refinement loop reaches an empty queue
or its cell-count stopping condition within its existing `n` iterations.
Exact cell accounting identifies that condition with discreteness. The full
certificate-preservation theorem proves equitability at either exit.
Count splitting preserves the computed hits, mark arrays, generation stamp,
cache flag, and label, partition, and index array allocations in every branch.
Persistent scratch bounds survive these splits. The actual search storage
invalidation admits a changed partition, and canonical installation preserves
the existing scratch validity.
The executed count splitter permutes labels within its nonempty bounded window,
leaves exterior positions fixed, and preserves all incoming cell multisets
when that window is a partition cell. The sequential insertion reads, including
coinciding cuts, and the actual indirect-sort branch are covered.
It also orders the whole cell by hit values when the initial key is below its
second-minimum sentinel. The proof follows the equal-count scan, all five
insertion arms, and sorting of the larger-count tail. Under the local count
bound, the executed splitter writes exactly the boundaries between unequal
adjacent counts, retaining every other partition value. The proof includes
exhaustion of its bounded tail scan. Its output cells are exactly maximal
constant-count runs, with cell nesting and unchanged exterior partition data.
The executed count splitter preserves full index validity, including singleton
sentinels and entries outside the split. The proof follows both initial
fragments and every bounded tail-scan transition. It requires a valid incoming
cache, a bounded partition cell, a valid label permutation, partition allocation,
and the local hit bound. Local permutations retain label bounds and injectivity
through all insertion arms. Native neighbour scans establish exact counts on
touched nontrivial cells, including first-touch clearing, repeated neighbours,
and skipped singleton cells. Every count is bounded by the splitter size.
The complete nontrivial pass preserves the label permutation, partition
allocation, and cache validity, including every pending touched cell. Both
full passes preserve the vertex multiset of every original partition cell.
The nontrivial pass makes the native count into its captured splitter constant
on every output cell. This includes untouched cells, whose semantic counts
are zero despite unrestricted retained scratch. `CountPending` follows the
actual touched-cell fold and preserves completed disjoint cells.
`splitSingleton_constant` proves the corresponding native row-count guarantee
for the complete singleton pass. `SingletonPending` covers untouched zeros,
uniform cells, and the binary fragments produced by compaction and reverse fill.
`splitSingleton_active` proves that every fragment of an active original cell
is active and every other original cell has at most one inactive fragment.
`ActiveCells` composes this rule over disjoint original cells. The complete
count splitter and nontrivial pass prove the same activation rule, including
largest-fragment replacement. `ActiveSpan` tracks activation of every interior
fragment and bounds all appended queue entries inside the original cell;
replacement therefore leaves outside membership unchanged. `NativeCounts`
identifies the executed native count with shared set-intersection cardinality.
`PassCert` proves certificate preservation for both actual main-loop branches,
including the selected queue entry's swap/pop removal and hash update.
These results use only a proof projection of partition fields, not execution
of dense refinement.
`DistanceAdj` identifies distance-one vertices with native neighbours, including
small graphs and unreachable sentinels. `DistanceRun` proves constant distance
classes and fragment activation for the literal distance loop. `DistanceCert`
transports the certificate through that branch. `RefineCert` preserves it
through the complete executed refinement; `refineWith_equitable` combines this
with exact counting and stopping. `initial_cert` derives the root certificate
from initial colour-cell activation, and `initial_equitable` proves the actual
root refinement equitable for every nonempty input.
`ChildEntry` proves that the executed sparse child policy preserves the label
permutation, supplies the next level's valid partition and exact count, and
derives its certificate from parent equitability. `Descent` composes this with
the production visit, yielding equitable children with valid scratch and
exact counts. `TargetValid` derives nontrivial-cell existence, checked-label
success, and the fresh/cached target's bounded cell contract from node facts.
`SpecTree` defines the finite unpruned sparse tree using executed fresh sparse
refinement, hint-free targets, and every target member. `SpecFuel` proves
nonemptiness for valid inputs and all coloured roots, including the empty
graph. `SpecBound` proves that every larger sufficient fuel enumerates exactly
the same leaves, covering all children. `SpecMax` defines the lawful sparse
maximum with a reachable attaining label and proves domination of every leaf.
`SpecTransport` transports every executed leaf under isomorphism and
within-cell reordering. `SpecIso` proves invariance of the maximum;
`SpecCanon` proves canonical-form invariance and the isomorphism biconditional,
including order zero. `MaxResult.run_max` identifies the nonempty production
key with this maximum; `Sparse.Canonical.canon_eq_specCanon` proves equality
of the total public forms at every order, including zero.
`RefineFrame` coarsens the executed refinement's cell permutation to every
ancestor partition and retains inherited boundary values literally. Production
visits preserve the original colour-cell contents under the ancestor-boundary
invariant. `SpecColors` carries this through every unpruned child: all leaves
preserve ordered initial colour cells, the attaining form has the canonical
sorted colour sequence, and its native neighbour rows are normalized.
`IndexSet` interprets cached cell membership, and `TargetCounts` identifies the
native target counts with neighbour counts into those cells. `TargetInvariant`
proves invariance of scores, first-maximum selection and all target fields
under permutations within equitable cells. `ContextMap` and `TargetEquiv`
prove graph-renaming transport. `TargetTransport` gives the full fresh and
cached position, set and size laws, including different admissible scratch
contents and invalid-cache fallback; valid index witnesses are constructed.
`SortedKeys` proves uniqueness of the sorted count sequence and the literal
partition array determined by it. `CountClasses` identifies each fragment's
vertex multiset with the original cell filtered by its count. `CountInvariant`
and `CountTransport` prove that the executed count splitter preserves its
ordered partition and cell contents under within-cell permutations and vertex
renaming, with independently allocated scratch. `MinimaUnique` identifies the
two minimum keys and both cutoffs independently of input vertex order.
`CountUniform` proves the literal early return after hashing a uniform cell's
start. `CountExecution` derives the exact hash and queue trace from every
executed branch, including both distance modes, singleton fragments, strict
largest-fragment ties and final replacement. `CountCompare` and `CountControl`
prove literal hash, active-set and ordered-queue agreement from equal count
multisets. The combined transport law includes the exact cell count and only
requires hit agreement inside the divided cell; stale counts elsewhere are
unrestricted.
`IndexTransport` proves vertex-index transport, including singleton sentinels,
and agreement of valid endpoint caches at cell starts. `RowTransport` and
`TouchCompare` transport native neighbour-cell multisets and their sorted
first-touch lists. `MarkTransport` applies these to the executed singleton
marking loops: touched-cell arrays agree literally and vertex-mark predicates
commute with renaming, including different generations and retained marks.
The singleton compaction and reverse reinsertion loops have exact prefix,
retained-order, collected-hit, and index-write contracts. Their composition
preserves the cell's vertex multiset and separates the predicate classes.
`CompactClasses` identifies the restored fragments literally with the
retained source order and the reversed collected source order. Its transport
law gives equal cuts and hit counts and maps both fragment multisets.
`BinaryControl` proves the conditional fragment finalization, and
`BinaryStep` composes the executed compaction, reverse fill and finalization
into a complete singleton-cell observation contract: the hash, active set,
ordered queue, partition and counter are determined by the predicate-class
sizes. The same contract preserves the label window, gives literal fragment
formulas, retains unaffected scratch fields, and carries valid incoming
indices through the executed cache writes via `BinaryIndex`. `BinaryPass`
composes these cells while preserving valid indices and every pending cell.
`SingletonTrace` connects this trace to the actual native marking and
touched-cell loops, including the initial touched-count hash.
`SingletonEquiv` proves transport of the complete executed singleton pass:
ordered partition, hash, active set, ordered queue and exact cell count agree
literally, and output cell multisets commute with vertex renaming. Input
orders within cells, native row orders, valid caches and generations may differ.
`RowsTransport` and `ScanTransport` establish the same multiset and exact-count
transport for complete native nontrivial scans, including first-touch clearing.
`CountPass` and `NontrivialTrace` derive a trace of the executed touched-cell
loop from those counts, retaining every pending cell and its local hit bound.
`NontrivialEquiv` proves the full production nontrivial-pass transport law for
the ordered partition, cell multisets, hash, active set, ordered queue and
exact cell count. Scratch hits outside touched cells remain unrestricted.
`DistanceTransport` and `RefineDistance` transport the complete shallow branch,
including native BFS from the actual queued singleton. `RefineLoop` composes
the exact first-ten preference, swap/pop removal, hashes, splitter branches
and stopping guards. `RefineInitial` establishes the packed queue and rebuilt
indices. `refineWith_parts` identifies the proof blocks with production by
kernel definitional equality. `refineWith_equiv` proves end-to-end ordered-cell
and code equivariance, including final cleanup, under arbitrary bounded
scratch on either side. The partition, active set, ordered queue, count and
hash agree literally; labels transport as multisets within corresponding
cells. `refineWith_congr` proves literal label-array equality too for identical
inputs with arbitrary bounded scratch. `splitSingleton_lab`, `splitCounts_lab`
and `splitNontrivial_lab` cover both executed splitter branches. Exact count
scanning and three-way insertion feed `Sort.indirect_congr`, which follows
pivot sampling, partition swaps and the explicit stack without changing tie
order. Only keys in the current cell are constrained. `RefineCongr` and
`DistanceCongr` compose these through the main and distance loops; native BFS
starts at the same queued vertex. `RefineLiteral` includes initial index
rebuilding, empty-queue return and final cleanup. Incoming retained counts,
marks, generations and unused cache entries may differ.
The conditional cache finalization for one nontrivial cell is proved, including
both uniform-predicate cases. Native neighbour marking agrees with adjacency
and enumerates bounded nontrivial cells without duplicates. Sorting retains
first-touch coverage, and a cut preserves every disjoint cell. The complete
executed singleton pass preserves the label permutation, partition allocation,
and full cache validity through every touched cell and uniform-cell return.
Its counter increments match newly closed boundaries, and inherited closed
values are retained literally. It preserves exact agreement between the
active bitset and a duplicate-free queue of cell starts. Queue insertion,
replacement by the last entry followed by popping, and largest-fragment
replacement have exact membership proofs. The complete count splitter
preserves this queue contract through its initial fragments, bounded tail
scan, and largest-fragment replacement. The fragment activation proofs supply
the active-set invariant used in certificate preservation.

The complete refinement now preserves label permutations, every original
cell's vertex multiset, exact cell counting, and the active queue contract.
Its scratch cache is valid for the returned partition whenever indexed. The
proof follows index rebuilding, distance initialization, the first-ten queue
preference, removal by replacement and popping, and both main-loop splitter
paths. Native shortest paths supply all distance bounds; count bounds come
from the proved first-touch scans. Production visits preserve `NodeOk` and
return valid scratch; an exact incoming cell count remains exact. Distinct
active starts inject into partition cells at every valid node, so the
existing loop bound ends with an empty queue or a discrete partition. This
structural stopping theorem combines with `RefineCert` to establish equitability.

The full refinement function preserves partition allocation and every old
closed boundary: each write retains the old value or installs the current
level. This includes the distance pass, all three splitters, and the main
active-cell loop. The initial active-set cardinality is bounded by the
endpoint count for every endpoint list. The root therefore satisfies the
operational exhaustion theorem without an extra hypothesis. Stable sparse
colour buckets satisfy the shared partition-state contract, and every initial
colour cell is active.
The count splitter's counter increments equal its newly closed boundaries.
This follows the actual first cut and later fragment scan, using the local
hit bound and the second-minimum sentinel to rule out an empty second
fragment. Counts outside the affected cell remain unrestricted. The root's
passed cell count equals its boundary count. Both complete native passes
compose this exact counter relation and retain all inherited closed values.
The full refinement loop composes the same counter and boundary relation.
Count splitting also retains every old closed boundary value literally,
including inherited ancestor boundaries.
Shared recovery projections apply to arbitrary search storage. The actual
recovery operation gives the same ancestor partition before and after a
descendant count split. The sparse policy's child creation and recovery retain
scratch allocation and generation bounds while invalidating indices. Its full
target transition preserves scratch validity through guards, hints, borrowed
counts, and bookkeeping updates.
Persistent allocation and mark-generation bounds hold through the complete
singleton and nontrivial splitters, index rebuilding, distance initialization,
the full refinement loop, and the production visit. Advancing the generation
makes all old marks stale. Target selection preserves these bounds independently
of index correctness. Full refinement integrates the index and first-touch
count semantics; `Reach` supplies their entry invariants at each production call.

The executed breadth-first distances have attaining walks, minimality,
exact unreachable sentinels, and relabelling equivariance. Its queue is
unique and bounded, and both exhaustion and the full-queue early exit satisfy
the shortest-path contract.

## Proof dependencies and integration

1. **Refinement and caches — proved.** Use the established full-sort and shortest-path
   contracts, without adding sortedness or distance correctness as caller
   hypotheses. The executed refinement now preserves labels, cell multisets,
   partition boundaries, exact counts, queues and indices, and generation
   bounds. `Reach` carries ordered-colour contents, ancestor frames, exact
   counts, target membership and scratch contracts through every production
   call, including individualization and recovery.
   Ordered-cell, partition, active-set, queue, count and hash agreement under
   bounded scratch follows from full refinement transport. `refineWith_congr`
   adds literal label-array agreement for identical inputs, completing the
   fresh/cached refinement contract without constraining unobserved scratch.
   Full equitability is proved from the incoming certificate,
   with the root certificate derived from its actual initializer. `Reach`
   carries the individualization/equitable-child result through bookkeeping
   and backtracking between children.
   Full production code and ordered-cell equivariance is proved, allowing
   within-cell permutations and independent bounded scratch. Its proof composes
   singleton, nontrivial and distance passes through the literal main loop.
   Relabelling may change neighbour and tied-label order. Target equivariance
   and invariance within equitable cells are proved. `VisitKey` and `VisitTarget`
   apply these and the fresh/cached agreement to production calls, supplying
   the established cache, equitability and nontrivial-cell facts.
2. **Declarative canonicalization — proved.** The finite unpruned tree, sufficient-fuel
   stability, reachable attaining label and maximum are defined and proved.
   `SpecNode` derives all root, refinement and child invariants. `SpecTransport`
   transports every actual leaf and its full code chain under isomorphism and
   within-cell reordering. `canonSpecKey_map` proves maximum invariance;
   `specCanon_invariant` and `iso_iff_specCanon_eq` establish the
   canonical-form characterization, including order zero. Canonical colouring
   and neighbour normalization are proved. The production result equals
   this proved canonical form. Explicit conversions preserve verdicts, not
   necessarily canonical forms.
3. **Reachability and totality — proved.** Sparse instances of `Generic.Contract` and
   `Generic.SoundPolicy` establish partition frames and sufficient fuel.
   Generalized bookkeeping projections over `SearchState n κ` support these
   instances; the native cache and key proofs below supply the sparse invariants.
   `SearchBounds` instantiates the shared
   persistent-invariant contract and proves scratch allocation and generation
   bounds through all production nodes, sweeps, exits and final installation.
   `Reach` instantiates the sparse partition contract: executed visits,
   targets, all bookkeeping, individualization and recovery preserve node
   validity, equitable parents, ordered-colour contents and reference-label
   frame effects. Root premises are derived from stable colour buckets.
   `Reference` instantiates preservation of the saved first leaf, codes and
   target array through off-path nodes and later siblings. `FirstFields`
   proves actual code/target writes, unchanged ancestor slots, allocation
   sizes and retention of the terminal sentinel. `Depth` bounds every
   emitted code below that sentinel and prevents comparisons from advancing
   below the saved first leaf. `ReferenceResult` derives these facts and
   validity of the saved first label at the initialized root. `ClassifyStore`
   proves native incumbent-prefix preservation and the exact candidate prefix
   for every better verdict. `StoreSearch` carries the installed row cache
   through the actual mutual recursion; `FirstStore` seeds it from the first
   leaf and retained blank allocation. `StoreResult` proves unconditional
   root and final-installation validity, with every returned working row
   representing the public label's relabelling. Semantic code and descent
   histories are established by the following invariants. `WorkSize` proves exact permutation
   workspace allocation through every actual node, sweep and root. `Scatter`
   identifies its entries with the forward map between parsed labels.
   `FirstHistory` constructs a selected native descent with its actual code
   sequence and literal terminal label/partition from `Generic.FirstPath`.
   `FirstRef` proves that all saved code and target slots, the first label
   and terminal sentinel describe that same descent after later siblings.
   `RootHistory` derives this reference from initialization, preserving it
   through final row installation. `CodeBounds` bounds every code in that
   actual descent, and `CodeFields` preserves its preallocated canonical
   code array. `FirstCodes` derives initialization of both code machines at
   the actual first leaf. `CodeRead` identifies stable native incumbent
   storage with its semantic sparse key. `Comparison` includes parsed saved
   labels and the first key's lower bound, deriving the initial state and
   preserving it through native visits, comparisons, targets and children.
   `ComparisonOps` proves preparation and ancestor recovery, including a
   negative row verdict after tied codes. `CodeOrder` connects the shared code
   machine to native sparse key order, including sentinel precedence and
   frozen comparisons. `Canonical` proves that the executed canonical verdict
   chooses the exact incumbent/candidate maximum and returns settled codes;
   its complete-classifier lemma consumes a first-reference bound.
   `PathFrame` and `Positions` prove ordered ancestor-cell preservation and
   literal retention of every individualized vertex through native descents.
   `Guided` proves equality of depth and complete code sequences for selected
   and guided descents with corresponding terminal labels, allowing independent
   caches and within-cell order. `GuidedLeaf` derives the ancestor stabilizer
   from those literal labels and identifies the first sentinel and graph under
   a native automorphism. `GuidedPerm` and `RouteAt` extend and recover these
   histories through actual child visits and returned partition frames.
   `RouteKey` derives the complete first-reference key and exact leaf maximum
   from these histories and the established admission soundness.
   `RouteAlignment`, `RouteTarget` and `RouteHistory` preserve the general
   history through preparation, child entry and full-call recovery;
   `FirstRoute` derives it from the actual first child. `LeafCodes` proves
   settled comparisons and incumbent growth at every terminal classification.
   `CodeState` and `CodePrepare` supply the prepared histories, recorded targets
   and nonempty target when a positive comparison requires a child.
   `CodeSweep` and `CodeNode` prove recoverable comparisons and monotone native
   incumbents through the executed mutual recursion. `FirstCompare` carries
   the initialized first-leaf comparison through all ancestor sibling sweeps;
   `CodeResult` derives settled comparisons and a readable incumbent from
   actual root initialization and preserves them through final row installation.
   `CanonFrame`, `CanonNode`, `CanonSweep` and `CanonCalls` prove canonical
   reference provenance through complete native calls. `CanonSource` shows
   that a child retains its incoming reference or installs one through its
   literal chosen vertex; a reference pointing above the child is unchanged.
   `CanonGuide` retains the reference's covered-child witness through sibling
   permutations and actual child recovery, using local child coverage as the
   induction premise. `CanonScatter` identifies the canonical classifier's
   literal forward scatter. `ReturnOrigin` proves that every short return
   retains its emitting leaf's last pair, canonical ancestor and trace entry,
   or the implicit pair and cheap-boundary limit, through intervening calls.
   `ExitBound` derives the exact receiving level from the native ancestor and
   cheap bounds. `Capacity` proves preservation of the pinned pair capacity.
   `CanonPair` establishes the canonical scatter's parent-cell stabilizer;
   `ShortPair` proves actual receiver pair validity for explicit and implicit
   emissions, deriving later-sibling child validity from native invariants.
   `SubtreeKey` aggregates the existing unpruned leaves, with sufficient fuel
   proving attainment. `SubtreeMap`, `VertexKey` and `VertexFrame` transport
   those maxima under native isomorphisms, checked cell stabilizers and parent
   recovery. `FilterCover` and `FilterPrune` prove ranked coverage preservation
   by both actual filters, including carriers removed by earlier filters.
   `CoverFrame` transports coverage and reference keys together through sibling
   reordering. `CanonCover` proves that an actual received canonical scatter
   covers the whole current child through the already covered reference child.
   `PrefixKey` preserves native comparisons and maxima under ancestor codes.
   `SubtreeSplit` decomposes the unpruned maximum into complete children and
   proves attainment by one child. `VisitKey` and `VisitTarget` connect fresh
   specification visits to actual cached visits, including codes, counts,
   partitions, parent frames and all target fields. `VisitSplit` proves the
   discrete node's exact key and characterizes internal-node bounds using the
   actual cached target's child maxima. `VisitCover` closes node coverage from
   exhausted ranked child coverage, including the ancestor prefix.
   `CodeBound` proves that an actual negative code comparison after preparation
   covers the whole node and every continuation. `Maximum` supplies native
   incumbent upper bounds and exit-coverage composition; `LeafBound` derives
   upper bounds and candidate coverage from the actual classifier and exit.
   `MaxFrame` and `MaxCell` retain valid frozen native entries, sufficient
   depth-derived fuel and the original vertex-indexed child keys through
   sibling reordering. `MaxEmit` proves whole-node upper bounds and coverage
   for the actual discrete classifier exits and nondiscrete code rejection.
   `CodeScope` associates recorded ancestor codes with their valid frozen
   entries, preserves this association on descent and truncation, and derives
   coverage witnesses from native negative comparisons. `MaxReject` proves
   the complete return contract for code-supported nondiscrete rejection,
   including nonlocal returns; it retains the actual alternative of a cheap
   boundary return. `CursorCover` connects received child results and orbit
   skips to the executable cursor. `FrozenPrune`, `ResumeCover` and
   `ReceiveCover` compose actual short and long filtering with recovery and
   the next off-path sibling call, using the child's maximum result as the
   recursive hypothesis. `SmallKey` identifies all complete native child
   keys under the cheap shape. `MaxTarget` identifies full node coverage with
   its original cached target; a passing native cheap guard makes any actual
   individualized child attain the whole node key, including after parent
   reordering. `MaxParent` retains each suspended native entry and its
   literal chosen child; under the cheap shape their full keys coincide
   unless an earlier negative comparison already covers the parent.
   `MaxScope` initializes the ancestor chain at the root, extends it on
   individualization and preserves it under incumbent growth and the native
   cheap-boundary counter alternative. `MaxCheap` propagates coverage across
   that chain and proves the full return contract for actual discrete
   emissions to their cheap boundary and every nondiscrete rejection,
   given the ancestor invariant. `MaxChoice` derives the stronger target
   alternative from native preparation: the unhinted target or a negative
   prefix covering every continuation, including hinted children.
   `MaxPrepare` establishes suspended-parent validity on both preparation
   paths. `MaxDescent` establishes the actual child scopes and retains
   ancestors through complete off-path calls. `MaxRecover` and `MaxResume`
   derive the next surviving vertex's comparison, history, target, shape
   and ancestor invariants from the actual child call and recovery.
   `MaxUpperSweep` and `MaxUpperNode` close the complete off-path node/sibling
   upper-bound induction, including both filters, orbit skips, hinted
   targets and nonlocal returns. Their hypotheses are native entry and
   ancestor invariants; no subcall maximum theorem remains assumed.
   `MaxFirstLeaf` derives the first leaf's code machine from actual
   stored-prefix writes and allocation, identifies its installed native
   key with the full frozen node key and proves the complete maximum
   contract for the executed first discrete call. `MaxFirstEntry` derives
   native first-entry storage, histories and inherited shape from the root
   initializer and preserves them through actual first children.
   `MaxFirstCodes` derives the complete first-leaf comparison from literal
   stored-prefix and suffix writes at arbitrary entry depth, and recovers
   the caller's exact code prefix after the full call. `MaxFirstResume`
   derives the next sibling's comparison, history, target, shape and
   ancestor facts from the actual first-child return without assuming a
   maximum result. `MaxFirstSweep` and `MaxFirstUpper` close the complete
   first-path upper-bound induction, including every later sibling.
   `MaxUpperResult` identifies the depth-derived root bound with the
   declarative maximum by sufficient-fuel stability. `runState_upper`
   and `run_upper` prove that every installed production key is at most
   `canonSpecKey`, with no search-correctness premise. The order-zero
   state has no installed code chain; final native row-cache updates
   retain the key bound.
   `MaxScatter` identifies the actual chosen child's full key and
   transports coverage from a reference child by a native automorphism.
   `MaxAncestor` derives the ancestor child frames from the existing
   parent chain. `MaxRetain` proves literal preservation of closed
   boundaries through actual preparation, individualization and later
   entries. `MaxEmitter` derives the emitter's cell containment and
   selected vertex position from these facts, and constructs the
   nonlocal witness from covered-reference scatter data. `MaxGuides`
   records covered children at suspension and associates earlier reference
   counters with their literal saved labels. It initializes at the root
   and extends through actual individualization. `MaxGuideReturn`
   preserves these associations through complete off-path calls, terminal
   dispatch and both actual child return/recovery paths. `MaxAutoFirst`
   proves the full maximum return contract for first-reference automorphism
   leaves, including cheap admission and nonlocal returns, from the
   covered-reference invariant and positive strict ancestor counter.
   `MaxAutoCanon` proves the corresponding contract for canonical admission
   returning to its canonical ancestor, with either short flag. Both rules
   derive the native scatter and emitter geometry. `MaxGuideFrame` transfers
   reference coverage to recovered label order. `MaxGuideBack` and
   `MaxGuideFirst` establish both guides for the next sibling from the
   completed child's coverage; native provenance and `FirstFrame` supply
   label containment and the exact selected position. `AncestorOrder` and
   `MaxControl` preserve ancestor order, establish positive receiving counters
   and set both ancestors exactly to the parent after its first child.
   Actual preparation retains references and initializes the new sweep's
   vacuous guides under strict ancestor bounds. `MaxRank` derives coverage
   of smaller target vertices from ranked frozen-cell coverage, including
   filtered vertices and hinted targets. Its actual trace-word argument
   covers a selected child with a smaller orbit pointer. `Coset` proves
   off-path index preservation; `MaxCosetState` associates that index with
   the suspended first ancestor through preparation, selection and both
   return paths. `MaxCoset` proves the full canonical-admission maximum
   rule, including the earlier first-ancestor coset return, from the local
   reference, rank, index, counter and trace invariants. `MaxTrace` derives
   stabilization for all suspended first ancestors from the actual first
   leaf and preserves it through preparation, child calls and recovery.
   `SelectedCell` identifies all fields of the enabled native cached target
   with its complete cell window, including hinted selections. `MaxLoop`
   freezes that actual selection and identifies its literal child entries;
   `LoopCover` derives suspended ranks, frozen canonical guides and parent
   coverage from its child coverage. `MaxContext` assembles these facts with
   code histories, pruning-pair validity and counters at child entry.
   `MaxStart` establishes the complete off-path sweep context at native
   preparation; `MaxNext` restores it after actual child recovery for every
   filtered subset with proved coverage. `MaxSweep.lower_sweep` proves the
   entire later-sibling coverage induction, including orbit skips, both
   filters and nonlocal returns. `MaxTerminal` supplies all terminal cases,
   including discrete rejection and better-leaf cheap returns.
   `MaxNode.node_max` proves the complete off-path node maximum contract by
   induction on the actual recursion bound, using the established upper
   bound and these coverage results. `MaxFirstContext` initializes the full
   first-descent context and preserves it at each literal first cursor.
   `MaxFirstPairs` restores the parent's pruning workspace; `MaxFirstNext`
   restores the full sibling context from the completed child's coverage.
   `MaxFirstFilter` justifies its actual short filter from emitted pairs.
   `MaxFirstLower` proves coverage through the entire first sweep, and
   `MaxFirstNode` closes the first-descent maximum induction.
   `MaxResult.runState_max` and `run_max` identify the nonempty production
   key with `canonSpecKey`, using the actual initialized context and the
   existing no-exhaustion theorem. No subtree-result assumption remains.
   `AncestorStab` transports stabilization between suspended ancestor frames
   and derives it from actual reference scatters. `OrbitCover` composes the
   literal trace word behind a skipped pointer and proves ranked coverage for
   that skip, conditional on trace stabilization of the frozen partition.
   An empty individualized path discharges this condition from native
   automorphism soundness. `TraceFrame` records frozen reference containment
   and trace stabilization. `TraceFrameLeaf` proves it for actual reference
   scatters and classifier exits; `TraceFrameOps`, `TraceFrameNode`,
   `TraceFrameSweep` and `TraceFrameCalls` preserve it through the complete
   native mutual recursion, including truncated calls and nonlocal returns.
   `TraceFrameSeed` and `FirstTraceFrame` initialize it at the actual first
   leaf and retain it throughout the first descent's returned computation.
   `TraceOrbit.firstChild_stabilizes` specializes this to each prepared parent
   partition, and `TraceFrame.skip_cover` discharges the orbit guard's
   stabilization premise. The assembled later-sibling coverage invariant
   uses this result, and `MaxFirstNext` initializes it at the actual first
   child's return as part of the completed first-descent induction.
   `ReadyPerm` preserves a frozen
   equitable node and its refinement certificate under within-cell label
   reordering. `DescentAt` ties its current witness to the production arrays
   and count, extends it through actual cached child visits, and restores it
   from the established native frame effect on recovery. `Alignment` retains
   that descent while first-code agreement is live, including recovery after
   arbitrary off-path child calls. `AlignedTarget` identifies the actual cached
   target with its stored slot. `Controls` proves that descendant calls retain
   the frozen ancestor and cannot enable its failed cheap guard. `CheapHistory`
   combines these into preparation, child and return transitions and proves
   both first-admission guard arms sound from the retained history, independently
   of incumbent comparison. `FirstCheap` establishes inherited guard shapes
   from initialization and preserves them through first children. `FirstReturn`
   derives the recovered history and saved target from the actual first-child
   call. `Trace` proves native automorphism verdicts and literal trace appends;
   `Saved` preserves installed reference and workspace validity through full
   off-path calls and derives it from the first descent. `TraceState` combines
   those facts with histories through preparation, admission, child entry and
   recovery. `TraceSweep`, `TraceNode` and `FirstTrace` close the mutual
   recursion and first-path induction. `TraceResult.generator_iso` proves
   unconditionally that every emitted array has the graph's order and is the
   exact forward map of a coloured automorphism, including order zero.
   `Orbits` proves preservation of the trace-relative pointer relation through
   every actual policy operation. `runColored_orbits` and `orbit_word` derive
   descending, in-range final pointers connected by words in the emitted
   trace; `orbit_iso` realizes each pointer by a native coloured automorphism.
   These are soundness results; exact orbits still require completeness.
   `FixedState`, `FixedNode`, `FixedSweep` and `Fixed` prove preservation of
   fixed singleton cells and exact restoration of every node and sweep
   call's incoming fixed-point bitset, including truncation and nonlocal
   returns. `runColored_fixed` derives the empty final fixed set from
   initialization. `Stabilize` transports cell stabilizers through actual
   cached refinement. `PathState` initializes the root path invariant and
   proves its local transitions and recovery after complete native child calls.
   `CheapBoundary` establishes implicit pairs at actual equitable states and
   preserves frozen pairs through refinement, child calls and recovery;
   `FirstBoundary` covers the complete first-path search. `Pairs` validates
   explicit and implicit admissions, including bounded workspace replacement.
   `PairsState`, `PairsSweep`, `PairsNode` and `FirstPairs` close the actual
   mutual recursion. `PairsResult.runColored_pairs` proves unconditional
   validity of every retained root-colour pruning pair, including order zero.
   `Prune` transports this workspace along the current path and gives checked
   carriers for native long-filter removals and representatives of whole cells.
   The complete maximum-preservation induction uses these pruning facts.
   The emitted trace's full generation theorem is proved below.
   Canonical-reference provenance and both code comparison machines are
   established through arbitrary nonlocal returns. The complete coverage
   induction integrates the reference guide, orbit skips, ancestor domination
   and nonlocal coverage witnesses. Native
   negative-code domination and complete local leaf bounds are established. Receiver pair
   validity and local short/long filter coverage are established independently.
   Parent recovery is proved. `Fuel` proves that the existing node and cursor
   bounds suffice, with unconditional `runState_noFuel` including order zero.
   `FirstPath` constructs the actual first descent from identity orbits and
   nonempty native targets. `FirstResult` proves that it installs a full,
   colour-respecting canonical label retained through all remaining siblings
   and nonlocal returns. `Result` proves unconditional `searchResult?_isSome`,
   including order zero, independently of certificate replay.
4. **Production maximum and public API — proved.** The complete native
   induction carries incumbent code histories and ancestor frames through
   nonlocal returns and justifies every classification, orbit filter,
   short/long prune, cheap-automorphism shortcut and dominated target hint.
   It uses sound generators and stabilizer membership without assuming
   generation completeness. `runState_max` and `run_max` identify the actual
   nonempty final key with the unpruned maximum. Native `canonicalize`, `canon`, `label`, `findIso` and
   `isIso` are exposed in `Sparse.Ops`; result extraction uses unconditional
   parser success. Relabelling, colour ordering, transporter soundness and
   exact diagnostic agreement are proved. `Sparse.Canonical` proves
   `canon_eq_specCanon`, canonical invariance and idempotence, the canonical
   isomorphism biconditional, transporter completeness and both decision
   directions, including order zero. `Sparse.UncoloredOps` provides total
   bare sparse `canonicalize`, `canon`, `label`, `findIso` and `isIso`, using
   one colour for nonempty graphs and zero colours for the empty graph.
   Native result agreement, relabelling, canonical invariance and equivalence,
   transporter soundness and completeness, and both decision directions are proved.
5. **Automorphisms — proved.** The full emitted trace is proved to generate all
   colour-preserving automorphisms using first-path stabilizers and reference
   child coverage. It is distinct from the bounded 500-pair pruning workspace.
   `CanonAutom` proves native canonical-tie graph equality and identifies the
   emitted permutation. `LeafAutom` proves coloured automorphism soundness
   for canonical ties and explicitly scanned first-reference admissions,
   using the established label, colour and row-cache invariants. The cheap
   first-reference branch uses ancestor histories derived through the
   production trace recursion.
   `SmallCell` and `SmallStep` connect the native equitable partition to
   cell-stabilizer transitivity and preserve both cheap-guard shapes through
   actual individualization and refinement. `Path` records literal cached
   child calls, and `PathTransport` matches whole descents under isomorphism.
   `CheapLeaves` proves equality of normalized graphs at discrete
   leaves below a cheap-shaped node with the same target positions, including
   independent bounded scratch. `CheapPrefix` proves that a discrete descent
   following a target prefix reaches the same depth and graph. `ReferenceLeaf`
   connects this fact to the stored reference and exact emitted scatter.
   `FollowsPerm` retains current histories through within-cell reordering and
   literal cached child calls. `CheapAdmission` proves coloured automorphism
   soundness from these histories. `ReadyTarget` proves target agreement for
   equivalent native equitable nodes. `CodeTransport` transports selected
   descents with their complete code sequences. `CheapTarget` and
   `ReferenceTarget` prove that an open branch following saved targets chooses
   the next stored target, including after sibling reordering. `TargetHint`
   identifies the actual cached hint's complete target fields with unhinted
   selection under these history premises. The executed-search trace induction
   derives frozen ancestors, current histories and matching targets at every
   cheap admission, and proves soundness of every emitted generator.
   `GenerationFrame` proves that true point stabilizers preserve native
   target cells and are trivial at actual first discrete visits.
   `TraceContains` proves retention of every emitted array through both kinds
   of complete calls. `GenerationTrace` decodes the full trace as forward
   permutations, proves native automorphism soundness and realization of
   every emitted array, and constructs generated orbit-pointer carriers
   fixing the active base. `FirstBounds` proves the
   native first-code and all-same lower bounds. `EarlyReturn` identifies
   the actual emitting leaf of an unconsumed return and bounds that return
   using both ancestor counters and pruning boundaries. `FirstSweep` proves
   exact all-same preservation through later siblings and first-child cleanup.
   `CodePrefix` identifies the exact saved code along a cheap-shaped descent
   following stored targets. `ReferenceEmit` proves that matching native
   leaf graphs force the executed first-reference admission and supply its
   literal emitted label carrier. `ReferenceCode` connects recovered parents
   to the actual cached child code; `ReferenceStep` and `ReferenceDescent`
   prove the complete cheap-reference descent and its emitted carrier by
   induction on the executed recursion. `FirstTail` proves that every later
   first-path child returns to its receiver and the whole sibling sweep
   finishes, including both native filters and orbit skips. `FirstComplete`
   proves normal return of every actual first-path call, deriving the guiding
   child's return inductively. `ReferenceReturn` extracts checked label
   carriers or orbit-pointer evidence from actual returns. `ReferenceSweep`
   proves that a canonical carrier comes from an earlier cursor, and
   `GeneratedReceipt` advances generated orbit coverage from this evidence.
   `FirstSuffix` identifies the literal continuation after the guiding child.
   `FirstCount` follows that continuation and every actual counter update:
   increments count distinct original target vertices with checked
   cell-stabilizing carriers to the guide. Reaching the original target size
   supplies such a carrier for every original vertex. `FirstDrop` identifies
   the exact guard lowering the all-same boundary. `LeafPath` and `Uniform`
   describe the complete keys and targets of literal cached descents and
   prove their isomorphism transport. `FirstUniform` derives uniformity at
   the actual returned all-same boundary from the counted carriers.
   `RefPath` preserves the boundary's uniformity under checked cell
   stabilizers. `Matching` connects the literal stored codes, targets and
   parsed first label to a selected occurrence, and `FirstWitness` constructs
   that richer reference from every complete actual first call. Every valid
   refined state has a selected discrete descendant. `MatchingTarget` and
   `UniformStep` retain matching through the actual cached minimum child;
   `UniformReturn` follows those child calls to an actual emitted checked
   carrier and return to the first-reference ancestor. Checked cell
   stabilizers transport the richer reference in both directions;
   `ReferenceOrbit` supplies it in every true path-stabilizer orbit image
   without assuming completeness of the emitted group.
   `ChildPath` transports frozen reference occurrences to the exact cached
   children entered after sibling reordering. `PathCover` specializes the
   ranked absence ledger to those native occurrences. `ReferenceVisit`
   consumes canonical returns through their earlier source, while
   `ReferenceFilter` derives both filters' witnesses from the actual child
   workspace. `ReferenceResume` reconstructs the full next-sibling context
   after the literal filters and recovery. `ReferenceLoop` proves the
   complete off-path sweep induction, with reference completion of actual
   smaller child calls as its recursive premise. `SmallUniform` proves full
   key and target uniformity below every cheap-shaped native node using
   true cell-stabilizer transitivity and independent bounded scratch.
   `ReferenceComplete` discharges the smaller-child premise by induction on
   the actual node calls, including reference completion above the uniform
   boundary. `GeneratedVisit` advances generated orbit coverage from each
   actual child return; `GeneratedTail` proves the complete suffix, including
   orbit skips. `GeneratedHead` constructs its reference and base premises
   from the actual guiding child. `GeneratedComplete` proves the full
   first-path stabilizer induction. `GeneratedRoot.runColored_generates` and
   `generated_iff` identify the subgroup generated by the actual output with
   all native colour-preserving automorphisms, including at order zero.
   `OrbitReplay` identifies the actual pointers and count with the literal
   sequence of emitted joins. `OrbitExact` proves exact least representatives,
   the full automorphism-orbit biconditional and the actual root count.
   Coloured and bare sparse `autos` expose the existing `AutResult` shape;
   the coloured `Aut` projections retain the same single traversal and have
   generation and orbit correctness theorems. `OrbitClosure` proves closure
   of every intermediate native orbit array under its current emitted trace.
   `OrbitMark` identifies the actual counter test with true stabilizer-orbit
   membership after each cursor advance. `StabilizerTail` proves exact
   counting through visited children and orbit skips; `StabilizerHead`
   derives the first-child premises and identifies each complete first-path
   index with its stabilizer orbit size. `OrderOps` proves that off-path
   nodes and later siblings preserve the actual order accumulator.
   `OrderStep` identifies its exact first-child multiplication and terminal
   value. The Mathlib `Sparse.Order` induction proves that the existing
   product accumulator computes the full group order, including order zero.
6. **Certificates — integration remains.** Distinct sparse `CertNode`,
   `checkNode` and `checkKey` entrypoints recompute refinement, targets and leaf
   comparisons. `checkNode_valid` proves domination of every actual leaf and
   exact attainment; `checkKey_sound` identifies the declarative maximum.
   `produceNode_replays` and `produceRoot_replays` prove unlimited expansion
   completeness. `produceCand_eq` connects the producer to the actual production
   maximum and literal label from one optimized search; `certifyKey?_eq` proves
   unconditional success of production followed by checking. Differing accepted
   keys prove non-isomorphism. `Literal.checkKey_eq` identifies kernel replay
   with that checker, including every sparse splitter, distance branch, sort,
   target, parser and relabelling operation. The first imported-module tests
   accept the recorded order-12 random keys and their negative pair and reject
   malformed records. `checkCanon_sound` proves that accepted result packages
   return the canonical form and a label relabelling the input to it;
   `certifyCanon?_eq` proves unconditional success and exact agreement with the
   direct result, including the production label. `Replay.checkAutom_sound`
   verifies sparse graph automorphisms and transport of complete ordered child
   partitions. `Replay.scan_valid` proves that only earlier checked sibling flags
   can be reused. `Compact.checkNode_valid` and `checkKey_sound` prove full
   domination and attainment with these references. `Compact.produceNode_replays`
   and `produceRoot_replays` prove unlimited compact production complete, including
   full expansion when no checked witness is available. `Compact.produceCand`
   reuses the same optimized search's key, label and generator trace;
   `Compact.certifyCanon?_eq` proves exact direct-result agreement.
   `Literal.Compact` proves equality of compact key/result replay with the native
   checkers. Kernel tests accept a compact endpoint-swap certificate and reject
   forward/self references, invalid permutations, non-automorphisms and incorrect
   child-partition transport. `CertNode.stats` counts actual records, automorphism
   records and permutation payload entries. `Compact.checkRecords?` enforces the
   record limit before replay, with exact unlimited-verdict agreement and kernel
   exhaustion/rejection tests. `Quota.collect` and `Quota.emit` thread the record
   quota through actual sibling production. `Compact.produceNode?_budget` counts
   exactly its emitted tree; `produceNode?_eq` and `produceRoot?_eq` prove exact
   agreement with unlimited compact production on success. `candidate?` retains
   a supplied native run's label and enforces the record cap without repeating
   the search. `produceNode?_complete` and `produceRoot?_complete` prove that the
   exact unlimited tree size suffices. `produceRoot?_none` characterizes exhaustion
   precisely, and `candidate?_complete` gives the full unlimited key, label and
   tree from the optimized native search whenever the record quota covers it.
   The CFI kernel campaign passes four fresh builds, with replay time, peak
   memory and adjacent import baselines retained in
   `reports/bench-results/hexgraphiso-sparse-replay-unlimited.jsonl`.
   Search and record-limit exhaustion remain inconclusive.
7. **Tactics and Mathlib.** `Sparse.TacticSupport` evaluates native inputs,
   proposes transporters with the optimized searches, reifies sparse literals,
   and emits kernel-checked transporter and compact-certificate proofs.
   `Sparse.Tactic` registers coloured and bare sparse goals with the existing
   `graph_iso` extension mechanism. `SparseTacticTests` exercises public dispatch
   across an import boundary on the
   empty graph, the recorded order-12 positive/negative pairs and the ordered
   Petersen order-10 positive/negative pairs. Both proof routes use the original
   literal checkers without operation counters or estimated replay limits.
   Bare tests include the empty graph and a singleton, and the random pair
   tests preserve goals after search-node and certificate-record exhaustion.
   Open inputs are rejected with an explicit diagnostic.
   `Limited.node_budget` conserves the
   quota through the whole shared recursion; `node_exhausted` freezes exhausted
   state, and `node_nodes` bounds the actual native counter on all returns.
   `runPair?_nodes` proves the two native searches fit one combined quota.
   The backend uses this paired search for both proof routes and bounded compact
   production for negatives. `SparseLimitTests` covers zero, insufficient, exact
   and surplus quotas, including exhaustion between the two searches; successful
   outputs match canonical rows, labels, codes, generators, group data and all
   seven diagnostics. `LimitAgreement.node_eq` and `sweep_eq` prove exact
   native projection through the whole executed recursion, including backward
   preservation of the non-exhausted condition. `runColored?_eq` and
   `runPair?_eq` identify complete successful states with the direct runs,
   without validity assumptions on intermediate raw states. Bounded candidates
   consequently retain the unlimited producer's exact key, label and tree;
   `candidate?_replays` proves their acceptance. Public sparse positives check
   explicit transporters; negatives replay canonical certificates.
   `HexGraphIsoMathlib.SparseTacticTests` checks imported kernel replay through
   the explicit Mathlib sparse encoding: ordered-colour positive/negative pairs,
   the empty graph and a nonidentity finite enumeration. The encoding uses
   Hex's kernel-transparent vector constructor for both rows and colours.
   The encoding bridge
   proves full decoded automorphism generation, equivalence of the full groups,
   exact native orbit representatives, and cardinality of the orbit quotient.
   `Sparse.Aut.order_card` identifies the executed index product with the
   full native group cardinality; `Mathlib.Sparse.autOrder_card` transfers
   that result to the full decoded automorphism group under any enumeration.
   Keep direct `SimpleGraph` goals on their existing encoding.
   `HexGraphIsoMathlib.Sparse.Canonical` already proves enumeration-independent
   production canonical equivalence, complete sparse decision correspondence,
   and decoding of the actual returned transporter.

Complete each dependency before relying on its conclusion. The direct public
canonicalization theorem is independent of certificate replay. Canonical-form
invariance is not an assertion that canonical labels are equivariant in graphs
with automorphisms.

## Documentation and integration

Update the computational and Mathlib SPECs with each delivered contract,
clearly distinguishing established guarantees from outstanding obligations.
Include precise hypotheses, public theorem surfaces, logical-limit behaviour,
and the single-traversal automorphism result. Extend existing public imports,
conformance targets, benchmarks, and CI jobs. Preserve the existing library
pair and managed-directory release structure.

## Acceptance

Use the normal build and runner defaults, without imposed memory or worker
limits. Record peak memory usage with measurement context and terminate the
entire owned process group on timeout. A failed or timed-out proof is unsolved,
not evidence of non-isomorphism. Retain completed samples when any later
process fails. Use a temporary `GIT_INDEX_FILE` when a freshness script stages
sources, to preserve existing staging.

Build each proof increment using `lake build` and resolve diagnostics before
continuing. At integrated milestones run the complete sparse campaign via
`scripts/oracle/graphiso_sparse_check.py --trace-corpus`, fresh sparse fixtures,
and dense regressions. Compare canonical adjacency, colours, labels, all seven
statistics, generator emissions, exact orbits, and integer group order.

Cover empty/discrete and disconnected graphs, repeated keys and sort cutoffs,
distance refinement, queue priority, cache reuse/recovery, target depth,
workspace saturation, and packed-set boundaries. Reject malformed certificate
records, labels, codes, witnesses, and sibling references. Every logical limit
has an exhaustion test; failure must not prove non-isomorphism. Require
imported-module kernel replay for the random order-12 positive/negative pairs,
ordered-colour order-10 pairs, and the scheduled negative CFI case under
separately recorded larger limits.

Run trust, dependency, full-build, public import, published-library, and
Mathlib-free benchmark checks. No unfinished proofs, added axioms, or
`native_decide` remain in the correctness path. Full SPEC parity and the
unconditional theorem surface are release-readiness requirements.

Preserve historical performance data and six-way figures. Relevant source
fingerprints follow the existing freshness rules, including proof-only edits;
there is no free-form exemption. Executable changes require adjacent alternating
AB/BA measurements and refreshed affected figures. Retain every completed
sample and the current normalization rule without a minimum-order cutoff.
Measure new automorphism and certificate paths separately. The source reports
for existing performance choices are [the first optimization report](graphiso-sparse-performance.md),
[the further optimization report](graphiso-sparse-performance-2.md), and
[the cutoff comparison](graphiso-sparse-cutover.md).
