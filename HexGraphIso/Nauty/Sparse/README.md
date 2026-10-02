# Sparse nauty

This directory implements the sparse dispatch of nauty 2.9.3. The supported
inputs, pinned C configuration, exact ordering requirements, and public
correctness theorems are specified in
[the sparse SPEC](../../SPEC/hex-graph-iso.md#sparse-graphs-and-sparse-nauty).
The user-facing operations live in [`HexGraphIso/Sparse`](../../Sparse),
with [`HexGraphIso/Sparse.lean`](../../Sparse.lean) as their umbrella import.

## Executable code

| Module | Responsibility |
| --- | --- |
| [Graph](Graph.lean) | Native sparse adjacency, canonical rows, automorphism checks, canonical comparison and update, and distance BFS |
| [Sort](Sort.lean) | nauty's indirect sort, including its ordering of equal keys |
| [Cells](Cells.lean) | Numeric sorting of touched cell starts |
| [Refine/State](Refine/State.lean) | Reusable scratch arrays, refinement state, and cell indices |
| [Refine/Counts](Refine/Counts.lean) | Count and distance splitting |
| [Refine](Refine.lean) | Singleton splitting, neighbour counting, distance shortcut, and the active-cell loop |
| [Target](Target.lean) | Sparse target-cell selection and its cached variant |
| [Search](Search.lean) | Sparse operations supplied to the shared nauty traversal |

A position indexes `lab`; neighbour numbers and the entries of `lab` are
vertices. `cellstart` is indexed by vertex and contains its cell's first
label position, or the sentinel `n` for a singleton. `cellend` is indexed by
cell start and contains an inclusive final label position. Other endpoint
entries may be stale. Most splitter loops use the exclusive bound
`last = cellend[first] + 1`.

`active` records membership while `queue` records processing order. Both
matter: selecting a splitter, adding fragments, and replacing the largest
fragment must follow the C order. Likewise, `longcode` records the exact
sequence of refinement hash updates; the count and distance branches have
different updates.

## Count splitting

[`splitCounts`](Refine/Counts.lean) composes three inline operations:

1. `CountSort.firstRun` finds the end of the initial equal-count run. A
   uniform cell returns after hashing its first position.
2. `CountSort.minima` performs nauty's three-way insertion. The first two
   fragments contain the two smallest counts; their boundaries are `v2`
   and `v3`. The remaining labels have larger counts.
3. `CountSort.finish` installs fragment boundaries and vertex indices,
   sorts the larger-count tail, and scans its runs. It maintains the ordered
   active queue and the prescribed largest-fragment replacement.

These are the executed loops as well as the definitions used by the proofs.
[`CountParts`](CountParts.lean) gives their composition by definitional
equality. [`Refine/Minima`](Refine/Minima.lean) proves the scan and insertion
properties; [`Refine/CountSpec`](Refine/CountSpec.lean) adds count bounds and
permutation preservation. Its `splitCounts_induct` lets callers prove a
uniform return and an installation step without repeating the insertion
loop invariant.

The installation contracts separate the properties needed downstream:
[`CountSize`](CountSize.lean) counts new boundaries,
[`CountPattern`](CountPattern.lean) identifies exactly the unequal-count
boundaries, [`CountActive`](CountActive.lean) and
[`CountQueue`](CountQueue.lean) describe activation,
[`CountIndex`](CountIndex.lean) establishes the resulting cell cache, and
[`CountExecution`](CountExecution.lean) records the literal hash and queue
trace. The `Minima`, `Index`, and `CountTrace` modules supply the corresponding
local invariants and transition lemmas.

## Ownership and validation

Array ownership is part of the implementation. When a loop takes an array
out of a state record for mutation, the old field is cleared before the
first write. Keeping that alias alive can force a copy. Inline helper
boundaries must preserve this ownership behavior.

The initial scan and insertion use `macro_inline` so that the compiler
expands them before introducing intermediate loop states. The installer
uses ordinary inlining. `RefineSt.hash` is also inlined to avoid a
record-level function call at each hash update. The proofs use the same
definitions regardless of these compilation annotations.

The mathematical proofs and exact C differential checks serve different
purposes. The proofs establish the public isomorphism and automorphism
contracts; the oracle also checks the pinned traversal's labels, statistics,
and emitted generators. Run the extended oracle with
`python3 scripts/oracle/graphiso_sparse_check.py --trace-corpus` after
`lake build hexgraphiso_sparse_probe`. Runtime changes also need adjacent
AB/BA measurements against a preserved executable, following the
[shared-host protocol](../../../SPEC/benchmarking.md).
