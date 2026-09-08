# Long-prune proof locality

The production search scans all stored pairs. Restricting that scan to
`autos.extract (autos.size - 32) autos.size` changes traversal while preserving
the existing local correctness contracts. The bounded scan is a diagnostic
variant and is not part of the production implementation.

## Behavioural witness

[The input graph](hex-graph-iso-prune.json) has 120 vertices and one colour.
It is the disjoint union of two CFI graphs over the triangular prism.
Each base vertex has four even-parity middle vertices and three port pairs,
with ports ordered by neighbouring base vertex. One component is untwisted.
The other crosses the port connections over base edge `(0, 1)`.
The graph is relabelled using `Random.shuffle` with the UInt64 seed value `1`.

| Search policy | Visited nodes | Accepted generators |
|---|---:|---:|
| Full stored-pair scan | 168 | 11 |
| Newest 32 stored pairs | 712 | 11 |

Both runs have identical canonical rows and best path codes. The comparison
uses the actual generic recursion and engine operations, with only the long
filter changed. These node counts demonstrate different traversal, not a
performance improvement. They are not timing measurements or a replacement
for the required cactus sweep.

A separate resumed-sweep fixture retains an old checked swap followed by 32
identity pairs. The full scan exhausts its cursor, while the bounded scan
visits one additional node. The normal-root example above establishes the
behavioural difference without relying on that seeded state.

## Proof obligations

The filter's public obligations are unchanged:

- A surviving vertex belongs to the incoming target set.
- A removed vertex has a checked cell-stabilizing carrier to a smaller vertex.
- For whole-cell transport, the carrier fixes the receiving base and reaches
  a surviving vertex.

The bounded scan changes `mem_longprune` to quantify over the selected suffix.
In `longprune_drop` and `longprune_carried`, suffix membership supplies original
workspace membership. No recursive correctness proof needs alteration.
The experimental patch has 9 inserted and 5 deleted lines in two files:
`Search/Search.lean` and `Invariant/Autos.lean`.

Both the bounded variant and restored production variant build these targets
together (1,014 jobs each), including their actual
receiving and resumed-sweep rules:

- `HexGraphIso.Nauty.Policy.MaxCombine`
- `HexGraphIso.Nauty.Policy.GeneratedRoot`
- `HexGraphIso.Nauty.Correct.Certify`
- `HexGraphIso.AutComplete`

This checks structured maximum-rule assembly and generation, and the legacy
certification and generation proofs. The experiment checks the filter-dependent rules independently of first-leaf
installation and exhausted-cursor coverage. Their unconditional whole-engine
assembly is in `Policy/KeyComplete.lean` and `Policy/Complete.lean`.

Generated image coverage on the first path uses emitted scatters and recorded
orbit words. Short returns to its sibling receiver are impossible. The long
filter runs only off the first path, where checked carriers preserve matching
reference occurrence through both filters. That reference search produces an
emitted carrier when its result is consumed by the first-path sweep. Thus
this generation proof does not require a generated witness for every
implicit stored pair.

## Consequence

This optimization is local in both proof designs. It provides no exclusive
proof-locality advantage for the structured rewrite. It does show that the
new maximum and generation arguments tolerate a real change in pruning
strength without changing the recursion, ancestor-return argument, or global
invariant. The comparison supports continued correctness assembly, while
leaving broader maintainability advantages to be assessed from the finished
implementation.
