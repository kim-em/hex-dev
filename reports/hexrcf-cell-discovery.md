# Automatic ordinary sector discovery

`CellDiscover.run` composes the owner’s complete partition with the adapter’s
native carrier, full derivative root table and complete cell producers. It
requires fixed source coefficients, the ordered original divisors and the
shared formula. The caller supplies no sector points. All original divisors
are checked before partition construction, including for zero atoms and empty
domain formulas.

## One common context

[CellDiscover](../adapters/HexRCF/RealCoefficients/CellDiscover.lean) retains
the actual `Tower.Sample.Partition` and its collection. Its input conversion
transports every fixed coefficient and original guard into the same common
context. All sections, ordinary sector points, root descriptors and sign rows
are then produced in that context. Preparation, dimension and cell failures
retain separate structured causes. The produced cell JSON is a proposal for
`CellRead`, not proof evidence.

`Packet.model` obtains a compatible collection model from the actual owner
theorem. `Packet.values` preserves each source coordinate. `Packet.sound`
composes accepted complete cell replay with that model to prove the original
shared sentence at its original fixed real coefficients. `Packet.domains`
recovers every original divisor’s nonzero real value, even when normalization
removed it from the matrix. Each conclusion uses a compatible model of the actual collection.
These theorems require accepted replay; they do not infer acceptance from a
native producer result.

## Ordered boundary correspondence

[CellAlignment](../adapters/HexRCF/RealCoefficients/CellAlignment.lean)
proves that the owner partition and independently checked radical root table
have exactly the same strictly ordered interpreted boundary list. The proof
uses the actual source conversion, atom specialization, complete root union,
radical identity, full root coverage and strict ordering. Zero polynomial
factors are omitted from the carrier without deleting their matrix positions;
repeated atoms retain their occurrences. Neither root-list equality nor
squarefreeness is an extra hypothesis. The literal radical check remains an
explicit checked premise. `dimensions` derives the number of ordinary sector
points from this correspondence.

The fresh [proof audit](../conformance/HexRCF/CellDiscoverProofs.lean) rechecks
all nine actual theorem bodies. Each uses exactly `propext`, `Classical.choice`
and `Quot.sound`. Required transitive dependencies include the actual owner
partition coverage/order and complete root replay coverage/order laws.

## Construction and refusal cases

The compiled [linear](../conformance/HexRCF/CellDiscoverLinear.lean) and
[algebraic](../conformance/HexRCF/CellDiscoverAlgebraic.lean) regressions invoke
the actual producer, decode all generated cells and check both quantifiers.
The algebraic case constructs both roots and all three sectors of X²−√2,
transports nonrational guards into the enlarged common context, and rejects
its new-context packet under the old context with the exact evidence error.
No explicit sector points or stored complete fixture are supplied to discovery.
The existing selected-coefficient fixture supplies the original parent.

The [additional cases](../conformance/HexRCF/CellDiscoverCases.lean) check
eleven matrices: both selected coefficient signs, true and false formulas,
Boolean tautology, zero-atom constants, and upper-included/lower-excluded,
equal and reversed half-open domain guards. Complete root counts include
empty and deduplicated lists. Every case also refuses an original zero guard
before searching. These runtime checks are producer/checker regressions;
the generic soundness theorems supply the mathematical acceptance boundary.

## Remaining acceptance obligations

The returned native collection is not frozen context/provider/history
evidence. The existing compiled fallback on arbitrary missing predecessor
records remains outside strict replay. This API installs no new tactic handler
and does not prove general frontend acceptance or algebraic-only completeness.
`SectorRequest.points` now requests every open cell through the owner's checked
endpoint API, including the two unbounded sectors and the empty-root whole
line. Both `CellDiscover.run` and the sector existence proof use that route.
`SectorRequest.points_spec` proves joint request success and sector membership;
`CellAlignment` connects those endpoints to the checked root table. The
[decision report](hexrcf-cell-decision.md) distinguishes that progress from the
remaining full executable build, serialization and reader acceptance proof.

The [existing construction report](hexrcf-cell-build.md) documents the
explicit-point producer; the [evidence inventory](hexrcf-adapter-evidence.md)
keeps its scope separate from automatic discovery and frozen acceptance.

## Validation

The [source-bound record](data/hexrcf-cell-discovery/context.json) binds the nine
implementation/manual/target files at `56cccab8bf`. The full optional adapter,
conformance and manual build passes 14,684 jobs. The separate manual build
passes 14,257 jobs and the fresh complete renderer passes 14,259. The focused
producer regressions and fresh proof-body audit pass separately. The DAG and
umbrella check, 625 admission cones covering 1,525 local modules, eleven scanner
regressions, copyright, manual split, literal regeneration, conformance wiring,
relative links and `git diff --check` pass. The initial package-style unittest
invocation failed because its script directory was absent from the import path;
its retained failure is separate from the corrected passing direct invocation.

All six desktop/narrow captures were opened and inspected. The
[narrow code example](data/hexrcf-cell-discovery/discovery-cell-narrow-source.png)
and changed prose fit their targets, with zero descendant overflow. This is a
check of the changed section, not of unrelated horizontal overflow elsewhere
in the complete manual. Each own build uses one aggregate 32GiB cgroup, zero
swap and two Lean threads; the full build records an 8.8G peak. These are build
validation observations, not scaling measurements or a speedup claim.
