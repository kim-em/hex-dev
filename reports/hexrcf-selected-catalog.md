# Supplied selected-root catalog replay

The regression supplies a complete serialized selected root to an empty tower
catalog with its validated rational base. Its predecessor is the selected
positive root α of `X² − 2`; its upper selected root satisfies `X² − α`.
The original statement is `∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2`.
This is a supplied-root API example, not a new tactic producer.

## Literal and source bindings

The [packet](../conformance-fixtures/HexRCF/selected-catalog.json) contains the
full predecessor suffix and upper root frame. The constructor-only
[JSON module](../conformance/HexRCF/SelectedRoot/CatalogData.lean) and
[byte module](../conformance/HexRCF/SelectedRoot/CatalogByteData.lean) contain
75 and 21 definitions respectively. The existing
[converter](../scripts/rcf/selected_literals.py) regenerates both in its CI
check. The byte literal is exactly 2,911 bytes, including the owner's trailing
space. Python proposes data; Lean checks its meaning.

[Catalog](../conformance/HexRCF/SelectedRoot/Catalog.lean) proves that the JSON
is the actual serialized selected root. Its frame proof uses the public
`Dag.encode_leaf` theorem for this one-node evidence graph, avoiding evaluation
of the native hash function. The owner's lawful decoder recovers the original
packet. [CatalogSource](../conformance/HexRCF/SelectedRoot/CatalogSource.lean)
uses `Catalog.reconstruct_suffix` and the actual root reader to reconstruct the
original parent from the empty catalog. The returned root denotes the same
ordinary real point as the checked selected-row example, and all three source
conditions hold at that point.

[CatalogBytes](../conformance/HexRCF/SelectedRoot/CatalogBytes.lean) separately
checks the exact writer output, size and lexical limits. It composes the
owner's `Serialized.readBytes_write` law with catalog reconstruction through
a variable-input parser lemma. Its source theorem explicitly names the
returned packed root and a real model of that root's parent; its final
existential theorem extracts that same point.

## Refusals and proof checks

[CatalogControls](../conformance/HexRCF/SelectedRoot/CatalogControls.lean)
checks a stale predecessor binding and a universal root-set packet supplied
to the single-root reader. The actual byte entrypoint rejects a zero byte
limit and a truncated 2,909-byte input. Removing only the final space leaves
valid syntax, so that input is not the truncation control.

The fresh [audit](../conformance/HexRCF/SelectedRoot/CatalogAudit.lean) checks
every definition in each literal module, including reachability from its
packet root. Its exact foreign computation allowlists are numeral/JSON
machinery for JSON and `UInt8.ofNat`/`UInt8.instOfNat` for bytes; constructors,
projections and proofs are allowed separately. Thirteen actual proof bodies
are rechecked with active kernel diagnostics excluding the listed native
producers. Trivial identities and simple refusal transports are checked by
the ordinary kernel without requiring artificial unfolding diagnostics.
Complete transitive proof-axiom audits allow only `propext`,
`Classical.choice` and `Quot.sound`.

## Scope

This proves one supplied selected-root packet and its source conditions.
It does not prove complete root-set coverage, produce arbitrary frozen
certificates, collect every intermediate dependency, or establish frontend
completeness. The default catalog value codecs and adjunction retain native
paths: ordinary-kernel acceptance of this packet does not establish strict
production-free compiled replay for arbitrary catalogs. The source model
and checked row remain explicit inputs to the source correspondence.

The [build record](data/hexrcf-selected-catalog/build-context.json) binds source
hashes and retained diagnostics. These are operational correctness builds,
not a paired speed comparison, asymptotic study or memory measurement. The
catalog audit and full manual build pass 13,865 Lake jobs. The manual render
passes 13,837 jobs and contains the catalog paragraphs; its source chapter has
2,989 lines. The initial namespace failure is retained separately from the
corrected integration and final complete-module audit. The
[adapter inventory](hexrcf-adapter-evidence.md) retains the full remaining
completion requirements.
