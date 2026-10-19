# Reuse of owning finite descriptor restoration

[`RootCodec.read_covered`](../adapters/HexRCF/RealCoefficients/RootCodec.lean)
delegates to the merged owner's
`Algebraic.RootReplay.readDescriptor_covered`. Its existing separate finite
head, endpoint, graph and context requirements instantiate that owner's exact
coverage lists. Its public statement is unchanged, including arbitrary caller
hashing and restoration of the original checked descriptor.

`RootCodec.replay_covered` uses `Dag.validate_encode` and
`Codec.bindings_of_validate` directly for arbitrary checked query trees. It no
longer repeats the checked-node traversal. The descriptor constructor equality
and replay reconstruction proofs reside in their existing owners. No producer
premise or global coefficient-codec law is added.

The consuming exports are merged in main through PR #10939
(`a5b2e17965`) and the proof-construction work in #10938 (`95d73a2b1a`),
contained in actual parent squash `82d5a6e0359b8502bf53b6bed62628ffae02a387`.
The adapter changes only proof bodies and their dependency audit; executable
readers and packet encoders retain their implementations.

The 10,962-job affected Lake selection checks all 21 actual serialization,
complete-read/domain/soundness proof bodies, requiring the direct owner export
and graph-validation/binding laws. Only the standard three axioms occur.
Native controls retain complete restricted-reader acceptance, omitted-zero
refusal, malformed-root refusal before folds, original guard preflight and
both constant/empty strict verdicts. DAG/umbrella, admission scan (642 cones,
1,542 local modules), copyright, selected literals and whitespace checks pass.

The [source-bound record](data/hexrcf-owner-descriptor-reuse/context.json)
retains the exact adapter/test sources, owner exports, toolchain/pins and six
raw validation logs. The selected incremental build took 30.969 s at 2.8 GiB
peak with zero swap, under the aggregate 32 GiB/two-thread/serial build limit.
This is an operational observation, with no before/after or speedup claim.
No new manual example or rendering is claimed because the public interfaces
and displayed examples are unchanged.

This proof reuse does not assemble frozen provider/predecessor histories,
authenticate arbitrary reached arithmetic records or establish strict compiled
rejection of every missing record. The complete #10358 extension and its
remaining frontend/realization/performance requirements remain open.
