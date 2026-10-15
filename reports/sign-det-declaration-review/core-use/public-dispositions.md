# SignDet core public API dispositions

Individual public-API dispositions for the bound imported environment. The open Dependencies rows are facets of one existing cross-level production-integration requirement, not new algorithm assignments. Existing public APIs remain intact; final family acceptance remains open.

The open dependency-envelope rows refer to the [owning SPEC](../../../HexSignDet/SPEC/hex-sign-det.md) and production assembly owned by [#10378](https://github.com/kim-em/hex-dev/issues/10378) and [#10358](https://github.com/kim-em/hex-dev/issues/10358). Generic reader examples do not close that requirement. A public contract can be useful independently of current production clients; the individual reasons below record that judgment.

## `Hex.SignDet.Codec.Decimal.readInt`

Decision: retain. Retain the direct UTF-8 signed-integer entry point for codec clients that already have a decimal payload. Requiring them to invoke the JSON lexer would change the accepted language.

Runs actual UTF-8 validation before signed digit reading; it does not authenticate a coefficient or certificate.

Assessment: [core-parser.md:18](../core-parser.md). Alias-merged named clients: 2.

## `Hex.SignDet.Codec.Decimal.readIntText`

Decision: retain. Retain the character-level signed decoder as the reusable layer between UTF-8 validation and digit reading; its restricted grammar is explicit rather than hidden in a JSON instance.

Permits an optional minus and nonempty digit word, rejecting plus/fraction/exponent syntax; JSON leading zeros remain a lexer obligation.

Assessment: [core-parser.md:17](../core-parser.md). Alias-merged named clients: 3.

## `Hex.SignDet.Codec.Decimal.readInt_repr`

Decision: retain. Retain the signed printer/reader roundtrip as the codec law for both Int constructors. It removes a successful-parse premise from consumers of emitted integers.

Actual signed integer decimal printer/reader preserves both Int constructors and arbitrary magnitudes.

Assessment: [core-parser.md:21](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Decimal.readInt_toString`

Decision: retain. Retain the standard-toString specialization so byte-codec clients can use Lean's printing surface without proving how it relates to the underlying integer printer.

Standard toString specializes the same actual signed-integer byte roundtrip.

Assessment: [core-parser.md:22](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Decimal.readNat`

Decision: retain. Retain the natural-byte entry point for direct codec use, including whole-input UTF-8 rejection. It is deliberately weaker than JSON lexical validation.

Validates whole UTF-8 input before the actual digit reader; not a complete JSON-number lexer.

Assessment: [core-parser.md:11](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Decimal.readNat_repr`

Decision: retain. Retain the natural-byte roundtrip for callers emitting literal natural values; otherwise they must reconstruct the UTF-8 and digit-reader composition.

Actual natural decimal byte printer/reader roundtrip, without a parser-success premise.

Assessment: [core-parser.md:16](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.Value.writeBytes_toList`

Decision: retain. Retain the actual byte-list representation law for ordinary-kernel literal replay, where structural characters are usable but unfolding the full UTF-8 printer is unsuitable.

Exact ordinary-kernel equality exposes the actual UTF-8 byte list through structural token characters, with no performance claim.

Assessment: [core-parser.md:113](../core-parser.md). Alias-merged named clients: 5.

## `Hex.SignDet.Codec.Json.Values.toListLoop`

Decision: retain. Retain the implementation selected by the proved compiler-simplification registration for public Values.toList. Its purpose is compiler replacement, even when the imported term graph records no runtime caller.

Actual list conversion through the native width loop and array representation.

Assessment: [core-serialization.md:113](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Json.Values.toList_impl`

Decision: retain. Retain the proved csimp registration: deleting it changes how public list conversion compiles. Named declaration references do not inventory compiler registration uses.

Proved csimp replacement preserves exact reference list semantics while changing only compiled width traversal.

Assessment: [core-serialization.md:114](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.of_array`

Decision: retain. Retain the array-encoding representation law so external codec proofs can expose ordered element encoding without unfolding the To instance.

The actual array instance maps the supplied element dictionary in literal order.

Assessment: [core-serialization.md:126](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.of_list`

Decision: retain. Retain the corresponding list-encoding law: callers supply a List rather than an Array and need the exact ordered conversion before applying element-codec laws.

The actual list instance uses the same ordered array construction.

Assessment: [core-serialization.md:127](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.read_of_bool`

Decision: retain. Retain this terminating simp rule for the scalar Boolean dictionary. Simplification of anonymous or external examples need not leave a named-client edge.

Actual Boolean scalar dictionaries roundtrip exactly; appropriate simp normalization.

Assessment: [core-serialization.md:128](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.read_of_string`

Decision: retain. Retain this scalar string roundtrip as simp normalization; it discharges literal dictionary decoding without exposing the JSON representation.

Actual string scalar dictionaries roundtrip exactly; appropriate simp normalization.

Assessment: [core-serialization.md:129](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.readBodyLoop_spec`

Decision: retain. Retain the native/reference parser agreement for arbitrary malformed inputs and fuel. A printer-only roundtrip would not support clients reasoning about rejection.

Public exact native/reference agreement covers malformed input and insufficient fuel, not just emitted strings.

Assessment: [core-parser.md:44](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.readBytes`

Decision: retain. Retain the whole-byte quoted-string reader for direct string-codec clients; it checks the trailing-input condition that the prefix reader intentionally omits.

Requires valid whole UTF-8 and empty character suffix after the quoted prefix; trailing bytes reject.

Assessment: [core-parser.md:49](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Str.readBytes_write`

Decision: retain. Retain the whole-byte Unicode roundtrip, so users of the quoted-string encoder do not have to combine escaping, UTF-8 and suffix lemmas themselves.

Every actual emitted Unicode string byte record reconstructs exactly, with no assumed parser-success or resource policy.

Assessment: [core-parser.md:50](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.scanLoop_spec`

Decision: retain. Retain the prefix-scan characterization independently of parsing success; byte-bound proofs must reason about consumption even when escape validation later fails.

Public exact zero-accumulator scan agreement; it makes no syntax-validation claim.

Assessment: [core-parser.md:45](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.writeBytes`

Decision: retain. Retain the public quoted-string byte encoder paired with readBytes and its roundtrip. It is a literal wire operation rather than a certificate producer.

Uses actual quoted escaping then UTF-8 encoding of the complete result.

Assessment: [core-parser.md:48](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Token.chars`

Decision: retain. Retain the structural token printer used to expose bytes to kernel proofs without reparsing an integer's printed characters.

Structural character printer preserves literal token values without reparsing emitted integer text.

Assessment: [core-parser.md:56](../core-parser.md). Alias-merged named clients: 7.

## `Hex.SignDet.Codec.Token.emit_eq_chars`

Decision: retain. Retain the equality connecting the structural character printer to the actual token emitter. It lets literal replay proofs choose the useful representation without changing emitted data.

Public exact equality of the two printers covers every token constructor; no byte allocation/timing conclusion follows.

Assessment: [core-parser.md:57](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Token.lexLoop_spec`

Decision: retain. Retain the actual/reference lexer equivalence for arbitrary streams and fuel; acceptance and refusal proofs cannot be replaced by the emitted-token roundtrip alone.

Public exact zero-prefix native/reference agreement applies to malformed streams and insufficient fuel.

Assessment: [core-parser.md:72](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.bindings_iff`

Decision: retain. Retain the exact context/head/endpoint guard characterization used by FastCheck.graph_roundtrip. Query identities and arithmetic replay remain separate, so the lemma does not overstate decode-time authentication.

Exact decode-time context/head/endpoints criterion for node and every moment; query lists/polynomials and arithmetic acceptance remain replay obligations. Reused in the existing false-graph control.

Assessment: [core-serialization.md:75](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.decodeGraph`

Decision: retain. Retain the raw graph byte-reader entry point for callers that need parsing without arithmetic replay. Combining it silently with replay would remove that useful separation.

Runs actual lexical policy, UTF-8/JSON parsing and complete raw-graph reading; no arithmetic replay is claimed.

Assessment: [core-serialization.md:135](../core-serialization.md). Alias-merged named clients: 15.

## `Hex.SignDet.Codec.decodePair_error`

Decision: retain. Retain the first-record error law so callers can prove short-circuit refusal without evaluating the evidence parser or local reader.

An error in the first record returns exactly that error without evaluating the evidence parser or reader.

Assessment: [core-serialization.md:35](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.decodePair_ok`

Decision: retain. Retain the accepted-pair substitution law for clients supplying concrete parse results; it isolates the structured reader from parser implementation details.

Substitutes the actual two accepted parse results before applying the unchanged structured reader.

Assessment: [core-serialization.md:34](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.decode_graph`

Decision: retain. Retain the full graph byte-roundtrip theorem with its real resource precheck, lawful codecs and subject bounds. It is the public route from printed evidence to the original raw graph.

Full graph byte roundtrip requires lawful codecs, structural/subject bounds and success of the exact encoded-byte resource check. Reuses the actual JSON/graph path; does not certify arithmetic.

Assessment: [core-graph-codec.md:22](../core-graph-codec.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.decode_graph_covered`

Decision: retain. Retain the finite-coverage specialization for carriers without a globally lawful codec. Removing it would force stronger global hypotheses on finite certificate replay.

Composes exact byte parsing and graph reconstruction under success of the actual byte/resource check and finite stored-value coverage. Independent arithmetic replay can still reject.

Assessment: [core-graph-codec.md:37](../core-graph-codec.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.encoded_graph`

Decision: retain. Retain the unconditional JSON-image characterization separately from bounded graph decoding. Callers must not need graph validity merely to expose the encoder's literal output.

Byte decoding of the encoder yields the exact JSON graph unconditionally; no graph validity or parser-limit claim follows.

Assessment: [core-graph-codec.md:21](../core-graph-codec.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.forIn_data`

Decision: retain. Retain the generic early-exit byte/array iteration correspondence used in literal guard proofs. It justifies the logical traversal, without asserting an allocation measurement.

Proves the actual byte-array loop agrees with array iteration, including early exit; no compiled allocation claim follows from this equality.

Assessment: [core-serialization.md:29](../core-serialization.md). Alias-merged named clients: 7.

## `Hex.SignDet.Dag.bindDomain_isSome`

Decision: retain. Retain the bidirectional binding criterion so users can characterize rejection as well as success without opening the dependent memo constructor.

Characterizes success by those three exact equalities. Equality in a mathematical interpretation does not suffice.

Assessment: [core-dag.md:33](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.bindDomain_self`

Decision: retain. Retain the unchanged-domain law as the standard identity case of memo rebinding, avoiding repeated proof-transport construction in clients.

Supplies the unchanged-domain success law without requiring callers to unfold proof transport.

Assessment: [core-dag.md:34](../core-dag.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.bindDomain_values`

Decision: retain. Retain the complete stored-value projection for rebinding clients; it guarantees the returned memo uses the original literal trees rather than freshly produced evidence.

Preserves all stored literal trees on acceptance and records rejection when any binding differs.

Assessment: [core-dag.md:35](../core-dag.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.changeOps_isSome`

Decision: retain. Retain optional-presence preservation as a separate operational transport law; users need not unpack a memo merely to show transport preserves refusal.

Operation transport preserves exactly whether the optional memo is present.

Assessment: [core-dag-support.md:56](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.changeOps_nodes`

Decision: retain. Retain the all-node projection for operation transport, including unreachable entries. A selected-root-only statement would be insufficient for later full replay.

Every stored literal node survives transport, including nodes not selected by a root lookup.

Assessment: [core-dag-support.md:57](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.changeOps_values`

Decision: retain. Retain ordered literal-value preservation across the operation transport, so evidence consumers can connect the transported memo to the original data without rerunning a checker.

Complete literal replay values survive operation transport, in order and with both successful and absent memos covered.

Assessment: [core-dag-support.md:55](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.check_sign_congr`

Decision: retain. Retain full-graph checker congruence for arbitrary stored operands, including malformed and unreachable entries. It is the finite-dependency interface needed by proof assembly.

Graph Boolean checking depends only on that complete finite operand inventory, including malformed and unreachable entries.

Assessment: [core-dag-support.md:63](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.children_mapNodes`

Decision: retain. Retain ordered-edge preservation for graph clients changing carriers or contexts; preserving only graph size or root index would not justify reusing child references.

Both ordered child references remain literally unchanged.

Assessment: [core-dag-support.md:21](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeBytes`

Decision: retain. Retain the checked byte-replay entry point alongside the raw parser. Its returned checked tree and exact refusal protocol are a distinct public operation.

Actual parsing followed by independent replay returns a tree with erased checker acceptance; parse/refusal errors are not mathematical nonexistence.

Assessment: [core-serialization.md:137](../core-serialization.md). Alias-merged named clients: 6.

## `Hex.SignDet.Dag.decodeBytes_sign_congr`

Decision: retain. Retain exact byte-replay error and tree preservation under finite sign agreement, allowing callers to replace a provider without assuming parsing succeeded.

Finite sign agreement on every actual decoded graph operand preserves exact parse/replay errors and literal returned tree values.

Assessment: [core-serialization.md:141](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.decodeDescriptor`

Decision: retain. Retain descriptor-bound replay as the public entry point authenticating the entire requested raw selection, rather than trusting a serialized count-one assertion.

Replays against the complete supplied raw descriptor, deriving derivative queries from actual head/indices; serialized count-one assertions are not trusted.

Assessment: [core-serialization.md:138](../core-serialization.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dag.decodeDescriptor_raw`

Decision: retain. Retain the raw-field projection for accepted descriptor reads so downstream code can recover the exact requested indices and signs without opening dependent proof fields.

Every accepted descriptor byte read retains all original raw fields, including derivative indices and signs.

Assessment: [core-serialization.md:144](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeDescriptor_sign_congr`

Decision: retain. Retain literal selected-root identity and evidence preservation when the provider changes. Optional success alone would lose the returned descriptor's binding.

Finite stored-operand agreement preserves raw selected-root identity and supplied evidence, including exact refusal errors.

Assessment: [core-serialization.md:143](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.decodeSigns`

Decision: retain. Retain supplied selected-sign replay separately from sign production. This operation validates the caller's vector and evidence without manufacturing missing lower facts.

Checks exactly the caller sign vector using supplied joint graph evidence; no selected-sign producer fills missing evidence.

Assessment: [core-serialization.md:139](../core-serialization.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dag.decodeSigns_evidence`

Decision: retain. Retain the arbitrary-byte acceptance characterization identifying the actual graph and evidence; a roundtrip restricted to the encoder's output cannot replace it.

Arbitrary accepted bytes identify the actual parsed graph, exact selected evidence and unchanged claimed signs, with no printer-success assumption.

Assessment: [core-serialization.md:140](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeSigns_sign_congr`

Decision: retain. Retain exact refusal, sign and evidence transport across provider changes, even when the validated descriptor's proof fields differ.

Finite stored-operand agreement and equal raw descriptor identity preserve exact errors, sign vector and literal evidence; validated proofs may differ.

Assessment: [core-serialization.md:142](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decode_replays`

Decision: retain. Retain the accepted-byte decomposition for independent parser/replay clients. It applies without printer provenance or a global codec-law hypothesis.

Arbitrary accepted bytes identify the exact parsed graph and actual replay result; no encoder or global codec law premise.

Assessment: [core-serialization.md:145](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.descriptor_sign_congr`

Decision: retain. Retain descriptor-extraction congruence with literal bindings, so finite evidence transport does not accidentally identify different requested selections.

Finite sign agreement preserves exact raw descriptor/evidence data or rejection; context, head and endpoints remain literal inputs.

Assessment: [core-dag-support.md:64](../core-dag-support.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dag.encodeBytes`

Decision: retain. Retain the literal graph printer independently of production and validity checks, permitting external certificate transport and negative fixtures.

Prints all literal graph fields without running a producer or validating mathematical evidence.

Assessment: [core-serialization.md:136](../core-serialization.md). Alias-merged named clients: 8.

## `Hex.SignDet.Dag.encode_leaf`

Decision: retain. Retain the one-leaf encoding law as the concrete initial graph case, without forcing clients to assume hash laws or evaluate the native hash table.

Actual encoding of a single leaf produces that literal node at index zero with no children. The empty-map proof needs no lawful-hash hypothesis or native hash-table evaluation. It establishes no replay acceptance.

Assessment: [core-codec-coefficients.md:29](../core-codec-coefficients.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dag.mapNodes`

Decision: retain. Retain the carrier/context mapping operation that preserves graph sharing and edges. Rebuilding an expanded tree would alter the evidence representation and cost model.

Transforms each stored node once and retains all indices, edges and the selected root across carrier/context types. It transports no arithmetic acceptance.

Assessment: [core-dag-support.md:18](../core-dag-support.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dag.node_mapNodes`

Decision: retain. Retain the indexed-node mapping law so clients can reuse a checked index and recover the corresponding transformed node directly.

Retrieves exactly the transformed original node at a valid original index.

Assessment: [core-dag-support.md:20](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.replay_sign_congr`

Decision: retain. Retain optional whole-tree replay congruence over the finite stored inventory. It avoids imposing recursive rechecking of an expanded tree on evidence transport.

Agreement on all stored sign operands preserves the exact optional returned tree without recursively rechecking an expanded tree.

Assessment: [core-dag-support.md:62](../core-dag-support.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dag.root_mapNodes`

Decision: retain. Retain literal root-index preservation even on malformed graphs; validity hypotheses would unnecessarily restrict raw transport and rejection proofs.

Root index is unchanged even for malformed raw graphs.

Assessment: [core-dag-support.md:22](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.select_isSome`

Decision: retain. Retain the exact lookup/query criterion for arbitrary checked memos, distinguishing an available index from a correctly bound selection.

Characterizes arbitrary memo selection in both directions: an existing index and exact query binding. No producer provenance or root semantics are assumed.

Assessment: [core-dag.md:31](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.select_values`

Decision: retain. Retain the selected literal tree and both failure cases, so users need not unfold memo lookup to connect supplied checked evidence to its stored value.

Identifies the exact returned tree at a matching stored entry and gives no tree for either rejection branch. It applies to any supplied checked memo.

Assessment: [core-dag.md:30](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_checked`

Decision: retain. Retain the bridge from graph extraction to the independent descriptor tree checker. It exposes the postcondition consumers actually need for arbitrary accepted evidence.

Successful graph extraction passes the independent descriptor tree checker for the original supplied query list and vector.

Assessment: [core-dag-support.md:74](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_encode`

Decision: retain. Retain preservation of an already accepted selected-sign tree through encoding, including its exact literal evidence rather than only existence.

Encoding existing accepted selected-sign evidence preserves acceptance and the exact literal evidence tree.

Assessment: [core-dag-support.md:76](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_encode_eq`

Decision: retain. Retain the stronger acceptance-and-refusal encoding equality for arbitrary supplied trees; the successful-evidence specialization alone cannot support negative transport tests.

Encoding any supplied tree preserves both selected-sign acceptance and rejection, including malformed query/matrix evidence or a wrong vector.

Assessment: [core-dag-support.md:77](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_memo`

Decision: retain. Retain the equivalence between validated-memo selection and graph checking, so shared-evidence consumers can reuse a memo without changing refusal behavior.

Selecting from an actually validated memo equals graph selected-sign checking, including refusal and complete returned evidence.

Assessment: [core-dag-support.md:72](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_replay`

Decision: retain. Retain the post-replay equivalence with the original selected-sign tree check. It separates graph reconstruction from checking the caller's claimed vector.

After actual graph replay succeeds, selected-sign presence equals the original tree checker on the exact claimed vector.

Assessment: [core-dag-support.md:75](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_sign_congr`

Decision: retain. Retain finite-provider congruence while allowing descriptor proof fields and source replays to differ; requiring dependent-record equality would be unnecessarily strong.

Finite stored-node sign agreement and equal raw descriptor identity preserve the optional sign/evidence data. Descriptor proof fields and source replays may differ.

Assessment: [core-dag-support.md:78](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.signOperands`

Decision: retain. Retain the complete stored-node operand inventory used by congruence, including unreachable nodes that full validation still checks.

Collects local-node sign dependencies from every stored entry, including unreachable entries; it is not just a selected-root inventory.

Assessment: [core-dag-support.md:58](../core-dag-support.md). Alias-merged named clients: 14.

## `Hex.SignDet.Dag.size_mapNodes`

Decision: retain. Retain array-length preservation as the index-validity interface for clients mapping raw graphs; root preservation alone gives no such bound.

Preserves array length, including unreachable entries.

Assessment: [core-dag-support.md:19](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.step_sign_congr`

Decision: retain. Retain local replay-step congruence with equal literal memo values, enabling modular whole-graph proofs that preserve rejection as well as success.

Finite local sign agreement and equal literal memo values preserve the optional step value across sign indices, including rejection.

Assessment: [core-dag-support.md:59](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.validate_get`

Decision: retain. Retain indexed memo/node correspondence with both successful lookups, rather than forcing users to reconstruct the validation fold.

Connects two successful indexed lookups to the same literal node, retaining both lookup hypotheses.

Assessment: [core-dag.md:27](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.validate_root`

Decision: retain. Retain the distinction between all-node validation and root selection. It lets callers reuse validation after changing the requested root while still checking the index separately.

Changing only the selected root leaves validation unchanged. A root index is checked at selection.

Assessment: [core-dag.md:28](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.validate_size`

Decision: retain. Retain the memo-length postcondition needed to justify later indexing without unfolding every validated entry.

Characterizes the memo length after success; delegates to exact node correspondence.

Assessment: [core-dag.md:26](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Checked`

Decision: open. Open integration item: identify the production local-reader result type that supplies actual coefficient-sign proofs. A packet paired with an arbitrary dependent value is not itself mathematical acceptance.

Retains a literal packet and a result of the caller-supplied dependent type. Mathematical acceptance depends on what that type and reader actually establish.

Assessment: [core-dependencies.md:20](../core-dependencies.md). Alias-merged named clients: 20.

## `Hex.SignDet.Dependencies.Decoded`

Decision: open. Open integration item: connect the stored graph and typed memo to the actual tower/tactic reader. The record's binding proofs do not establish provenance of local semantic facts.

Stores the graph, typed memo and proofs of ordered requested bindings, structural validity and exact entry retention. It records no parse or reader-acceptance provenance; mathematical facts must be carried by the caller's result type.

Assessment: [core-dependencies.md:38](../core-dependencies.md). Alias-merged named clients: 12.

## `Hex.SignDet.Dependencies.Decoded.memo_size`

Decision: open. Open integration item: use the one-result-per-packet bound in the production shared inventory, including unused packets. Existing finite examples do not supply automatic all-live assembly.

Literal memo-entry equality gives exactly one position per stored packet, including unused packets; existing selection proofs reuse the length law.

Assessment: [core-dependencies.md:39](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Decoded.results`

Decision: open. Open integration item: connect non-fallible root-order selection to the actual requested tower facts, including repeated requests. The generic selector already exists; its production application remains missing.

Selects stored memo values in root order using proved structural bounds and exact memo-entry equality; repeated roots reuse values and cannot fail.

Assessment: [core-dependencies.md:40](../core-dependencies.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dependencies.Decoded.results_bound`

Decision: open. Open integration item: make the production consumer use the full ordered level/subject binding, rather than accepting an index or context hash as sufficient evidence.

Selected memo results have precisely the requested ordered levels and full literal subjects.

Assessment: [core-dependencies.md:41](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Decoded.results_size`

Decision: open. Open integration item: verify that the production requested-fact list and selected memo results have this exact length, including empty and repeated requests.

Selected result count equals the requested binding count, including empty and repeated roots.

Assessment: [core-dependencies.md:42](../core-dependencies.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Entry`

Decision: open. Open integration item: specify how actual coefficient contexts, operands and child facts are serialized into each production packet. The raw entry type intentionally supplies no validity proof.

Stores level, subject, payload and ordered child references. Its type alone enforces no acyclicity, lower level or arithmetic validity.

Assessment: [core-dependencies.md:15](../core-dependencies.md). Alias-merged named clients: 68.

## `Hex.SignDet.Dependencies.Entry.codec`

Decision: open. Open integration item: use this literal packet codec in the production cross-level format, preserving child order and complete subjects rather than replacing them with weaker identifiers.

Retains level, subject, payload and ordered children literally; parsing supplies raw packets without acceptance.

Assessment: [core-dependencies.md:33](../core-dependencies.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dependencies.Entry.codec_lawful`

Decision: open. Open integration item: apply the actual packet roundtrip law to the production evidence envelope. A lawful raw codec does not establish semantic correctness of a local reader.

Literal packet tuple roundtrip uses the reference codec law for every child, with no graph premise.

Assessment: [core-dependencies.md:34](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph`

Decision: open. Open integration item: construct the production dependency graph of all reached facts, with shared and unreachable packets explicitly accounted for under the owning SPEC.

Stores entries and ordered roots, including shared and unreachable packets; validity is separate.

Assessment: [core-dependencies.md:16](../core-dependencies.md). Alias-merged named clients: 18.

## `Hex.SignDet.Dependencies.Graph.check`

Decision: open. Open integration item: connect production graph acceptance to every backward/lower-level reference, including unreachable entries. A successful small supplied graph does not establish this automatic assembly.

Checks every root and every stored child. Child indices point backward and levels strictly decrease; unreachable packets remain checked.

Assessment: [core-dependencies.md:19](../core-dependencies.md). Alias-merged named clients: 8.

## `Hex.SignDet.Dependencies.Graph.check_children`

Decision: open. Open integration item: use the complete child-reference postcondition in production reader assembly, so missing or stale predecessor facts cannot be bypassed.

Extracts all backward-index, lower-level and literal-reference conditions for every declared child of every stored entry.

Assessment: [core-dependencies.md:25](../core-dependencies.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Graph.check_roots`

Decision: open. Open integration item: connect each actual requested root reference to its full level/subject binding in the production decoder, including duplicate requests.

Extracts index existence and exact level/subject binding for each declared result; repeated roots are allowed.

Assessment: [core-dependencies.md:26](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Graph.codec`

Decision: open. Open integration item: settle the actual production use of the versioned cross-level envelope while preserving the current raw syntax and unsupported-version refusal.

Version-one tuple retains all entries and roots in wire order; unsupported version and malformed tuples reject independently of arithmetic.

Assessment: [core-dependencies.md:35](../core-dependencies.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dependencies.Graph.codec_bytes`

Decision: open. Open integration item: exercise actual production evidence bytes through the lexical/resource precheck and complete graph parser, then perform semantic replay separately.

Actual byte parser reconstructs the whole literal graph from printer output under the lexical/resource precheck, without assuming parser success or arithmetic validity.

Assessment: [core-dependencies.md:37](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph.codec_lawful`

Decision: open. Open integration item: compose the raw graph codec law with the production checked-reader path. This theorem deliberately also covers invalid raw graphs.

Literal envelope print/read roundtrip for arbitrary raw graphs, including structurally invalid ones.

Assessment: [core-dependencies.md:36](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph.decode`

Decision: open. Open integration item: supply the actual production local reader and ordered caller bindings. The generic decoder checks supplied data but never creates missing coefficient evidence.

Parses actual bytes, compares complete ordered caller bindings before any local reader, then validates all packets and stores actual accepted memo. No missing evidence is produced.

Assessment: [core-dependencies.md:43](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Graph.decode_encode`

Decision: open. Open integration item: instantiate the composed printer/parser/validation theorem with the production reader's actual accepted memo and resource precheck.

Composes actual printer/parser with the supplied accepted reader result; returns exactly that memo under only the byte precheck and actual validation premise.

Assessment: [core-dependencies.md:44](../core-dependencies.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Graph.validate?`

Decision: open. Open integration item: connect the all-packet validation fold to the production reader and its local semantic proof contract. Structural success alone does not prove the reader sound.

Rejects structural failures before folding all packets through the actual reader from an empty memo; does not prove the reader sound.

Assessment: [core-dependencies.md:23](../core-dependencies.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dependencies.Graph.validate_check`

Decision: open. Open integration item: propagate the generic decoder's structural acceptance into the production shared-evidence consumer without treating it as a semantic theorem about arbitrary result values.

Accepted typed validation implies its prior structural guard; no semantic reader soundness is inferred.

Assessment: [core-dependencies.md:30](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Graph.validate_entries`

Decision: open. Open integration item: make the production consumer retain the entire literal entry array, including unused packets, rather than rebuilding only selected facts.

Actual accepted validation returns exactly the full literal entry array, including payloads, children and unreachable entries.

Assessment: [core-dependencies.md:29](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Reference`

Decision: open. Open integration item: construct production references with exact coefficient level and complete subject. An index or context hash alone does not meet this interface.

Stores index, coefficient level and complete literal JSON subject; equality is not reduced to a context hash.

Assessment: [core-dependencies.md:14](../core-dependencies.md). Alias-merged named clients: 33.

## `Hex.SignDet.Dependencies.Reference.check`

Decision: open. Open integration item: apply the actual index/level/full-subject guard to every production dependency reference, including negative stale-reference cases.

Checks index existence and exact level/subject binding against the literal referenced entry.

Assessment: [core-dependencies.md:18](../core-dependencies.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dependencies.Reference.check_eq`

Decision: open. Open integration item: use the exact acceptance equivalence in production assembly, rather than deriving predecessor identity from a successful example output.

Bidirectional success criterion gives the exact existing index, level and complete subject; no semantic premise is hidden.

Assessment: [core-dependencies.md:24](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Reference.codec`

Decision: open. Open integration item: route the literal reference codec through the production shared-evidence format. Parsing the tuple supplies no valid-index theorem.

Integer-only JSON tuple retains index, level and complete literal subject; decoder performs syntax/type checks rather than graph validity.

Assessment: [core-dependencies.md:31](../core-dependencies.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dependencies.Reference.codec_lawful`

Decision: open. Open integration item: compose the reference roundtrip with actual production packet encoding, retaining invalid-index rejection at the graph layer.

Literal tuple print/read roundtrip for every reference, including invalid indices.

Assessment: [core-dependencies.md:32](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Reference.matches`

Decision: open. Open integration item: distinguish the production subject/level comparison from actual indexed-reference validation. The matching predicate alone cannot authenticate a predecessor.

Tests exact level and subject equality, without checking the referenced index or interpreting either packet.

Assessment: [core-dependencies.md:17](../core-dependencies.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dependencies.children?`

Decision: open. Open integration item: connect ordered lower-level child lookup to production local reading, preserving refusal for missing, foreign or stale facts before the reader runs.

Reads declared children from the supplied memo in order, requires exact subject/level matching and a lower level; missing or stale references reject before local reading.

Assessment: [core-dependencies.md:21](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.step`

Decision: open. Open integration item: instantiate the typed local-reader step with production arithmetic/sign evidence and its semantic contract; coverage is not supplied by the generic fold.

Invokes the supplied reader only after child lookup succeeds, and retains its exact dependent result with the supplied entry. Coverage is still the local reader contract.

Assessment: [core-dependencies.md:22](../core-dependencies.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dependencies.step_entry`

Decision: open. Open integration item: propagate literal packet identity from local reading to production evidence reconstruction, without inferring extra semantic facts from the dependent result type.

Accepted local reading returns the exact supplied packet, for any caller-supplied Type-valued result.

Assessment: [core-dependencies.md:27](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Descriptor.buildRoots_constant`

Decision: retain. Retain the constant-head output specialization with an explicit successful-result premise; it characterizes returned shape without falsely promising domain preparation.

A successful constant-head result is empty by the positive-degree shape requirement on every possible descriptor; this alone does not claim all constant inputs prepare successfully.

Assessment: [core-root-list.md:39](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.buildRoots_perm`

Decision: retain. Retain exact preservation of full produced words for clients using the public producer, instead of requiring them to open its table-extraction composition.

Successful public output preserves every full word of the actual produced table, including the constant/empty case.

Assessment: [core-root-list.md:40](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.buildRoots_raw`

Decision: retain. Retain the raw subject/index postcondition for every returned descriptor, which is needed independently of mathematical root coverage.

All returned descriptors retain the requested subject and full indices, including singleton lists.

Assessment: [core-root-list.md:38](../core-root-list.md). Alias-merged named clients: 1.

## `Hex.SignDet.Descriptor.buildRoots_sorted`

Decision: retain. Retain the public producer's strict comparator-order postcondition. It states executable order separately from the companion's interpreted root order.

Successful output is strictly pairwise ordered by the actual comparator; companion root-order interpretation remains explicit.

Assessment: [core-root-list.md:41](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.build_domain`

Decision: retain. Retain the exact failed-preparation diagnostic law so callers can distinguish domain rejection from malformed selection or context errors.

Exact failed preparation yields the domain diagnostic when context agrees; an unrelated prepared object cannot discharge it.

Assessment: [core-descriptors.md:65](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.build_malformed`

Decision: retain. Retain the malformed-selection diagnostic with the actual preparation/context premises, preserving the constructor's error priority.

With exact successful preparation and matching context, a rejected shape yields the malformed diagnostic. The diagnostic order is preserved.

Assessment: [core-descriptors.md:66](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.changeOps_evidence`

Decision: retain. Retain literal replay preservation under operation transport; clients should not have to reopen the descriptor to show no certificate was regenerated.

The entire replay is literally preserved; no checker or arithmetic producer is rerun.

Assessment: [core-handles.md:32](../core-handles.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.compare_ofError`

Decision: retain. Retain the diagnostic fallback characterization specifically to prevent treating its operational eq result as equality of selected roots.

Pins the diagnostic fallback to eq even if the ambient Ordering inhabitant differs; this is an operational fact, not equality of the selected roots.

Assessment: [core-comparison.md:35](../core-comparison.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.ofChecked_evidence`

Decision: retain. Retain the simp projection from a checked descriptor constructor to its original replay, so dependent packaging remains hidden from clients.

Simp projection preserves literal replay, rather than reconstructing another certificate.

Assessment: [core-descriptors.md:45](../core-descriptors.md). Alias-merged named clients: 3.

## `Hex.SignDet.Descriptor.ofTable_evidence`

Decision: retain. Retain the evidence projection for the table-reuse constructor, whose supplied shared replay differs from a new standalone production run.

Exact replay projection from table reuse, with the same dependent acceptance proof.

Assessment: [core-descriptors.md:51](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.prepareQueries_isSome`

Decision: retain. Retain the bidirectional query-handle existence criterion based on actual preparation, allowing callers to reason about readiness without producing signs.

Characterizes handle existence by actual preparation success, in both directions, without running selected-query production.

Assessment: [core-handles.md:19](../core-handles.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFromTable_perm`

Decision: retain. Retain exact word preservation on the shared-table path, rather than forcing clients through the proof of its reference-path agreement.

Transfers exact supplied-word preservation through the proved shared/reference-path agreement.

Assessment: [core-root-list.md:30](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFromTable_sorted`

Decision: retain. Retain strict ordering on the shared-table path with its supplied accepted evidence; the actual-producer order theorem has different premises.

Transfers strict finite order through that same agreement.

Assessment: [core-root-list.md:31](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFrom_counts`

Decision: retain. Retain count-one consequences for arbitrary successful extraction. It is the public guard postcondition, independent of how a table was produced.

Arbitrary successful extraction implies count one for every supplied row. The proof follows each count guard and actual recursive result; no producer provenance is assumed.

Assessment: [core-root-list.md:27](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFrom_length`

Decision: retain. Retain the assembly-length projection for successful extraction so callers need not derive it again from a permutation or unfold recursion.

Derives exact output length from the existing permutation law, without unfolding recursion downstream. This is an assembly count, not a theorem about polynomial multiplicity.

Assessment: [core-root-list.md:26](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.signAt_ternary`

Decision: retain. Retain the total-result representation invariant, including the diagnostic zero branch, while keeping selected-root semantics in the companion.

Successful values are ternary by table invariants. Lean's diagnostic default branch is also zero; this representation fact alone gives no selected-root semantics.

Assessment: [core-selected.md:35](../core-selected.md). Alias-merged named clients: 0.

## `Hex.SignDet.Node.check_sign_congr`

Decision: retain. Retain node-level provider congruence for arbitrary matrices and witnesses, enabling finite evidence substitution without assuming producer provenance.

Preserves the actual node result for arbitrary matrices and witnesses. Rank, support and literal guards are unaffected by changing the sign provider.

Assessment: [core-foundation.md:63](../core-foundation.md). Alias-merged named clients: 2.

## `Hex.SignDet.Node.signOperands`

Decision: retain. Retain the node's full preparation/moment/reduction inventory as the executable input to its sign-congruence contract; domain caching does not remove dependencies.

Includes preparation and every indexed moment/reduction. A native domain cache does not shrink the hypotheses of full replay.

Assessment: [core-foundation.md:62](../core-foundation.md). Alias-merged named clients: 10.

## `Hex.SignDet.QueryHandle.checkSigns`

Decision: retain. Retain the arbitrary-evidence replay operation on a prepared handle; users need it independently of selected-sign production and cached domain data.

Checks arbitrary supplied evidence against the original validated descriptor; stored domain data do not replace that checker.

Assessment: [core-handles.md:25](../core-handles.md). Alias-merged named clients: 1.

## `Hex.SignDet.QueryHandle.checkSigns_eq`

Decision: retain. Retain the exact checker identity for handle clients, hiding the handle representation while exposing unchanged arbitrary-evidence validation.

Exposes the exact checker identity for any handle and supplied query/vector/replay, without semantic or producer premises.

Assessment: [core-handles.md:26](../core-handles.md). Alias-merged named clients: 0.

## `Hex.SignDet.QueryReduction.checkFrom_sign_congr`

Decision: retain. Retain ordered query-reduction congruence, including index progression and mismatched-list rejection; the single-step reduction law is insufficient.

Preserves query order and index progression; the empty and mismatched cases remain part of the theorem.

Assessment: [core-foundation.md:59](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.RawDescriptor.check_count`

Decision: retain. Retain the finite-observation count postcondition with explicit interpretation and well-formedness hypotheses; it supports models beyond ordinary-real root sets.

With explicit valid observations and replay interpretation, the exact finite observation list contains the selected word once. Repeated observations count separately; ordinary-root distinctness is a companion requirement.

Assessment: [core-descriptors.md:58](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Reduction.checkFrom_sign_congr`

Decision: retain. Retain whole reduction-chain congruence across missing or extra steps, rather than offering a theorem only for successfully produced chains.

Induction covers missing and extra factors/steps as well as accepted chains. It transports checker results, not just successful producer outputs.

Assessment: [core-foundation.md:58](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.ReductionStep.check_sign_congr`

Decision: retain. Retain the local checker law identifying exactly which two scale signs may change; polynomial and literal checks remain intact.

Agreement on both scales preserves the actual step checker; polynomial identities and literal bindings remain checked.

Assessment: [core-foundation.md:57](../core-foundation.md). Alias-merged named clients: 2.

## `Hex.SignDet.ReductionStep.signOperands`

Decision: retain. Retain both scale operands even when the step later rejects, so dependency collection is independent of acceptance.

Includes both supplied scales, regardless of eventual acceptance or use.

Assessment: [core-foundation.md:55](../core-foundation.md). Alias-merged named clients: 4.

## `Hex.SignDet.Reencoding.count`

Decision: retain. Retain the finite-observation count interface for accepted re-encoding, with its actual interpretation premises rather than an implicit root-semantics assumption.

Converts that count to an occurrence count only under finite observation well-formedness and replay interpretation; it does not infer root interpretation from table shape.

Assessment: [core-comparison.md:21](../core-comparison.md). Alias-merged named clients: 0.

## `Hex.SignDet.Replay.check_sign_congr`

Decision: retain. Retain recursive replay congruence preserving support checks and all refusal paths. It transports evidence under supplied facts and does not produce those facts.

Structural induction preserves both child restrictions, their support-completeness checks and all rejection paths. It neither constructs coefficient evidence nor proves a joint field realization.

Assessment: [core-foundation.md:65](../core-foundation.md). Alias-merged named clients: 6.

## `Hex.SignDet.Replay.signOperands`

Decision: retain. Retain literal occurrence-based dependency collection for tree replay; deduplicated cross-level sharing is a separate representation.

Traverses the literal tree, preserving repeated subtrees and values as occurrences. Evidence sharing across coefficient-field levels belongs to another API.

Assessment: [core-foundation.md:64](../core-foundation.md). Alias-merged named clients: 5.

## `Hex.SignDet.Replay.support_complete`

Decision: retain. Retain the support-completeness interface used in count recovery, with moment interpretation explicit instead of inferred from an inverse matrix.

Specializes the same induction to the computational count-recovery proof; semantic consumers separately derive its moment interpretation.

Assessment: [core-tables.md:26](../core-tables.md). Alias-merged named clients: 2.

## `Hex.SignDet.Replay.support_iff`

Decision: retain. Retain exact support membership for accepted replay, combining completeness and absence of spurious positive columns without conflating membership and multiplicity.

Combines coverage and absence of spurious positive columns to characterize support exactly. Repeated observations affect counts, not membership.

Assessment: [core-tables.md:27](../core-tables.md). Alias-merged named clients: 0.

## `Hex.SignDet.Replay.table_count`

Decision: retain. Retain the actual recursive replay-to-count bridge, so finite-observation consumers need not reconstruct the support induction.

Uses the actual finite support induction to derive those hypotheses from accepted replay, well-formed observations and moment interpretation.

Assessment: [core-tables.md:51](../core-tables.md). Alias-merged named clients: 5.

## `Hex.SignDet.SelectedSigns.count`

Decision: retain. Retain the selected-word occurrence law under a lawful finite observation model; it remains usable before specializing to polynomial root semantics.

Accepted replay plus well-formed finite observations and moment interpretation gives exactly one occurrence of the full word. The interpretation hypotheses are essential.

Assessment: [core-selected.md:25](../core-selected.md). Alias-merged named clients: 0.

## `Hex.SignDet.SelectedSigns.readMemo_same`

Decision: retain. Retain the same-domain memo identity for callers reusing shared evidence, including exact refusal rather than only successful sign equality.

A memo already on the descriptor domain gives the original extraction result exactly, including refusal.

Assessment: [core-dag-support.md:69](../core-dag-support.md). Alias-merged named clients: 3.

## `Hex.SignDet.SelectedSigns.signs_eq`

Decision: retain. Retain the full vector/count consequence for finite observation models, keeping the companion's separate root-set interpretation out of the computational API.

Derives those complete counts from finite observation interpretation. The companion separately supplies root-set interpretation.

Assessment: [core-selected.md:27](../core-selected.md). Alias-merged named clients: 0.

## `Hex.SignDet.SelectedSigns.ternary`

Decision: retain. Retain the accepted-table coordinate invariant without adding semantic assumptions about the supplied sign function.

Table invariants force every additional coordinate to be a ternary code; this does not assume semantic correctness of the sign function.

Assessment: [core-selected.md:24](../core-selected.md). Alias-merged named clients: 1.

## `Hex.SignDet.SignTable.empty_count`

Decision: retain. Retain the terminating empty-table simp law for arbitrary query widths, so clients do not unfold sparse lookup to close the zero case.

The empty lookup equation is a terminating simp normalization for arbitrary conditions, including wrong widths.

Assessment: [core-tables.md:36](../core-tables.md). Alias-merged named clients: 0.

## `Hex.SignDet.System.counts_eq`

Decision: retain. Retain count recovery only after complete support and moment interpretation are supplied. Its public hypotheses make the missing-support pitfall visible.

Checked integer-system uniqueness recovers literal counts only after coverage and moment interpretation. The columns_nodup projection replaces checker unfolding without weakening either hypothesis.

Assessment: [core-replay.md:21](../core-replay.md). Alias-merged named clients: 2.

## `Hex.SignDet.System.covers_support`

Decision: retain. Retain the post-pruning support consequence as a composed interface; users should not have to reopen count recovery and pruning while preserving coverage hypotheses.

Combines count recovery and pruning while preserving checked-system, coverage and moment hypotheses. It does not infer coverage from invertibility.

Assessment: [core-replay.md:23](../core-replay.md). Alias-merged named clients: 0.

## `Hex.SignDet.System.mem_support`

Decision: retain. Retain membership from a positive coordinate of a separately justified solution. It does not let an inverse matrix stand in for actual-observation coverage.

Uses accepted-system uniqueness and a positive coordinate of another solution. The caller must establish actual-count equations on a complete candidate support separately.

Assessment: [core-foundation.md:41](../core-foundation.md). Alias-merged named clients: 0.

## `Hex.SignDet.System.unique`

Decision: retain. Retain the algebraic uniqueness theorem for checked scaled inverses, independently of the stronger semantic premises needed for actual observation counts.

A nonzero integer denominator permits cancellation after applying the supplied left inverse. Uniqueness does not imply that the candidate columns cover actual observations.

Assessment: [core-foundation.md:30](../core-foundation.md). Alias-merged named clients: 2.

## `Hex.SignDet.Thom.insert_nil`

Decision: retain. Retain the unconditional empty-insertion simp case used by literal replay, avoiding an unnecessary comparator or arithmetic premise.

Normalizes empty-list insertion to the singleton supplied descriptor, without a comparator or arithmetic premise; used by the literal replay consumer.

Assessment: [core-root-list.md:13](../core-root-list.md). Alias-merged named clients: 1.

## `Hex.SignDet.ValueCodec.Lawful.covers`

Decision: retain. Retain the bridge from a global codec law to finite coverage, so generic graph clients can reuse lawful codecs without rebuilding per-value facts.

A globally lawful codec supplies finite coverage; the converse is not claimed.

Assessment: [core-codec-coefficients.md:28](../core-codec-coefficients.md). Alias-merged named clients: 1.

## `Hex.SignDet.ValueCodec.nat`

Decision: retain. Retain the concrete natural literal codec as a usable public instance for graph clients and fixtures, with negative and wrong-kind rejection explicit.

Uses exact natural JSON scalar instances, rejecting other kinds and negative numbers.

Assessment: [core-serialization.md:11](../core-serialization.md). Alias-merged named clients: 69.

## `Hex.SignDet.ValueCodec.nat_lawful`

Decision: retain. Retain the global law for the actual natural codec, supplying the generic graph roundtrip interface rather than requiring repeated scalar proofs.

Provides global literal law for the actual natural value codec.

Assessment: [core-serialization.md:85](../core-serialization.md). Alias-merged named clients: 8.

## `Hex.SignDet.ValueCodec.rat`

Decision: retain. Retain the canonical rational-pair codec for exact graph clients; rejecting invalid denominators is part of its wire contract rather than silent normalization.

Encodes the canonical numerator/positive denominator pair and rejects zero or noncanonical denominators instead of normalizing untrusted pairs.

Assessment: [core-serialization.md:12](../core-serialization.md). Alias-merged named clients: 83.

## `Hex.SignDet.ValueCodec.rat_lawful`

Decision: retain. Retain the law for canonical rational pairs so graph clients can instantiate lawful transport without unfolding positive-denominator reconstruction.

Provides global literal law for canonical rational pairs using positive denominators and mkRat_self.

Assessment: [core-serialization.md:86](../core-serialization.md). Alias-merged named clients: 8.

## `Hex.SignDet.checkMoment_sign_congr`

Decision: retain. Retain the moment-check provider substitution law covering optional reductions and Tarski operands; neither component theorem alone preserves the complete checker.

Composes reduction and Tarski congruence without removing arithmetic or context checks, whether the optional reduction is present or absent.

Assessment: [core-foundation.md:61](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.count_moments`

Decision: retain. Retain the finite observation/count identity with complete coverage and distinct columns explicit; it is the algebraic bridge that prevents omitted-support errors.

Distinct candidate columns and complete coverage prevent double counting and omitted observations. Empty supports/observations remain valid; no root semantics is assumed.

Assessment: [core-replay.md:20](../core-replay.md). Alias-merged named clients: 1.

## `Hex.SignDet.momentSignOperands`

Decision: retain. Retain collection of both reduction scales and Tarski sign dependencies for the actual checked moment, separately from integer and query bindings.

Includes optional reduction scales and the actual shared Tarski certificate's operands. Integer moments and query bindings are separate checks.

Assessment: [core-foundation.md:60](../core-foundation.md). Alias-merged named clients: 3.

## `Hex.SignDet.reductionOperands`

Decision: retain. Retain occurrence-preserving collection across extra malformed steps, because rejection cannot justify omitting an operand from the congruence hypothesis.

Preserves all occurrences and includes extra malformed steps, so a rejected certificate cannot omit dependencies from the congruence hypothesis.

Assessment: [core-foundation.md:56](../core-foundation.md). Alias-merged named clients: 7.

## `Hex.SignDet.referencePrepared`

Decision: retain. Retain the independent full-ternary reference calculation used by Conformance.agrees and the SPEC-required reduced/full comparison. It is an intentional exponential reference API, never a production fallback.

Constructs the full ternary reference system with exactly ordered exponent/sign words. It remains an exponential small-case comparator, with the same `Except BuildError` contract and supplied prepared domain as the ordinary builder. Production recursion does not fall back to this operation.

Assessment: [core-foundation.md:49](../core-foundation.md). Alias-merged named clients: 8.

## `Hex.SignDet.words`

Decision: retain. Retain the ordered-word generator used by referencePrepared. Its purpose is the independently checked full reference system, including the singleton empty word and repeated-alphabet behavior.

Enumerates ordered words with the first coordinate varying slowest. The zero-length case is the singleton empty word; a repeated alphabet is not deduplicated.

Assessment: [core-foundation.md:48](../core-foundation.md). Alias-merged named clients: 7.
