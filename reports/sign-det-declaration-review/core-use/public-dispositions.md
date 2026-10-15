# SignDet core public API retention decisions

Manual public-API retention judgments for the 149 declarations without an alias-merged external-core production path at source `398f34c7f15ac4c7e9da1fff83ecbfc62eb69c72`. These adopt the existing per-declaration mathematical assessments. They do not claim named production clients, complete performance acceptance or a phase promotion. Generated constants and 98 fields remain distinct from these handwritten decisions.

## `Hex.SignDet.Codec.Decimal.readInt`

Decision: retain. Keep the actual literal parser/printer component for direct codec clients and its checked roundtrip/reference interface. Arithmetic authentication and whole-JSON acceptance remain separate where stated.

Runs actual UTF-8 validation before signed digit reading; it does not authenticate a coefficient or certificate.

Assessment: [core-parser.md:18](../core-parser.md). Alias-merged named clients: 2.

## `Hex.SignDet.Codec.Decimal.readIntText`

Decision: retain. Keep the actual literal parser/printer component for direct codec clients and its checked roundtrip/reference interface. Arithmetic authentication and whole-JSON acceptance remain separate where stated.

Permits an optional minus and nonempty digit word, rejecting plus/fraction/exponent syntax; JSON leading zeros remain a lexer obligation.

Assessment: [core-parser.md:17](../core-parser.md). Alias-merged named clients: 3.

## `Hex.SignDet.Codec.Decimal.readInt_repr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Actual signed integer decimal printer/reader preserves both Int constructors and arbitrary magnitudes.

Assessment: [core-parser.md:21](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Decimal.readInt_toString`

Decision: retain. Keep the specialization to the standard signed integer toString surface, rather than forcing byte-codec users to identify its representation with the underlying printer.

Standard toString specializes the same actual signed-integer byte roundtrip.

Assessment: [core-parser.md:22](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Decimal.readNat`

Decision: retain. Keep the actual literal parser/printer component for direct codec clients and its checked roundtrip/reference interface. Arithmetic authentication and whole-JSON acceptance remain separate where stated.

Validates whole UTF-8 input before the actual digit reader; not a complete JSON-number lexer.

Assessment: [core-parser.md:11](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Decimal.readNat_repr`

Decision: retain. Keep the direct natural-byte roundtrip surface; malformed integer grammar remains a separate lexer obligation.

Actual natural decimal byte printer/reader roundtrip, without a parser-success premise.

Assessment: [core-parser.md:16](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.Value.writeBytes_toList`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Exact ordinary-kernel equality exposes the actual UTF-8 byte list through structural token characters, with no performance claim.

Assessment: [core-parser.md:113](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.Values.toListLoop`

Decision: retain. Keep the replacement named by the proved csimp registration for public Values.toList. Its direct clients are the replacement theorem/equation; a production-path count does not capture compiler registration.

Actual list conversion through the native width loop and array representation.

Assessment: [core-serialization.md:113](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Json.Values.toList_impl`

Decision: retain. Keep the proved compiler-simplification registration. Its purpose is the native replacement of public Values.toList, so absence of a declaration-reference edge does not justify removal. No current internal C caller is claimed.

Proved csimp replacement preserves exact reference list semantics while changing only compiled width traversal.

Assessment: [core-serialization.md:114](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.of_array`

Decision: retain. Keep the representation law for the actual element dictionary and ordered array encoder. It avoids consumers unfolding the instance; it asserts no element-codec law.

The actual array instance maps the supplied element dictionary in literal order.

Assessment: [core-serialization.md:126](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.of_list`

Decision: retain. Keep the list instance representation law, including its ordered array conversion. It exposes a different public input type from of_array.

The actual list instance uses the same ordered array construction.

Assessment: [core-serialization.md:127](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.read_of_bool`

Decision: retain. Keep scalar dictionary roundtrip as a simp normalization for client expressions. A registration/anonymous use need not create a named term edge.

Actual Boolean scalar dictionaries roundtrip exactly; appropriate simp normalization.

Assessment: [core-serialization.md:128](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Json.read_of_string`

Decision: retain. Keep scalar dictionary roundtrip as a simp normalization for string client expressions. It certifies literal decoding, not arithmetic.

Actual string scalar dictionaries roundtrip exactly; appropriate simp normalization.

Assessment: [core-serialization.md:129](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.readBodyLoop_spec`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Public exact native/reference agreement covers malformed input and insufficient fuel, not just emitted strings.

Assessment: [core-parser.md:44](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.readBytes`

Decision: retain. Keep the actual literal parser/printer component for direct codec clients and its checked roundtrip/reference interface. Arithmetic authentication and whole-JSON acceptance remain separate where stated.

Requires valid whole UTF-8 and empty character suffix after the quoted prefix; trailing bytes reject.

Assessment: [core-parser.md:49](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Str.readBytes_write`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Every actual emitted Unicode string byte record reconstructs exactly, with no assumed parser-success or resource policy.

Assessment: [core-parser.md:50](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.scanLoop_spec`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Public exact zero-accumulator scan agreement; it makes no syntax-validation claim.

Assessment: [core-parser.md:45](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.Str.writeBytes`

Decision: retain. Keep the actual literal parser/printer component for direct codec clients and its checked roundtrip/reference interface. Arithmetic authentication and whole-JSON acceptance remain separate where stated.

Uses actual quoted escaping then UTF-8 encoding of the complete result.

Assessment: [core-parser.md:48](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Token.chars`

Decision: retain. Keep the actual literal parser/printer component for direct codec clients and its checked roundtrip/reference interface. Arithmetic authentication and whole-JSON acceptance remain separate where stated.

Structural character printer preserves literal token values without reparsing emitted integer text.

Assessment: [core-parser.md:56](../core-parser.md). Alias-merged named clients: 2.

## `Hex.SignDet.Codec.Token.emit_eq_chars`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Public exact equality of the two printers covers every token constructor; no byte allocation/timing conclusion follows.

Assessment: [core-parser.md:57](../core-parser.md). Alias-merged named clients: 1.

## `Hex.SignDet.Codec.Token.lexLoop_spec`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Public exact zero-prefix native/reference agreement applies to malformed streams and insufficient fuel.

Assessment: [core-parser.md:72](../core-parser.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.bindings_iff`

Decision: retain. Keep the exact context/head/endpoint acceptance criterion. The existing false-graph control uses it in an anonymous example, which this reference graph does not retain. Query and arithmetic replay obligations remain separate.

Exact decode-time context/head/endpoints criterion for node and every moment; query lists/polynomials and arithmetic acceptance remain replay obligations. Reused in the existing false-graph control.

Assessment: [core-serialization.md:75](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.decodeGraph`

Decision: retain. Keep this public graph operation and the associated explicit parse/replay or literal-transport boundary. Its source assessment gives the actual accepted data and rejection contract; pending automatic tower assembly is not part of this operation.

Runs actual lexical policy, UTF-8/JSON parsing and complete raw-graph reading; no arithmetic replay is claimed.

Assessment: [core-serialization.md:135](../core-serialization.md). Alias-merged named clients: 11.

## `Hex.SignDet.Codec.decodePair_error`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

An error in the first record returns exactly that error without evaluating the evidence parser or reader.

Assessment: [core-serialization.md:35](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.decodePair_ok`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Substitutes the actual two accepted parse results before applying the unchanged structured reader.

Assessment: [core-serialization.md:34](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.decode_graph`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Full graph byte roundtrip requires lawful codecs, structural/subject bounds and success of the exact encoded-byte resource check. Reuses the actual JSON/graph path; does not certify arithmetic.

Assessment: [core-graph-codec.md:22](../core-graph-codec.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.decode_graph_covered`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Composes exact byte parsing and graph reconstruction under success of the actual byte/resource check and finite stored-value coverage. Independent arithmetic replay can still reject.

Assessment: [core-graph-codec.md:37](../core-graph-codec.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.encoded_graph`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Byte decoding of the encoder yields the exact JSON graph unconditionally; no graph validity or parser-limit claim follows.

Assessment: [core-graph-codec.md:21](../core-graph-codec.md). Alias-merged named clients: 0.

## `Hex.SignDet.Codec.forIn_data`

Decision: retain. Keep the generic early-exit iteration correspondence as the public proof interface for byte guards. It gives no compiled allocation guarantee.

Proves the actual byte-array loop agrees with array iteration, including early exit; no compiled allocation claim follows from this equality.

Assessment: [core-serialization.md:29](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.bindDomain_isSome`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Characterizes success by those three exact equalities. Equality in a mathematical interpretation does not suffice.

Assessment: [core-dag.md:33](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.bindDomain_self`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Supplies the unchanged-domain success law without requiring callers to unfold proof transport.

Assessment: [core-dag.md:34](../core-dag.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.bindDomain_values`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Preserves all stored literal trees on acceptance and records rejection when any binding differs.

Assessment: [core-dag.md:35](../core-dag.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.changeOps_isSome`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Operation transport preserves exactly whether the optional memo is present.

Assessment: [core-dag-support.md:56](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.changeOps_nodes`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Every stored literal node survives transport, including nodes not selected by a root lookup.

Assessment: [core-dag-support.md:57](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.changeOps_values`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Complete literal replay values survive operation transport, in order and with both successful and absent memos covered.

Assessment: [core-dag-support.md:55](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.check_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Graph Boolean checking depends only on that complete finite operand inventory, including malformed and unreachable entries.

Assessment: [core-dag-support.md:63](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.children_mapNodes`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Both ordered child references remain literally unchanged.

Assessment: [core-dag-support.md:21](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeBytes`

Decision: retain. Keep this public graph operation and the associated explicit parse/replay or literal-transport boundary. Its source assessment gives the actual accepted data and rejection contract; pending automatic tower assembly is not part of this operation.

Actual parsing followed by independent replay returns a tree with erased checker acceptance; parse/refusal errors are not mathematical nonexistence.

Assessment: [core-serialization.md:137](../core-serialization.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dag.decodeBytes_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Finite sign agreement on every actual decoded graph operand preserves exact parse/replay errors and literal returned tree values.

Assessment: [core-serialization.md:141](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeDescriptor`

Decision: retain. Keep this public graph operation and the associated explicit parse/replay or literal-transport boundary. Its source assessment gives the actual accepted data and rejection contract; pending automatic tower assembly is not part of this operation.

Replays against the complete supplied raw descriptor, deriving derivative queries from actual head/indices; serialized count-one assertions are not trusted.

Assessment: [core-serialization.md:138](../core-serialization.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dag.decodeDescriptor_raw`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Every accepted descriptor byte read retains all original raw fields, including derivative indices and signs.

Assessment: [core-serialization.md:144](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeDescriptor_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Finite stored-operand agreement preserves raw selected-root identity and supplied evidence, including exact refusal errors.

Assessment: [core-serialization.md:143](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeSigns`

Decision: retain. Keep this public graph operation and the associated explicit parse/replay or literal-transport boundary. Its source assessment gives the actual accepted data and rejection contract; pending automatic tower assembly is not part of this operation.

Checks exactly the caller sign vector using supplied joint graph evidence; no selected-sign producer fills missing evidence.

Assessment: [core-serialization.md:139](../core-serialization.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dag.decodeSigns_evidence`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Arbitrary accepted bytes identify the actual parsed graph, exact selected evidence and unchanged claimed signs, with no printer-success assumption.

Assessment: [core-serialization.md:140](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decodeSigns_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Finite stored-operand agreement and equal raw descriptor identity preserve exact errors, sign vector and literal evidence; validated proofs may differ.

Assessment: [core-serialization.md:142](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.decode_replays`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Arbitrary accepted bytes identify the exact parsed graph and actual replay result; no encoder or global codec law premise.

Assessment: [core-serialization.md:145](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.descriptor_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Finite sign agreement preserves exact raw descriptor/evidence data or rejection; context, head and endpoints remain literal inputs.

Assessment: [core-dag-support.md:64](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.encodeBytes`

Decision: retain. Keep this public graph operation and the associated explicit parse/replay or literal-transport boundary. Its source assessment gives the actual accepted data and rejection contract; pending automatic tower assembly is not part of this operation.

Prints all literal graph fields without running a producer or validating mathematical evidence.

Assessment: [core-serialization.md:136](../core-serialization.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dag.encode_leaf`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Actual encoding of a single leaf produces that literal node at index zero with no children. The empty-map proof needs no lawful-hash hypothesis or native hash-table evaluation. It establishes no replay acceptance.

Assessment: [core-codec-coefficients.md:29](../core-codec-coefficients.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.mapNodes`

Decision: retain. Keep this public graph operation and the associated explicit parse/replay or literal-transport boundary. Its source assessment gives the actual accepted data and rejection contract; pending automatic tower assembly is not part of this operation.

Transforms each stored node once and retains all indices, edges and the selected root across carrier/context types. It transports no arithmetic acceptance.

Assessment: [core-dag-support.md:18](../core-dag-support.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dag.node_mapNodes`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Retrieves exactly the transformed original node at a valid original index.

Assessment: [core-dag-support.md:20](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.replay_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Agreement on all stored sign operands preserves the exact optional returned tree without recursively rechecking an expanded tree.

Assessment: [core-dag-support.md:62](../core-dag-support.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dag.root_mapNodes`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Root index is unchanged even for malformed raw graphs.

Assessment: [core-dag-support.md:22](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.select_isSome`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Characterizes arbitrary memo selection in both directions: an existing index and exact query binding. No producer provenance or root semantics are assumed.

Assessment: [core-dag.md:31](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.select_values`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Identifies the exact returned tree at a matching stored entry and gives no tree for either rejection branch. It applies to any supplied checked memo.

Assessment: [core-dag.md:30](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_checked`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Successful graph extraction passes the independent descriptor tree checker for the original supplied query list and vector.

Assessment: [core-dag-support.md:74](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_encode`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Encoding existing accepted selected-sign evidence preserves acceptance and the exact literal evidence tree.

Assessment: [core-dag-support.md:76](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_encode_eq`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Encoding any supplied tree preserves both selected-sign acceptance and rejection, including malformed query/matrix evidence or a wrong vector.

Assessment: [core-dag-support.md:77](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_memo`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Selecting from an actually validated memo equals graph selected-sign checking, including refusal and complete returned evidence.

Assessment: [core-dag-support.md:72](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_replay`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

After actual graph replay succeeds, selected-sign presence equals the original tree checker on the exact claimed vector.

Assessment: [core-dag-support.md:75](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.selectedSigns_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Finite stored-node sign agreement and equal raw descriptor identity preserve the optional sign/evidence data. Descriptor proof fields and source replays may differ.

Assessment: [core-dag-support.md:78](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.signOperands`

Decision: retain. Keep the executable complete stored-operand inventory used by finite sign-congruence contracts. Retaining malformed, repeated and unreachable entries is essential to those hypotheses; this operation does not construct coefficient evidence.

Collects local-node sign dependencies from every stored entry, including unreachable entries; it is not just a selected-root inventory.

Assessment: [core-dag-support.md:58](../core-dag-support.md). Alias-merged named clients: 7.

## `Hex.SignDet.Dag.size_mapNodes`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Preserves array length, including unreachable entries.

Assessment: [core-dag-support.md:19](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.step_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Finite local sign agreement and equal literal memo values preserve the optional step value across sign indices, including rejection.

Assessment: [core-dag-support.md:59](../core-dag-support.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dag.validate_get`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Connects two successful indexed lookups to the same literal node, retaining both lookup hypotheses.

Assessment: [core-dag.md:27](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.validate_root`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Changing only the selected root leaves validation unchanged. A root index is checked at selection.

Assessment: [core-dag.md:28](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dag.validate_size`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Characterizes the memo length after success; delegates to exact node correspondence.

Assessment: [core-dag.md:26](../core-dag.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Checked`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Retains a literal packet and a result of the caller-supplied dependent type. Mathematical acceptance depends on what that type and reader actually establish.

Assessment: [core-dependencies.md:20](../core-dependencies.md). Alias-merged named clients: 18.

## `Hex.SignDet.Dependencies.Decoded`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Stores the graph, typed memo and proofs of ordered requested bindings, structural validity and exact entry retention. It records no parse or reader-acceptance provenance; mathematical facts must be carried by the caller's result type.

Assessment: [core-dependencies.md:38](../core-dependencies.md). Alias-merged named clients: 11.

## `Hex.SignDet.Dependencies.Decoded.memo_size`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Literal memo-entry equality gives exactly one position per stored packet, including unused packets; existing selection proofs reuse the length law.

Assessment: [core-dependencies.md:39](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Decoded.results`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Selects stored memo values in root order using proved structural bounds and exact memo-entry equality; repeated roots reuse values and cannot fail.

Assessment: [core-dependencies.md:40](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Decoded.results_bound`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Selected memo results have precisely the requested ordered levels and full literal subjects.

Assessment: [core-dependencies.md:41](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Decoded.results_size`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Selected result count equals the requested binding count, including empty and repeated roots.

Assessment: [core-dependencies.md:42](../core-dependencies.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Entry`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Stores level, subject, payload and ordered child references. Its type alone enforces no acyclicity, lower level or arithmetic validity.

Assessment: [core-dependencies.md:15](../core-dependencies.md). Alias-merged named clients: 42.

## `Hex.SignDet.Dependencies.Entry.codec`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Retains level, subject, payload and ordered children literally; parsing supplies raw packets without acceptance.

Assessment: [core-dependencies.md:33](../core-dependencies.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dependencies.Entry.codec_lawful`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Literal packet tuple roundtrip uses the reference codec law for every child, with no graph premise.

Assessment: [core-dependencies.md:34](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Stores entries and ordered roots, including shared and unreachable packets; validity is separate.

Assessment: [core-dependencies.md:16](../core-dependencies.md). Alias-merged named clients: 17.

## `Hex.SignDet.Dependencies.Graph.check`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Checks every root and every stored child. Child indices point backward and levels strictly decrease; unreachable packets remain checked.

Assessment: [core-dependencies.md:19](../core-dependencies.md). Alias-merged named clients: 7.

## `Hex.SignDet.Dependencies.Graph.check_children`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Extracts all backward-index, lower-level and literal-reference conditions for every declared child of every stored entry.

Assessment: [core-dependencies.md:25](../core-dependencies.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Graph.check_roots`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Extracts index existence and exact level/subject binding for each declared result; repeated roots are allowed.

Assessment: [core-dependencies.md:26](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Graph.codec`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Version-one tuple retains all entries and roots in wire order; unsupported version and malformed tuples reject independently of arithmetic.

Assessment: [core-dependencies.md:35](../core-dependencies.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dependencies.Graph.codec_bytes`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Actual byte parser reconstructs the whole literal graph from printer output under the lexical/resource precheck, without assuming parser success or arithmetic validity.

Assessment: [core-dependencies.md:37](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph.codec_lawful`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Literal envelope print/read roundtrip for arbitrary raw graphs, including structurally invalid ones.

Assessment: [core-dependencies.md:36](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph.decode`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Parses actual bytes, compares complete ordered caller bindings before any local reader, then validates all packets and stores actual accepted memo. No missing evidence is produced.

Assessment: [core-dependencies.md:43](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Dependencies.Graph.decode_encode`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Composes actual printer/parser with the supplied accepted reader result; returns exactly that memo under only the byte precheck and actual validation premise.

Assessment: [core-dependencies.md:44](../core-dependencies.md). Alias-merged named clients: 0.

## `Hex.SignDet.Dependencies.Graph.validate?`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Rejects structural failures before folding all packets through the actual reader from an empty memo; does not prove the reader sound.

Assessment: [core-dependencies.md:23](../core-dependencies.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dependencies.Graph.validate_check`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Accepted typed validation implies its prior structural guard; no semantic reader soundness is inferred.

Assessment: [core-dependencies.md:30](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Graph.validate_entries`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Actual accepted validation returns exactly the full literal entry array, including payloads, children and unreachable entries.

Assessment: [core-dependencies.md:29](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Reference`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Stores index, coefficient level and complete literal JSON subject; equality is not reduced to a context hash.

Assessment: [core-dependencies.md:14](../core-dependencies.md). Alias-merged named clients: 32.

## `Hex.SignDet.Dependencies.Reference.check`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Checks index existence and exact level/subject binding against the literal referenced entry.

Assessment: [core-dependencies.md:18](../core-dependencies.md). Alias-merged named clients: 4.

## `Hex.SignDet.Dependencies.Reference.check_eq`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Bidirectional success criterion gives the exact existing index, level and complete subject; no semantic premise is hidden.

Assessment: [core-dependencies.md:24](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Reference.codec`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Integer-only JSON tuple retains index, level and complete literal subject; decoder performs syntax/type checks rather than graph validity.

Assessment: [core-dependencies.md:31](../core-dependencies.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dependencies.Reference.codec_lawful`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Literal tuple print/read roundtrip for every reference, including invalid indices.

Assessment: [core-dependencies.md:32](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.Reference.matches`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Tests exact level and subject equality, without checking the referenced index or interpreting either packet.

Assessment: [core-dependencies.md:17](../core-dependencies.md). Alias-merged named clients: 3.

## `Hex.SignDet.Dependencies.children?`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Reads declared children from the supplied memo in order, requires exact subject/level matching and a lower level; missing or stale references reject before local reading.

Assessment: [core-dependencies.md:21](../core-dependencies.md). Alias-merged named clients: 2.

## `Hex.SignDet.Dependencies.step`

Decision: retain. Keep this part of the public typed dependency-envelope interface. Raw packets, structural validation, caller-supplied local reading and returned bindings are deliberately separate; active tower/tactic assembly does not change this generic contract or supply the missing reader facts.

Invokes the supplied reader only after child lookup succeeds, and retains its exact dependent result with the supplied entry. Coverage is still the local reader contract.

Assessment: [core-dependencies.md:22](../core-dependencies.md). Alias-merged named clients: 5.

## `Hex.SignDet.Dependencies.step_entry`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Accepted local reading returns the exact supplied packet, for any caller-supplied Type-valued result.

Assessment: [core-dependencies.md:27](../core-dependencies.md). Alias-merged named clients: 1.

## `Hex.SignDet.Descriptor.buildRoots_constant`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

A successful constant-head result is empty by the positive-degree shape requirement on every possible descriptor; this alone does not claim all constant inputs prepare successfully.

Assessment: [core-root-list.md:39](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.buildRoots_perm`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Successful public output preserves every full word of the actual produced table, including the constant/empty case.

Assessment: [core-root-list.md:40](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.buildRoots_raw`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

All returned descriptors retain the requested subject and full indices, including singleton lists.

Assessment: [core-root-list.md:38](../core-root-list.md). Alias-merged named clients: 1.

## `Hex.SignDet.Descriptor.buildRoots_sorted`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Successful output is strictly pairwise ordered by the actual comparator; companion root-order interpretation remains explicit.

Assessment: [core-root-list.md:41](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.build_domain`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Exact failed preparation yields the domain diagnostic when context agrees; an unrelated prepared object cannot discharge it.

Assessment: [core-descriptors.md:65](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.build_malformed`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

With exact successful preparation and matching context, a rejected shape yields the malformed diagnostic. The diagnostic order is preserved.

Assessment: [core-descriptors.md:66](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.changeOps_evidence`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

The entire replay is literally preserved; no checker or arithmetic producer is rerun.

Assessment: [core-handles.md:32](../core-handles.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.compare_ofError`

Decision: retain. Keep the characterization of the diagnostic fallback, so callers cannot confuse its operational eq with equality of selected roots.

Pins the diagnostic fallback to eq even if the ambient Ordering inhabitant differs; this is an operational fact, not equality of the selected roots.

Assessment: [core-comparison.md:35](../core-comparison.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.ofChecked_evidence`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Simp projection preserves literal replay, rather than reconstructing another certificate.

Assessment: [core-descriptors.md:45](../core-descriptors.md). Alias-merged named clients: 1.

## `Hex.SignDet.Descriptor.ofTable_evidence`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Exact replay projection from table reuse, with the same dependent acceptance proof.

Assessment: [core-descriptors.md:51](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.prepareQueries_isSome`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Characterizes handle existence by actual preparation success, in both directions, without running selected-query production.

Assessment: [core-handles.md:19](../core-handles.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFromTable_perm`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Transfers exact supplied-word preservation through the proved shared/reference-path agreement.

Assessment: [core-root-list.md:30](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFromTable_sorted`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Transfers strict finite order through that same agreement.

Assessment: [core-root-list.md:31](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFrom_counts`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Arbitrary successful extraction implies count one for every supplied row. The proof follows each count guard and actual recursive result; no producer provenance is assumed.

Assessment: [core-root-list.md:27](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.rootsFrom_length`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Derives exact output length from the existing permutation law, without unfolding recursion downstream. This is an assembly count, not a theorem about polynomial multiplicity.

Assessment: [core-root-list.md:26](../core-root-list.md). Alias-merged named clients: 0.

## `Hex.SignDet.Descriptor.signAt_ternary`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Successful values are ternary by table invariants. Lean's diagnostic default branch is also zero; this representation fact alone gives no selected-root semantics.

Assessment: [core-selected.md:35](../core-selected.md). Alias-merged named clients: 0.

## `Hex.SignDet.Node.check_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Preserves the actual node result for arbitrary matrices and witnesses. Rank, support and literal guards are unaffected by changing the sign provider.

Assessment: [core-foundation.md:63](../core-foundation.md). Alias-merged named clients: 2.

## `Hex.SignDet.Node.signOperands`

Decision: retain. Keep the executable complete stored-operand inventory used by finite sign-congruence contracts. Retaining malformed, repeated and unreachable entries is essential to those hypotheses; this operation does not construct coefficient evidence.

Includes preparation and every indexed moment/reduction. A native domain cache does not shrink the hypotheses of full replay.

Assessment: [core-foundation.md:62](../core-foundation.md). Alias-merged named clients: 10.

## `Hex.SignDet.QueryHandle.checkSigns`

Decision: retain. Keep the arbitrary supplied-evidence replay entry point on a prepared query handle. A cached domain does not replace descriptor checking or turn this operation into an evidence producer.

Checks arbitrary supplied evidence against the original validated descriptor; stored domain data do not replace that checker.

Assessment: [core-handles.md:25](../core-handles.md). Alias-merged named clients: 1.

## `Hex.SignDet.QueryHandle.checkSigns_eq`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Exposes the exact checker identity for any handle and supplied query/vector/replay, without semantic or producer premises.

Assessment: [core-handles.md:26](../core-handles.md). Alias-merged named clients: 0.

## `Hex.SignDet.QueryReduction.checkFrom_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Preserves query order and index progression; the empty and mismatched cases remain part of the theorem.

Assessment: [core-foundation.md:59](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.RawDescriptor.check_count`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

With explicit valid observations and replay interpretation, the exact finite observation list contains the selected word once. Repeated observations count separately; ordinary-root distinctness is a companion requirement.

Assessment: [core-descriptors.md:58](../core-descriptors.md). Alias-merged named clients: 0.

## `Hex.SignDet.Reduction.checkFrom_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Induction covers missing and extra factors/steps as well as accepted chains. It transports checker results, not just successful producer outputs.

Assessment: [core-foundation.md:58](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.ReductionStep.check_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Agreement on both scales preserves the actual step checker; polynomial identities and literal bindings remain checked.

Assessment: [core-foundation.md:57](../core-foundation.md). Alias-merged named clients: 2.

## `Hex.SignDet.ReductionStep.signOperands`

Decision: retain. Keep the executable complete stored-operand inventory used by finite sign-congruence contracts. Retaining malformed, repeated and unreachable entries is essential to those hypotheses; this operation does not construct coefficient evidence.

Includes both supplied scales, regardless of eventual acceptance or use.

Assessment: [core-foundation.md:55](../core-foundation.md). Alias-merged named clients: 4.

## `Hex.SignDet.Reencoding.count`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Converts that count to an occurrence count only under finite observation well-formedness and replay interpretation; it does not infer root interpretation from table shape.

Assessment: [core-comparison.md:21](../core-comparison.md). Alias-merged named clients: 0.

## `Hex.SignDet.Replay.check_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Structural induction preserves both child restrictions, their support-completeness checks and all rejection paths. It neither constructs coefficient evidence nor proves a joint field realization.

Assessment: [core-foundation.md:65](../core-foundation.md). Alias-merged named clients: 6.

## `Hex.SignDet.Replay.signOperands`

Decision: retain. Keep the executable complete stored-operand inventory used by finite sign-congruence contracts. Retaining malformed, repeated and unreachable entries is essential to those hypotheses; this operation does not construct coefficient evidence.

Traverses the literal tree, preserving repeated subtrees and values as occurrences. Evidence sharing across coefficient-field levels belongs to another API.

Assessment: [core-foundation.md:64](../core-foundation.md). Alias-merged named clients: 5.

## `Hex.SignDet.Replay.support_complete`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Specializes the same induction to the computational count-recovery proof; semantic consumers separately derive its moment interpretation.

Assessment: [core-tables.md:26](../core-tables.md). Alias-merged named clients: 2.

## `Hex.SignDet.Replay.support_iff`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Combines coverage and absence of spurious positive columns to characterize support exactly. Repeated observations affect counts, not membership.

Assessment: [core-tables.md:27](../core-tables.md). Alias-merged named clients: 0.

## `Hex.SignDet.Replay.table_count`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Uses the actual finite support induction to derive those hypotheses from accepted replay, well-formed observations and moment interpretation.

Assessment: [core-tables.md:51](../core-tables.md). Alias-merged named clients: 5.

## `Hex.SignDet.SelectedSigns.count`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Accepted replay plus well-formed finite observations and moment interpretation gives exactly one occurrence of the full word. The interpretation hypotheses are essential.

Assessment: [core-selected.md:25](../core-selected.md). Alias-merged named clients: 0.

## `Hex.SignDet.SelectedSigns.readMemo_same`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

A memo already on the descriptor domain gives the original extraction result exactly, including refusal.

Assessment: [core-dag-support.md:69](../core-dag-support.md). Alias-merged named clients: 0.

## `Hex.SignDet.SelectedSigns.signs_eq`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Derives those complete counts from finite observation interpretation. The companion separately supplies root-set interpretation.

Assessment: [core-selected.md:27](../core-selected.md). Alias-merged named clients: 0.

## `Hex.SignDet.SelectedSigns.ternary`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Table invariants force every additional coordinate to be a ternary code; this does not assume semantic correctness of the sign function.

Assessment: [core-selected.md:24](../core-selected.md). Alias-merged named clients: 1.

## `Hex.SignDet.SignTable.empty_count`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

The empty lookup equation is a terminating simp normalization for arbitrary conditions, including wrong widths.

Assessment: [core-tables.md:36](../core-tables.md). Alias-merged named clients: 0.

## `Hex.SignDet.System.counts_eq`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Checked integer-system uniqueness recovers literal counts only after coverage and moment interpretation. The columns_nodup projection replaces checker unfolding without weakening either hypothesis.

Assessment: [core-replay.md:21](../core-replay.md). Alias-merged named clients: 2.

## `Hex.SignDet.System.covers_support`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Combines count recovery and pruning while preserving checked-system, coverage and moment hypotheses. It does not infer coverage from invertibility.

Assessment: [core-replay.md:23](../core-replay.md). Alias-merged named clients: 0.

## `Hex.SignDet.System.mem_support`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Uses accepted-system uniqueness and a positive coordinate of another solution. The caller must establish actual-count equations on a complete candidate support separately.

Assessment: [core-foundation.md:41](../core-foundation.md). Alias-merged named clients: 0.

## `Hex.SignDet.System.unique`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

A nonzero integer denominator permits cancellation after applying the supplied left inverse. Uniqueness does not imply that the candidate columns cover actual observations.

Assessment: [core-foundation.md:30](../core-foundation.md). Alias-merged named clients: 2.

## `Hex.SignDet.Thom.insert_nil`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Normalizes empty-list insertion to the singleton supplied descriptor, without a comparator or arithmetic premise; used by the literal replay consumer.

Assessment: [core-root-list.md:13](../core-root-list.md). Alias-merged named clients: 1.

## `Hex.SignDet.ValueCodec.Lawful.covers`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

A globally lawful codec supplies finite coverage; the converse is not claimed.

Assessment: [core-codec-coefficients.md:28](../core-codec-coefficients.md). Alias-merged named clients: 0.

## `Hex.SignDet.ValueCodec.nat`

Decision: retain. Keep the concrete installable literal codec and its independent roundtrip law as a public starting point for graph clients. Finite coverage of other carriers remains a separate contract.

Uses exact natural JSON scalar instances, rejecting other kinds and negative numbers.

Assessment: [core-serialization.md:11](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.ValueCodec.nat_lawful`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Provides global literal law for the actual natural value codec.

Assessment: [core-serialization.md:85](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.ValueCodec.rat`

Decision: retain. Keep the concrete installable literal codec and its independent roundtrip law as a public starting point for graph clients. Finite coverage of other carriers remains a separate contract.

Encodes the canonical numerator/positive denominator pair and rejects zero or noncanonical denominators instead of normalizing untrusted pairs.

Assessment: [core-serialization.md:12](../core-serialization.md). Alias-merged named clients: 1.

## `Hex.SignDet.ValueCodec.rat_lawful`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Provides global literal law for canonical rational pairs using positive denominators and mkRat_self.

Assessment: [core-serialization.md:86](../core-serialization.md). Alias-merged named clients: 0.

## `Hex.SignDet.checkMoment_sign_congr`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Composes reduction and Tarski congruence without removing arithmetic or context checks, whether the optional reduction is present or absent.

Assessment: [core-foundation.md:61](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.count_moments`

Decision: retain. Keep the public characterization with exactly the hypotheses described in the individual assessment below. It lets callers use the stated acceptance, refusal, transport or data law without unfolding the executable representation; no current external production client is claimed.

Distinct candidate columns and complete coverage prevent double counting and omitted observations. Empty supports/observations remain valid; no root semantics is assumed.

Assessment: [core-replay.md:20](../core-replay.md). Alias-merged named clients: 1.

## `Hex.SignDet.momentSignOperands`

Decision: retain. Keep the executable complete stored-operand inventory used by finite sign-congruence contracts. Retaining malformed, repeated and unreachable entries is essential to those hypotheses; this operation does not construct coefficient evidence.

Includes optional reduction scales and the actual shared Tarski certificate's operands. Integer moments and query bindings are separate checks.

Assessment: [core-foundation.md:60](../core-foundation.md). Alias-merged named clients: 3.

## `Hex.SignDet.reductionOperands`

Decision: retain. Keep the executable complete stored-operand inventory used by finite sign-congruence contracts. Retaining malformed, repeated and unreachable entries is essential to those hypotheses; this operation does not construct coefficient evidence.

Preserves all occurrences and includes extra malformed steps, so a rejected certificate cannot omit dependencies from the congruence hypothesis.

Assessment: [core-foundation.md:56](../core-foundation.md). Alias-merged named clients: 7.

## `Hex.SignDet.referencePrepared`

Decision: retain. Keep the independent full-ternary reference builder used by Conformance.agrees and the SPEC-required reduced/full comparison. It is an intentional exponential reference API, not a production fallback.

Constructs the full ternary reference system with exactly ordered exponent/sign words. It remains an exponential small-case comparator, with the same `Except BuildError` contract and supplied prepared domain as the ordinary builder. Production recursion does not fall back to this operation.

Assessment: [core-foundation.md:49](../core-foundation.md). Alias-merged named clients: 1.

## `Hex.SignDet.words`

Decision: retain. Keep the ordered-word generator used by referencePrepared. Its purpose is the independently checked full reference system; no production fallback or complexity improvement is claimed.

Enumerates ordered words with the first coordinate varying slowest. The zero-length case is the singleton empty word; a repeated alphabet is not deduplicated.

Assessment: [core-foundation.md:48](../core-foundation.md). Alias-merged named clients: 1.
