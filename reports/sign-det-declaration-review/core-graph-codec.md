# Graph codec proof assessment

This assessment covers the 30 named declarations and six `Shape` fields
in `GraphLaws`, `FiniteLaws` and `FiniteGraph`. It concerns literal reconstruction and
parser bounds. Arithmetic replay, root semantics and producer totality are
separate obligations. Lawful scalar/context codecs are explicit premises.

| Declaration | Assessment |
| --- | --- |
| `Codec.Shape` | Records row/column arity, two rank bounds and reduction/preparation index bounds. It proves no arithmetic identity or support completeness. |
| `Codec.Shape.read_node` | Reuses the node roundtrip theorem with every required structural bound and both codec laws. |
| `Codec.query_indices` | Private induction follows the checked query reduction list and the running input index. Every accepted step index is below the original index plus query length. |
| `Codec.factor_indices` | Private factor-list bound follows the actual zip/replicate construction, including differing exponent/query lengths. It asserts no product identity. |
| `Codec.reduction_indices` | Private induction follows checked factor reduction steps and transfers the supplied factor-index bounds to every accepted step. |
| `Codec.Shape.of_check` | Accepted node checks give all six parser bounds, using literal query bindings, positive-column rank equality, preparation length and the actual checked moment reductions. No semantic model is needed. |
| `Codec.bindings_of_check` | Accepted local node checking supplies exact context, head and endpoint binding for that node and every retained moment. Uses the public binding characterization rather than unfolding the reader implementation; no mathematical interpretation or producer provenance is assumed. |
| `Codec.bindings_of_validate` | Lifts exact local binding to every stored entry using the validated memo/node equality, including entries outside the selected root's reachable subgraph. Unifies the two former reader proofs and preserves the distinction between literal binding and semantic evidence. |
| `Codec.Shape.of_validate` | Successful graph validation supplies shape for every entry, including unreachable entries; uses exact validated memo/node correspondence. |
| `Codec.read_children` | Preserves ordered left/right references under strict earlier-index bounds. Does not check child query semantics. |
| `Codec.read_entry` | Reconstructs the complete literal node and both child references from lawful codecs, shape, exact subject bindings and earlier-index bounds. |
| `Codec.read_entries` | The actual left fold reconstructs all entries in order; its induction preserves prefix sizes and checks unreachable entries too. |
| `Codec.read_graph` | Preserves all literal fields with an in-bounds selected root, shapes, bindings and earlier-child bounds. False arithmetic evidence may still roundtrip. |
| `Codec.encoded_graph` | Byte decoding of the encoder yields the exact JSON graph unconditionally; no graph validity or parser-limit claim follows. |
| `Codec.decode_graph` | Full graph byte roundtrip requires lawful codecs, structural/subject bounds and success of the exact encoded-byte resource check. Reuses the actual JSON/graph path; does not certify arithmetic. |
| `Codec.read_poly_covered` | Requires coverage of each stored polynomial coefficient; preserves the canonical polynomial read by the existing decoder. |
| `Codec.read_endpoint_covered` | Finite endpoints need their stored value covered; infinite endpoints contain no coefficient to cover. |
| `Codec.read_remainder_covered` | Covers both witness scales and the quotient; reconstruction does not establish the asserted division identity. |
| `Codec.read_terminal_covered` | Preserves the terminal scale and polynomial with their exact finite coverage. |
| `Codec.read_chain_covered` | Preserves all chain polynomials, degree metadata, initial witness, subsequent steps and the optional terminal record. It proves no signed-remainder-chain identity. |
| `Codec.read_tarski_covered` | Reconstructs all twelve literal fields with coefficient coverage and the actual context roundtrip; root-query validity remains independent. |
| `Codec.read_step_covered` | Requires stored next/witness coefficients and an index strictly below parser arity; finite coefficient coverage alone does not discharge the index check. |
| `Codec.read_reduction_covered` | Reconstructs the ordered steps and final result with coverage and an arity bound for every step. |
| `Codec.read_preparation_covered` | Reconstructs the actual query-preparation list with coefficient coverage and each step's parser index bound. |
| `Codec.nodeContexts` | Enumerates the node context then all moment contexts in wire order. It does not claim those contexts coincide. |
| `Codec.read_node_covered` | Uses only finite stored-coefficient/context coverage and all six shape fields; arbitrary false arithmetic witnesses can still roundtrip. |
| `Codec.graphContexts` | Includes every node and moment context in stored entry order, including unreachable entries. |
| `Codec.read_entries_covered` | Private induction follows the actual left fold and prefix sizes, checking finite coverage, subject binding, shape and earlier-only children for every entry. |
| `Codec.read_graph_covered` | Reconstructs the entire literal graph from finite coverage, a valid selected index, every node's shape/bindings and ordered child bounds. It does not assume globally complete readers. |
| `Codec.decode_graph_covered` | Composes exact byte parsing and graph reconstruction under success of the actual byte/resource check and finite stored-value coverage. Independent arithmetic replay can still reject. |

The six shape fields track the exact parser bounds: `rows`, `columns`,
`rankRows`, `rankCols`, `reductions` and `preparation`. Each is individually
documented. Names are short within `Hex.SignDet.Codec`. Existing guards for
`Shape.of_validate`, `decode_graph` and `decode_graph_covered` permit only
`propext`, `Classical.choice` and `Quot.sound`. This is partial source review,
not whole-library phase acceptance or performance evidence.
