# Common-polynomial comparison and re-encoding assessment

This assessment covers all 27 named declarations in three computational modules
and their sixteen source structure fields. It is partial core review; it does
not advance a phase counter or establish a computational regression result.

| Declaration | Assessment |
| --- | --- |
| `CommonProduct` | Seven fields retain both original heads, literal context, candidate common head and three division factors; no squarefreeness is encoded in the structure. |
| `CommonProduct.check` | Checks literal bindings and three zero-difference identities. Noncanonical coefficient representations are accepted through the existing zero test, without requiring literal equality of the products. |
| `CommonProduct.check_iff` | Characterizes the guard for an arbitrary record, in both directions; no gcd or producer provenance is assumed. |
| `CommonProduct.check_eq` | Preserves the existing forward interface and delegates to the full acceptance equivalence. |
| `CommonProduct.build` | Uses the existing gcd/division kernels, then independently checks the actual record. With unlawful coefficient operations, the recheck can return `.error .system`; producer success under lawful semantic hypotheses is a companion theorem. |
| `CommonProduct.build_of_check` | Identifies the actual constructed record when its check succeeds. It does not assume arbitrary common-product evidence is the producer output. |
| `RawDescriptor.constraints` | Keeps the original head, derivative queries and finite endpoint inequalities in order; no rational separator is introduced. |
| `RawDescriptor.constraintSigns` | Uses zero for the original equation, the stored derivative word, positive lower and negative upper endpoint signs, matching constraints in order. |
| `Descriptor.checkReencoding` | Authenticates target head and endpoints, complete joint replay, and a count-one word including every source constraint. |
| `Descriptor.checkReencoding_iff` | Provides both directions of that complete guard for arbitrary supplied evidence. Root semantics and target-domain validity remain separate companion conclusions. |
| `Reencoding` | Its three documented fields retain the validated target, exact joint evidence and acceptance proof. Arbitrary accepted re-encoding need not have full derivative indices. |
| `Reencoding.check_eq` | Derives named target bindings and a count-one accepted table through the forward guard and table lookup agreement. |
| `Reencoding.count` | Converts that count to an occurrence count only under finite observation well-formedness and replay interpretation; it does not infer root interpretation from table shape. |
| `Descriptor.buildReencoding` | Prepares the target domain, builds the joint table, filters by all old-root constraints, builds the target and rechecks it. Invalid domains or absent roots return none; internal invariant failures retain diagnostics. |
| `Descriptor.buildReencoding_ofNone` | Invalid actual preparation exits before table construction. |
| `Descriptor.buildReencoding_ofEmpty` | No matching row in the actual constructed joint table exits before descriptor construction. |
| `Descriptor.buildReencoding_ofTable` | Requires the actual preparation and replay equations, a unique matching row, actual successful target construction and acceptance; proves the executable success branch. |
| `Descriptor.buildReencoding_full` | Successful actual production gives canonical full indices; arbitrary accepted certificates do not inherit producer provenance. |
| `Comparison` | Six documented fields retain checked common identities, both original-root re-encodings and the actual comparator equation, rather than just two words. |
| `Descriptor.buildComparison` | Uses the whole-line common head and retains original intervals as query constraints, avoiding an endpoint collision between different heads. |
| `Descriptor.buildComparison_of_success` | Follows the actual common-head, two re-encoding and full-order branches, preserving dependent evidence and the returned order. |
| `Descriptor.buildOrder` | Literal equal heads use actual completions; unequal heads use checked common-product comparison. Literal equality is a sufficient shortcut, not semantic equality. |
| `Descriptor.buildOrder_ofCompletion` | Identifies the direct branch only under equal literal heads, actual successful completion equations and the actual full-order result. |
| `Descriptor.buildOrder_ofComparison` | Identifies the unequal-head branch using its actual successful comparison record. |
| `Descriptor.compare` | A total diagnostic wrapper returning the constructed order; its eq fallback is excluded only by lawful companion producer-success hypotheses. |
| `Descriptor.compare_ofBuild` | Successful actual construction identifies the total returned order, without claiming unconditional construction success. |
| `Descriptor.compare_ofError` | Pins the diagnostic fallback to eq even if the ambient Ordering inhabitant differs; this is an operational fact, not equality of the selected roots. |

## Proof clients and remaining obligations

The common-product producer proof uses the reverse acceptance equivalence.
The ordinary and partial-word re-encoding producer proofs use the corresponding
reverse joint guard. Existing common-product root soundness and re-encoding
counts use the forward interfaces. No executable definitions, guards or
certificate layouts change.

The seven `CommonProduct`, three `Reencoding` and six `Comparison` fields
have source documentation. Public imports remain the existing computational
and companion umbrellas. Tau Ceti stays in the companion.

The existing comparison and re-encoding conformance cases retain different
heads, old endpoint constraints, no matching root and invalid target domains.
They are reused rather than assigning new direct examples. The full producer
success and selected-root preservation proofs remain in the companion.
Other core modules, current whole-library reference assessment and the
specified Phase-6 computational checks remain outstanding.

The axiom checks expect only `propext` for `CommonProduct.check_iff` and
`propext`, `Classical.choice`, `Quot.sound` for
`Descriptor.checkReencoding_iff`. The import DAG, admission scan and reviewed
source bindings are checked locally. The binding checker verifies named source
inventory and exact file bytes; it does not establish field documentation,
mathematical correctness or whole-repository reference completeness.

`CommonProduct.check_eq` keeps the existing public forward interface used by
root-soundness clients. The new `_iff` name distinguishes the bidirectional
acceptance law without changing that interface. Other existing `_eq`
characterizations are outside this tranche's naming changes.

The source-bound checks here concern the SignDet assessment. The earlier
Sturm reference audit binds its archived source revision; it is not a fresh
usage attestation for later monorepo changes.
