# Literal graph and memo API assessment

This assessment covers the 28 named declarations in `HexSignDet/Dag.lean`,
its equality instance and six structure fields. It is partial computational
core review; it does not advance a phase counter or establish a performance
regression result. Arithmetic interpretation and producer completeness remain
separate companion obligations.

| Declaration | Assessment |
| --- | --- |
| `Entry` | Retains the exact node and optional child indices. The structure alone permits invalid indices; validation checks them against the accepted prefix. |
| `Dag` | Retains every entry and a selected index. Validation examines unreachable entries as well; selection checks the root separately. |
| `Checked` | Stores a literal replay tree and its acceptance proof for the fixed sign function, context, head and endpoints. Its own ordered queries determine the acceptance index. |
| `step` | Checks leaf shape or two existing children, the exact query split, product rows/columns and the local node. Returns checked tree evidence without recursively rechecking accepted children. |
| `step_eq` | Characterizes the actual step, preserving the full dependent return value and every rejection while eliminating the optional domain cache. |
| `step_cache` | A supplied checked domain cannot change the step result; this follows from the local node cache theorem rather than assuming cache identity. |
| `step_node` | Identifies the exact stored node on successful execution, including both child branches and missing-index rejection. |
| `fold_nodes` | Private induction used by `validate_nodes`; proves that successful folding appends precisely the supplied nodes to the initial memo. |
| `cache` | Uses the first entry's first moment only after literal context/head/endpoint bindings and domain replay. Cache failure falls back to ordinary checking rather than certifying the graph. |
| `validate?` | Folds all entries from an empty memo, which excludes forward references and cycles. It intentionally does not require a valid selected root. |
| `validate_nodes` | Successful validation identifies every memo node with its serialized entry, including unreachable entries. |
| `validate_size` | Characterizes the memo length after success; delegates to exact node correspondence. |
| `validate_get` | Connects two successful indexed lookups to the same literal node, retaining both lookup hypotheses. |
| `validate_root` | Changing only the selected root leaves validation unchanged. A root index is checked at selection. |
| `select?` | Reuses an accepted tree only after a successful lookup and exact equality of ordered queries; performs no arithmetic replay. |
| `select_values` | Identifies the exact returned tree at a matching stored entry and gives no tree for either rejection branch. It applies to any supplied checked memo. |
| `select_isSome` | Characterizes arbitrary memo selection in both directions: an existing index and exact query binding. No producer provenance or root semantics are assumed. |
| `bindDomain?` | Transports the dependent memo only after literal equality of the head and both endpoints. The sign function and context remain fixed. |
| `bindDomain_isSome` | Characterizes success by those three exact equalities. Equality in a mathematical interpretation does not suffice. |
| `bindDomain_self` | Supplies the unchanged-domain success law without requiring callers to unfold proof transport. |
| `bindDomain_values` | Preserves all stored literal trees on acceptance and records rejection when any binding differs. |
| `replay?` | Validates the entire graph, then selects the requested root and query list. Empty graphs and invalid selected indices cannot return checked evidence. |
| `replay_eq` | Identifies the cached implementation with the original prefix replay, including the exact reconstructed tree and rejection behavior. |
| `check` | Boolean view of actual replay success; it is certificate acceptance, not a root-existence decision. |
| `check_replay` | An arbitrary accepted graph has an actual accepted tree expansion on the caller's full bindings. It does not claim unconditional producer success. |
| `descriptor?` | Checks raw shape and context, performs the actual graph replay, then requires count one for the supplied word. Invalid evidence does not establish root nonexistence. |
| `descriptor_replay` | On the actual successful replay equation, graph extraction agrees with the tree-level constructor, including raw-shape/context/count rejection. |
| `descriptor_raw` | Successful extraction preserves the complete caller-supplied raw descriptor. |

The `Entry` equality instance compares literal nodes and child indices using
the existing component equality; it introduces no semantic coefficient equality.
The six fields are `Entry.node`, `Entry.children`, `Dag.entries`, `Dag.root`,
`Checked.value` and `Checked.accepted`. Each is documented at its declaration;
the last proof is erased at runtime. Graph selection can choose an earlier
entry, but graph validation still checks the complete array.

The existing conformance controls cover graph replay, missing/forward edges,
invalid unreachable entries, memo selection and foreign cache bindings. The
ordinary public umbrella imports this module. Existing callers in `DagMap`,
`DagEncode`, byte readers and root/sign extraction retain their contracts.
The new selection and rebinding equivalences supplement these controls with
arbitrary-input proof contracts. Kernel axiom guards in the existing conformance
module cover both new theorems. The manual explains the two bindings beside
its existing graph example; no new arithmetic algorithm or owner example is
introduced.
