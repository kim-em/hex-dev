# DAG encoding, prefix invariants and structural transformations

These source assessments cover 69 named declarations, five structure fields
and the entry hashing instance across nine DAG support modules.
They do not establish whole-library phase acceptance. Structural expansion
and arithmetic replay use separate instances of the same prefix invariant.

| Declaration | Assessment |
| --- | --- |
| `Dag.Expansion.step_bounds` | Private successful-step inversion proves both children refer to the supplied memo; a leaf has no reference-bound premise. |
| `Dag.Expansion.fold_bounds` | Private induction follows the actual expansion fold and growing prefix size, bounding every child reference at its stored entry index. |
| `Dag.encode_root` | Actual encoding of any replay tree selects an existing entry, independently of arithmetic acceptance. |
| `Dag.encode_bounds` | Every encoded child refers strictly backward; uses actual encoder expansion and fold bounds. |
| `Dag.Encoder` | Stores entries and an index cache as producer state; its type alone certifies neither index coherence nor arithmetic validity. |
| `Dag.Encoder.insert` | Reuses an exact cached entry or appends the new literal entry at the old array size. Arbitrary supplied cache state needs the separate invariant. |
| `Dag.encodeFrom` | Traverses children left-to-right before interning their parent; cached entries retain child indices and literal node identity. |
| `Dag.encode` | Starts from empty state, shares exact entries and retains the first index. Visits every tree occurrence; complexity is not bounded by distinct graph entries when expansion is large. |
| `Dag.mapNodes` | Transforms each stored node once and retains all indices, edges and the selected root across carrier/context types. It transports no arithmetic acceptance. |
| `Dag.size_mapNodes` | Preserves array length, including unreachable entries. |
| `Dag.node_mapNodes` | Retrieves exactly the transformed original node at a valid original index. |
| `Dag.children_mapNodes` | Both ordered child references remain literally unchanged. |
| `Dag.root_mapNodes` | Root index is unchanged even for malformed raw graphs. |
| `Dag.Prefix` | Every successful old lookup yields the same value in the later memo; failure positions carry no promise. This is sufficient preservation, not an assertion about storage allocation. |
| `Dag.Prefix.refl` | Identity memo inclusion preserves every successful lookup. |
| `Dag.Prefix.trans` | Composes successful-lookup preservation without adding an array-size premise. |
| `Dag.Prefix.push` | Appending retains all earlier successful lookups and their exact values. |
| `Dag.Encoder.Valid` | Binds the actual fold, entry/memo size and every cache lookup to the supplied step function. Arithmetic validity follows only when that function is an arithmetic checker. |
| `Dag.Encoder.valid_empty` | Empty state satisfies the fold/size/cache invariant for any supplied step function. |
| `Dag.Encoder.insert_valid` | Under successful-step monotonicity and a valid prior state, insertion preserves the memo prefix and binds its returned index to the exact new local result; handles both cache reuse and insertion without trusting hash uniqueness. |
| `Dag.Expansion.step` | Structural expansion reads both supplied child indices or constructs a leaf. It performs no arithmetic, context, query-split or support checks. |
| `Dag.Expansion.step_isSome` | Exact success criterion for arbitrary memo/entry data: leaves always expand, while a split requires both optional child lookups. It checks no arithmetic. |
| `Dag.Expansion.run` | Folds every stored entry from an empty memo. Forward/cyclic/missing references reject even in unreachable entries; root-index selection occurs separately. |
| `Dag.Expansion.step_mono` | Exact structural result persists under successful-lookup prefix preservation; no arithmetic acceptance or global array inclusion theorem is assumed. |
| `Dag.Expansion.Valid` | Specializes the generic encoder invariant to structural expansion, without adding arithmetic validity. |
| `Dag.Expansion.valid_empty` | Empty state satisfies that structural invariant through the generic empty-state law. |
| `Dag.Expansion.insert_valid` | Uses structural step monotonicity to preserve the invariant, old memo values and exact returned index. |
| `Dag.Expansion.encodeFrom_expands` | Induction follows the actual left/right encoder traversal and every literal child occurrence, including invalid arithmetic evidence. |
| `Dag.expand?` | Requires successful expansion of every entry, then looks up the selected root. Structural success alone does not authenticate certificates. |
| `Dag.expand_encode` | Any supplied tree is recovered literally after encoding, with no replay-acceptance premise. |
| `Dag.step_expands` | An accepted local arithmetic step returns the same tree as structural expansion. The converse is not claimed. |
| `Dag.fold_expands` | Private fold induction preserves every checked value under structural expansion, including exact child references. |
| `Dag.validate_expands` | Successful validation gives the structural memo for every serialized entry, not merely the root-reachable subset. |
| `Dag.replay_expands` | Arbitrary accepted graph replay expands to precisely its returned tree, retaining the exact literal returned replay. |
| `Dag.check_encode_eq` | Boolean graph and tree checks agree in both acceptance and rejection; encoding cannot repair invalid supplied evidence. |
| `Dag.descriptor_encode` | Graph/tree descriptor extraction agrees on every encoded literal tree, including all malformed-subject and replay-refusal branches. |
| `Dag.step_mono` | Arithmetic local-step success and exact checked value persist under memo-prefix growth; successful earlier child lookups are unchanged. |
| `Dag.step_leaf` | Accepted leaf replay identifies the complete checked local-step value in any memo. |
| `Dag.step_split` | Exact supplied child lookups and accepted split replay imply the complete checked local-step value, retaining ordered query products and bindings. |
| `Dag.encodeFrom_checks` | Actual recursive encoding preserves an accepted tree and all prior memo bindings while checking every generated entry. |
| `Dag.replay_encode` | An accepted tree replays from its encoded graph with the exact caller queries and literal evidence; no root-sum or interpretation premise is needed. |
| `Dag.check_encode` | Encoded accepted trees pass graph checking; general rejection agreement is supplied by check_encode_eq. |
| `Dag.Checked.ofOperations` | Restores a literal checked tree under five equal arithmetic instance dictionaries; equality transport changes only the erased proof. |
| `Dag.changeOps` | Maps optional checked memos under those literal equalities, preserving absence and stored values without rerunning checks. |
| `Dag.changeOps_validate` | Operation transport agrees with actual validation, including rejection; no merely semantically equivalent operations are substituted. |
| `Dag.changeOps_values` | Complete literal replay values survive operation transport, in order and with both successful and absent memos covered. |
| `Dag.changeOps_isSome` | Operation transport preserves exactly whether the optional memo is present. |
| `Dag.changeOps_nodes` | Every stored literal node survives transport, including nodes not selected by a root lookup. |
| `Dag.signOperands` | Collects local-node sign dependencies from every stored entry, including unreachable entries; it is not just a selected-root inventory. |
| `Dag.step_sign_congr` | Finite local sign agreement and equal literal memo values preserve the optional step value across sign indices, including rejection. |
| `Dag.fold_sign_congr` | Private induction preserves the optional complete memo under every entry’s finite sign agreement and initial literal-value equality. |
| `Dag.select_congr` | Private selection proof uses optional literal memo equality to preserve missing-memo, invalid-index, query-mismatch and successful-root branches. |
| `Dag.replay_sign_congr` | Agreement on all stored sign operands preserves the exact optional returned tree without recursively rechecking an expanded tree. |
| `Dag.check_sign_congr` | Graph Boolean checking depends only on that complete finite operand inventory, including malformed and unreachable entries. |
| `Dag.descriptor_sign_congr` | Finite sign agreement preserves exact raw descriptor/evidence data or rejection; context, head and endpoints remain literal inputs. |
| `SelectedSigns.ofTable` | Constructs selected-query evidence from accepted joint replay and the exact unique extending row of count one, without repeating replay. |
| `SelectedSigns.ofMemo?` | Selects an exact root/query entry from an accepted memo, then requires the complete unique extending row for the supplied sign vector. |
| `SelectedSigns.ofMemo_evidence` | Successful extraction retains the supplied sign vector and precisely the tree from the actual index/query lookup. |
| `SelectedSigns.readMemo?` | Checks literal head and endpoint equality before extracting selected signs from independently indexed memo data; sign/context are fixed in the type. |
| `SelectedSigns.readMemo_same` | A memo already on the descriptor domain gives the original extraction result exactly, including refusal. |
| `SelectedSigns.readMemo_evidence` | Successful dynamic binding identifies the actual accepted transported memo and subsequent extraction, without rerunning graph/domain checks. |
| `Dag.selectedSigns?` | Validates every graph entry for the descriptor prefix plus ordered queries and checks the exact claimed unique extending row; no replacement query evidence is produced. |
| `Dag.selectedSigns_memo` | Selecting from an actually validated memo equals graph selected-sign checking, including refusal and complete returned evidence. |
| `Dag.selectedSigns_evidence` | Success identifies the actual accepted graph replay and preserves every supplied sign and literal evidence field. |
| `Dag.selectedSigns_checked` | Successful graph extraction passes the independent descriptor tree checker for the original supplied query list and vector. |
| `Dag.selectedSigns_replay` | After actual graph replay succeeds, selected-sign presence equals the original tree checker on the exact claimed vector. |
| `Dag.selectedSigns_encode` | Encoding existing accepted selected-sign evidence preserves acceptance and the exact literal evidence tree. |
| `Dag.selectedSigns_encode_eq` | Encoding any supplied tree preserves both selected-sign acceptance and rejection, including malformed query/matrix evidence or a wrong vector. |
| `Dag.selectedSigns_sign_congr` | Finite stored-node sign agreement and equal raw descriptor identity preserve the optional sign/evidence data. Descriptor proof fields and source replays may differ. |

The entry hashing instance narrows search by selected literal fields; exact
entry equality still compares every node field and ordered child references.
Encoder fields `entries`/`indices` and invariant fields `fold`/`size`/`indices`
are individually documented. Prefix laws and private helper statements retain
short names and explicit hypotheses. There is no arithmetic acceptance
transport from structural expansion or node mapping alone.
