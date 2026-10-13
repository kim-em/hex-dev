# Sign-determination counting and recursive replay API

This assessment covers 49 named declarations in six computational modules,
the `QueryReduction` and `Node` equality instances, and their structure fields.
It complements the foundation assessment and remains a partial core review.
Neither phase counters nor performance acceptance change. Names below are
relative to `Hex.SignDet`.

The [source bindings](core-replay-manifest.json) record the exact reviewed files and updated proof/manual
clients. Native producer and checker definitions are unchanged; the new replay
acceptance equivalences retain every executed branch guard.

## Counts

| Declaration | Assessment |
| --- | --- |
| `counts` | Counts occurrences of each literal column independently. Repeated observations contribute separate units; repeated columns would duplicate coordinates. These are observation counts, not polynomial multiplicities. |
| `moments` | Sums the actual exponent/sign entries in observation order. Empty observations give zero; word-shape laws are separate. |
| `counts_cons` | The private induction step needs distinct columns to identify the single incremented coordinate. Its proof uses the same countP and unit-vector operations as computation. |
| `count_moments` | Distinct candidate columns and complete coverage prevent double counting and omitted observations. Empty supports/observations remain valid; no root semantics is assumed. |
| `System.counts_eq` | Checked integer-system uniqueness recovers literal counts only after coverage and moment interpretation. The columns_nodup projection replaces checker unfolding without weakening either hypothesis. |
| `System.covers_counts` | Exact finite counts and coverage retain each observation after strictly-positive pruning. This representation lemma needs no matrix inversion or acceptance assumption. |
| `System.covers_support` | Combines count recovery and pruning while preserving checked-system, coverage and moment hypotheses. It does not infer coverage from invertibility. |
| `System.support_subset` | Exact counts exclude spurious positive columns without a coverage hypothesis. Together with covers_counts it gives membership equivalence when coverage is known. |

## Tensor

| Declaration | Assessment |
| --- | --- |
| `productVector` | Left-major concatenation uses quotient/remainder indices matching the native list product. With either dimension zero there is no input Fin index to divide. The companion productVector_toList supplies ordered list correspondence. |
| `tensor` | The supplied integer witnesses use the same left-major indexing as supports. Companion matrixEquiv_tensor, tensor_mul and tensor_inverse expose mathematical correspondence and composition; no new inversion is performed. |

## Moment

| Declaration | Assessment |
| --- | --- |
| `moment` | Literal zip truncates mismatched lists; callers must validate lengths. Zero powers and the empty product are one. General polynomial rearrangement needs arithmetic laws, supplied through interpretation rather than instances on storage. |

## MomentReplay

| Declaration | Assessment |
| --- | --- |
| `queryPoly` | Uses the unreduced moment only when reduction is absent; otherwise it selects the literal retained result. Acceptance of that result is delegated to checkMoment. |
| `checkMoment` | The direct branch checks length and ternary exponents; the reduced branch checks the supplied positive reduction. Both replay an exactly bound Tarski query, including context, endpoints and integer value. |
| `checkMoment_eq` | Characterizes arbitrary replay independently of cache provenance or contents. It exposes full ordinary query replay and each representation guard without assuming producer success. |
| `checkMoment_query` | Projects the actual checked query from either representation. It makes no root-sum claim without the companion interpretation/sign laws. |
| `checkMoment_reduction` | Extracts mandatory accepted reduction evidence in the some branch. A forged result cannot bypass the reduction checker. |

## QueryReduction

| Declaration | Assessment |
| --- | --- |
| `QueryReduction` | Retains one indexed polynomial reduction per original query. Literal equality includes every step and repeated position; serialization is a separate API. |
| `QueryReduction.queries` | Returns reduced next operands in original step order without deduplication. Length/degree claims require checked evidence. |
| `QueryReduction.slice` | Drop/take selects a contiguous child list and rebinds indices from zero. Polynomial witnesses and scales are unchanged, including empty and out-of-range slices. |
| `QueryReduction.operands` | Selects original factors or the supplied preprocessing results. The function alone claims no validity; local replay checks preprocessing first. |
| `QueryReduction.checkFrom` | Checks every step with previous accumulator one, its original query as factor and exact running index. Empty/empty succeeds; every list-length mismatch rejects. |
| `QueryReduction.check` | Requires positive head degree before indexed replay. Constant/zero heads use a different producer path rather than fictitious positive-degree preprocessing. |
| `QueryReduction.checkFrom_bounds` | Derives equal list lengths and zero-or-smaller-degree results from arbitrary accepted replay. The recursive proof follows the actual list checker. |
| `QueryReduction.check_bounds` | Transfers the indexed step bounds to the public reduced-query list. It retains zero operands explicitly. |
| `QueryReduction.checkFrom_take` | An accepted prefix keeps its starting index. Requested lengths past the list end remain valid because the checker already established matching lengths. |
| `QueryReduction.checkFrom_drop` | An accepted suffix advances the requested starting index. Dropping past the end checks the empty pair, so no nonexistent witness is assumed. |
| `QueryReduction.checkFrom_reindex` | Changes positional bindings only; all polynomial and positivity guards remain. The proof uses the complete ReductionStep.check_eq facts. |
| `QueryReduction.slice_checks` | Combines suffix, prefix and reindex lemmas to preserve child acceptance without rerunning division. Positive-degree head acceptance is retained. |
| `QueryReduction.buildFrom` | Produces one positive pseudo-division witness per ordered query. Success of the checker requires the companion arithmetic/sign laws and nonzero head. |
| `QueryReduction.build` | Starts the actual producer at index zero. Companion build_checks supplies checker acceptance under lawful interpretation and positive head degree. |

## Replay

| Declaration | Assessment |
| --- | --- |
| `Node` | Intrinsic dimensions bind the integer system, moment/reduction vectors and retained rank witness. Eleven fields have individual docstrings; no field asserts domain/root coverage without checking. |
| `Node.rows` | Selects exactly the rank witness rows, preserving their order. Independence requires the rank checks; selection alone does not prove it. |
| `Replay` | A leaf or a parent with both explicit children. There is no omitted-child constructor; shared dependency encoding is handled by the separate DAG API. |
| `Replay.node` | Exposes the literal root node for either constructor. It does not traverse children or compute evidence. |
| `Node.cache` | Uses a shared domain only after exact context/head/endpoints/chain matching. Otherwise it validates the first certificate only when reuse can benefit multiple moments; singleton or empty systems need no local cache. |
| `Node.check` | Retains literal bindings, integer-system acceptance, rank/column order, native rank replay, direct scaled inverse, preprocessing and every moment. An empty local dimension is possible; tree-level Replay.check and query_evidence supply the required leaf domain evidence. |
| `Node.check_eq` | Exposes each checker guard and removes only optional cache work. Its full conjunction remains literal; no mathematical coverage or producer assumption replaces a guard. |
| `Node.check_cache` | Any previously checked shared domain preserves local acceptance, including stale or differently represented witnesses that fail bindings and trigger full replay. |
| `leafColumns` | Empty queries retain the singleton empty sign word; singleton queries use all three sign codes. Larger arities are rejected by Replay.check, so this is no exponential fallback. |
| `leafRows` | Empty queries retain the root-count exponent row; singleton queries use exponents zero, one and two. These literal rows support complete leaf enumeration only with the leaf arity guard. |
| `Replay.check` | Checks both children before requiring exact ordered support/row products and local acceptance. Empty parent support cannot bypass checked leaf domains. |
| `Replay.check_leaf` | A full acceptance equivalence exposes all leaf guards for arbitrary supplied nodes, including empty queries. The producer proof now constructs these named facts rather than unfolding Boolean associativity. |
| `Replay.check_split` | A full acceptance equivalence exposes arity, both child checks, both ordered products and the parent check. Neither child completeness nor row order is silently dropped. |
| `Replay.check_node` | Projects the checked root node from either accepted branch. Its conclusion does not establish the entire subtree if used in isolation. |
| `Replay.check_children` | Supplies both accepted children and the exact column product; the new check_split equivalence also exposes rows and arity when needed. Existing clients keep their statements. |
| `Node.check_bindings` | Extracts exact context/head/interval/query bindings and accepted integer system. Literal certificate equality is preserved for noncanonical representations. |
| `Node.check_moment` | Every finite row index carries checked indexed moment evidence. Zero-size systems give no row, which is why tree-level query_evidence matters. |
| `Node.check_preparation` | Extracts checked optional preprocessing against the original ordered query list. Absent preprocessing returns true without claiming reduction. |
| `Replay.query_evidence` | Follows accepted children to a complete leaf whose fixed columns force positive size. At least one checked Tarski query therefore carries the original domain guards, even for an empty parent system. |

## Literal equality and public proof clients

`QueryReduction` equality compares the entire ordered step list. `Node`
equality first aligns dimension and literal ordinary fields, then aligns the
retained support length before comparing the rank witness. This is literal
certificate equality; it does not quotient semantically equivalent witnesses.

The companion `buildTreeFrom_checks`, native DAG acceptance proofs and `Transport.Finite.replay_check` consume the new equivalences. Arguments determined by the
checker result are implicit, permitting direct mp/mpr applications.
The tree producer consumes these facts without
changing its arithmetic/sign laws, preparation invariant or recursive
termination argument. Existing field/root consumers retain their original
support coverage and semantic hypotheses. The manual names the branch API;
the existing owner examples remain the examples.

Ordinary-kernel axiom guards cover the two new lemmas. Those proof checks do
not establish computational scaling, producer totality for an arbitrary sign
provider, complete family realization, or whole-pair Phase-6 acceptance.

The retained binding checker verifies every source hash and individual
declaration inventory/disposition table for both this assessment and the
sparse-table assessment, alongside the foundation and companion bindings.

These source snapshots are checked manually with the retained binding tool;
CI builds the proof clients and kernel controls but does not enforce snapshot
hashes against unrelated future edits. Instance and structure-field assessments
are individually reviewed; the declaration scanner verifies the named
definition/theorem inventories, while content hashes bind all source forms.
