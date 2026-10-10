# Sign-determination companion declarations

The [manifest](manifest.json) identifies the 226 handwritten declarations in
37 production modules. Names below are relative to `Hex.SignDet`, except for
`Vector.toList_transport` and the three `Dag` theorems. Private helpers are
included; generated projections and elaborator declarations are not separate
entries. Each assessment considers the statement and proof, its hypotheses,
its role in the public API and its characterization of the executed operation.
Compiled references and their limitations are described in the [overview](README.md).

## Basis

| Declaration | Assessment |
| --- | --- |
| `rank_selectCols` | Distinct selected columns of a square integer matrix remain independent when the supplied scaled left inverse has nonzero denominator. No root interpretation or positive counts are assumed. |
| `System.retained_rank` | Pruning selects distinct positive-count columns, so rank equals retained width, including width zero. The system check supplies the inverse, rather than completeness of root support. |
| `System.basis_checks` | The actual integer rank producer passes its checker via exact integer quotient cancellation. No separate rank algorithm or supplied successful result is used. |
| `System.basis_rank` | Composes the checked producer's rank with retained-matrix rank to give the precise basis dimension. |
| `ordered_cols` (private) | An increasing enumeration of all finite columns is the identity enumeration; equal cardinality is essential. Used to preserve literal column order. |
| `System.basis_columns` | Full retained-column independence makes the producer's increasing pivot columns exactly the original order. This prevents a hidden permutation in child products. |
| `reverse_inverse` (private) | Nonzero scaled right inversion of a square integer matrix implies the matching left identity through determinant regularity, including dimension zero. |
| `System.basis_inverse` | Converts the actual rank certificate's right-inverse identity to the left-inverse identity required by BKR, with the same selected minor and denominator. |

## CommonProduct

| Declaration | Assessment |
| --- | --- |
| `CommonProduct.check_roots` | Arbitrary accepted product/divisibility identities prove the exact union of roots. The certificate need not come from the gcd producer; squarefreeness remains a separate obligation. |
| `quotient_lcm` (private) | Association with the gcd gives the three required division identities and association with the lcm. Zero inputs are handled explicitly. |
| `CommonProduct.build_success` | Proves success of the executed gcd/division constructor and association of its returned head with the mathematical lcm. Zero reflection suffices; literal coefficient injectivity is absent. |
| `CommonProduct.build_squarefree` | Squarefree source heads make the actual common head nonzero and squarefree. The conclusion supplies the domain needed by cross-polynomial comparison. |

## ComparisonProducer

| Declaration | Assessment |
| --- | --- |
| `Descriptor.buildComparison_success` | Constructs the common squarefree head, both successful joint re-encodings and a full-word ordering. No successful comparison is a premise. Division preservation is explicit. |
| `Descriptor.buildOrder_roots` | Equal literal heads use actual completions; different heads use the common-head producer. Both paths compare the original selected roots, even across different intervals. |
| `Descriptor.compare_success` | The public total comparator uses an actual successful order constructor; its diagnostic fallback is unreachable under the coefficient laws. |
| `Descriptor.compare_correct` | Characterizes all three results by strict mathematical order of the original selected roots, without requiring equal defining polynomials. |
| `Descriptor.compare_eq_iff` | Returned equality is exactly root equality; the two strict-order cases exclude accidental fallback equality. |
| `Descriptor.compare_lt_iff` | Gives the direct forward-order criterion usable downstream without unfolding the comparator. |
| `Descriptor.compare_gt_iff` | Gives the reverse strict-order criterion, with the same producer and interpretation hypotheses. |

## CompletionProducer

| Declaration | Assessment |
| --- | --- |
| `RawDescriptor.full_at` | The executed full query list is the formal derivative word in slots 1 through degree, without monic normalization or altered signs. |
| `RawDescriptor.full_congr` | Mathematically equal heads have equal full words even when their stored representations differ; zero reflection supplies degree agreement. |
| `Descriptor.select_full_at` | Selecting validated derivative indices from the complete word gives the original partial word at the same point, including an empty partial encoding. |
| `Descriptor.completion_rows` | An arbitrary accepted complete derivative table has exactly one count-one row extending the source word. Source count-one uniqueness and table semantics, rather than Thom ordering, establish this fact. |
| `Descriptor.buildCompletion_success` | Constructs preparation and the actual BKR table before discharging the completion guards. Neither successful output nor a matching row is assumed. |
| `Descriptor.buildCompletion_roots` | Combines actual success with preservation of the selected root and every formal derivative sign. |
| `Descriptor.complete_success` | Excludes the total wrapper's unchanged-source diagnostic fallback by identifying its actual successful completion. |
| `Descriptor.complete_correct` | Preserves root and literal source bindings and returns canonical full derivative slots and signs. These conclusions characterize the wrapper without opening its implementation. |

## Convert

| Declaration | Assessment |
| --- | --- |
| `convert_interpret` | Coefficientwise conversion preserves the interpreted polynomial when target values agree. Neither representation is required to be injective. |
| `convert_endpoint` | Finite values and infinite endpoint constructors survive conversion; no arithmetic or order hypotheses are needed. |
| `domain_convert` | Nonzero squarefree head, strict endpoint order and endpoint nonvanishing all survive value-preserving conversion. Real-closedness is unnecessary for domain alone. |
| `RawDescriptor.map_domain` | Applies that full domain equivalence to the actual mapped descriptor and its new literal context. |
| `RawDescriptor.map_signs` | Target derivative queries are reconstructed using target arithmetic; their signs agree by interpretation, without requiring literal preservation of arithmetic representations. |
| `Descriptor.convert_success` | Builds fresh target evidence from source count-one semantics and domain/sign correspondence. Target negation/inverse laws are required for production. |
| `Descriptor.convert_root` | A successful checked conversion preserves the exact selected root. This soundness statement does not assume target producer laws beyond the interpretation needed for accepted descriptors. |

## DagSelectedSigns

| Declaration | Assessment |
| --- | --- |
| `Dag.selectedSigns_values` | An arbitrary supplied graph accepted for the requested values has precisely the ordered signs at the original descriptor root. No graph producer provenance is assumed. |
| `Dag.memo_values` | An accepted shared-memo selection has the same mathematical signs; the result is tied to the memo's checked domain. |
| `Dag.readMemo_values` | Independently supplied domain bindings are checked before applying the memo theorem. It does not treat a matching index alone as valid evidence. |

## Derivatives

| Declaration | Assessment |
| --- | --- |
| `derivativesFrom_get` | Each executed derivative position equals the corresponding iterated formal derivative. The index bound and natural-cast/multiplication laws are sufficient. |
| `RawDescriptor.querySigns` | A well-formed descriptor's indexed query word agrees with formal derivative evaluation. Bounds justify indexing and remove the executable default branch. |

## Embedding

| Declaration | Assessment |
| --- | --- |
| `interpret_embedding` | Coefficient interpretation in the target field is polynomial mapping along the supplied ring homomorphism. No ordering is needed for this identity. |
| `signsAt_embedding` | Strict monotonicity preserves each sign at the image point, including zero signs and original query positions. |
| `interval_embedding` | The same ordered embedding preserves finite and infinite open-interval constraints. It does not assume rational separators. |
| `root_mem_embedding` | Membership supplies nonzero head and interval evidence; polynomial mapping then preserves root membership in the target interval. |
| `Descriptor.root_map` | The same accepted descriptor in two ordered real-closed ambient fields selects the image of its old root. Both interpretations and sign agreements remain explicit. |
| `Descriptor.root_comp` | Specializes root preservation to composition and derives the target arithmetic, zero and sign laws from the source and embedding. |

## FiniteSolve

| Declaration | Assessment |
| --- | --- |
| `columns_distinct` | A nonzero scaled left inverse forces distinct candidate columns before system acceptance. This avoids assuming a checker guard merely from eventual solver success. |
| `counts_nonneg` | Finite occurrence counts are nonnegative independently of completeness or matrix identities. The lemma directly discharges the executable guard. |
| `system_counts` | Shape, inverse and independently supplied observation coverage construct a checked system with actual counts and moments. Distinctness and nonnegativity are derived. |
| `System.check_counts` | Replaces counts and values by those of a new covered observation list while retaining the checked shape and inverse. Coverage remains a caller premise. |
| `empty_system` | The zero-query leaf covers every empty observation, including repeated empty words and no observations. Counts are constructed rather than assumed. |
| `singleton_system` | The three ternary columns and explicit inverse cover all singleton observations. Coverage precedes solving and includes zero-count columns. |

## Foundation

| Declaration | Assessment |
| --- | --- |
| `occCount_getElem` | Counts positions in a list, so duplicate words retain their occurrence multiplicity. This identifies Tau Ceti's sample function with the executable list count. |
| `sum_getElem` | The position-indexed foundation sum equals the actual ordered list sum, including the empty list. Generality is only additive-commutative-monoid structure. |
| `foundation_moments` | Applies the finite counting identity to the literal rows and columns. Distinct columns and complete observation coverage are explicit and independent of rank. |
| `System.foundation_counts` | A checked scaled inverse recovers the true counts only after separate coverage and actual-moment premises. An invertible incomplete candidate system is not accepted as completeness evidence. |
| `Replay.foundation_complete` | Existing replay induction obtains coverage from full leaf columns or already complete child supports, then applies count recovery before pruning each parent. |

## Naturality

| Declaration | Assessment |
| --- | --- |
| `signsAt_convert` | Ordered evaluation signs are preserved pointwise by value-preserving coefficient conversion; polynomial conversion supplies the characterization. |
| `Descriptor.convert_signAt` | Both actual total sign producers agree after successful checked conversion. Producer laws on both carriers rule out their diagnostic fallbacks. |
| `Descriptor.convert_compare` | Converts both roots and characterizes both actual total comparators, preserving equality and both strict orders across different heads. Division laws on both carriers remain necessary. |
| `determine_convert_counts` | Actual returned tables have equal counts for every word after value-preserving conversion, including words omitted from sparse storage. Each returned-table equation remains explicit. |
| `determine_convert_isSome` | Domain equivalence gives availability equivalence of the option-valued APIs over an ordered field. Real-closedness is unnecessary; this theorem alone does not assert root counts or absence of internal diagnostic fallback. |
| `Descriptor.buildRoots_convert_isSome` | Complete root-list production succeeds on equivalent converted domains, including valid root-free domains. Its proof uses real-closedness through `buildRoots_success`. |
| `Descriptor.buildRoots_convert_roots` | Compares the actual returned lists using coverage and strict sorting. Equal root membership alone would only give a permutation, so ordering is essential. |

## NodeBasis

| Declaration | Assessment |
| --- | --- |
| `Node.basisRows` | Dimension-indexed selected exponent rows retain the rank witness's literal row order. The list characterization is `basisRows_list`. |
| `Node.basisCols` | Dimension-indexed columns refer through positive-column selection; `basis_support` characterizes their ordered list under the column-order hypothesis. |
| `Node.basisRows_list` | Identifies the indexed representation with the node's actual executable row list, avoiding downstream unfolding of the vector definition. |
| `Node.basis_matrix` | The selected minor is exactly the moment matrix of these selected rows and columns before assuming rank-producer order. |
| `Node.basis_support` | An explicit full increasing column enumeration identifies the basis columns with all retained positive columns, including an empty support. |
| `Node.basis_width` | Checked row and column widths discharge the concatenation/tensor length premise; no polynomial semantics is needed. |
| `Node.basis_inverse` | The actual rank certificate inverts the indexed retained moment matrix. Equality with the producer's witness is explicit. |
| `Node.product_inverse` | Child producer witnesses compose into the exact Cartesian row/support lists and tensor inverse used by the parent. No parent success or root coverage is assumed. |

## NodeChecks

| Declaration | Assessment |
| --- | --- |
| `nodePreparation_checks` | Enabled reduction retains valid supplied preprocessing or constructs accepted preprocessing; disabled reduction carries none. Positive degree is derived from the actual reduction guard. |
| `buildNode_preparation` | Successful node construction retains the same checked preprocessing selected before solving. |
| `buildNode_checks` | Successful node construction passes complete local replay, including actual prepared query certificates and rank evidence. It is algebraic acceptance, not root-sum semantics or unconditional construction success. |

## NodeProducer

| Declaration | Assessment |
| --- | --- |
| `solveSystem_spec` | Arbitrary successful rational solving preserves literal row/column/value orders and passes the finite system checker. It does not infer mathematical root meaning from the supplied values. |
| `solveScaled_spec` | Successful scaled solving additionally retains the supplied denominator and inverse, rather than choosing new witnesses. |
| `Vector.toList_transport` | Equality transport changes the dimension index without changing ordered entries. The statement deliberately lives in the vector namespace. |
| `buildNode_spec` | Successful construction binds context, head, both endpoints and query list, and retains the actual checked system and rank certificate. |
| `buildNode_evidence` | Every reduction and certificate is tied to its actual indexed row and preprocessing; stored system values are exactly the certificate values. |
| `Node.check_of_basis` | The actual rank witness discharges matrix guards while polynomial/preprocessing evidence and literal bindings remain explicit. It is not a replacement root checker. |

## NodeSolve

| Declaration | Assessment |
| --- | --- |
| `buildNode_complete` | A checked candidate system with actual queried values proves node success for either rational or supplied scaled inversion. Independent coverage is established by callers, not inferred here. |
| `Node.parent_system` | Transports the checked child-product system to exactly the parent's list dimension, denominator and inverse. It preserves ordered rows, columns, counts and values without a permutation or new inverse search. |

## ParentSystem

| Declaration | Assessment |
| --- | --- |
| `product_all` (private) | Concatenating checked child words preserves combined width and entry guards. It supports both exponent and ternary-column validation. |
| `support_valid` (private) | Pruning preserves the original system's column width and ternary entries; it does not claim that the support covers observations. |
| `rows_valid` (private) | Selected rank-basis rows retain the system's width and exponent bounds. |
| `Node.product_system` | Independent coverage by both child supports constructs a checked parent on their literal Cartesian product. Tensor inversion and count guards are proved before the parent solve. |

## QueryHandle

| Declaration | Assessment |
| --- | --- |
| `Descriptor.prepareQueries_success` | Actual preparation succeeds for every accepted descriptor under producer laws, by constructing the empty-query selected-sign result. |
| `QueryHandle.buildSigns_success` | The cached handle's actual operation succeeds for any ordered query list by its proved agreement with ordinary selected-sign production. |
| `QueryHandle.buildSigns_roots` | Successful cached production retains original-root signs, including empty lists, repeats and zero answers. |
| `QueryHandle.signAt_success` | Identifies the successful singleton result used by the cached total sign wrapper, excluding its error fallback. |
| `QueryHandle.signAt_correct` | Cached singleton output is evaluation at the descriptor's original root. It reuses ordinary correctness rather than introducing a second semantic algorithm. |

## QueryReduction

| Declaration | Assessment |
| --- | --- |
| `QueryReduction.checkFrom_signs` | Arbitrary accepted indexed preprocessing preserves each query sign at every head root. Empty chains, zeros and duplicate queries are retained in order. |
| `QueryReduction.check_signs` | Projects that chain contract to the full ordered query vector of an accepted preprocessing record. |
| `Node.check_sign` | Composes accepted preprocessing and moment reduction to relate the actual Tarski operand to the original moment sign. Neither certificate is assumed produced. |
| `QueryReduction.buildFrom_checks` | The executed producer builds accepted preprocessing from a nonzero head and lawful arithmetic/sign operations, at any starting index. |
| `QueryReduction.build_checks` | Positive degree supplies the nonzero-head premise and the actual top-level producer passes its complete checker. Constant heads take the separate unreduced path. |

## RationalSolve

| Declaration | Assessment |
| --- | --- |
| `System.rationalInverse` | A checked integer scaled inverse forces the actual rational inverse operation to succeed, including the empty matrix. No root semantics is used. |
| `System.rationalCounts` | The inverse returned by the executed rational operation recovers the checked integer counts before denominator and positivity tests. |
| `clear_scalar` (private) | Divisibility gives the exact denominator-scaled entry identity. The natural scale may be zero; positivity is supplied separately by `inverse_den`. |
| `inverse_den` | The actual lcm fold is positive and clears every inverse entry in its literal index order, including dimension zero. |
| `clear_inverse` | Clearing the actual rational inverse yields the integer scaled identity checked by replay. Integer casting reflects the matrix equality. |
| `solveSystem_complete` | Checked finite systems force actual rational solver success with the same ordered rows, columns, values and counts. The newly chosen inverse and denominator need not equal the old witnesses. |

## Reduction

| Declaration | Assessment |
| --- | --- |
| `ReductionStep.check_sign` | Arbitrary checked positive-scaled identities preserve the product sign at each head root, including roots shared with the factors. Positive scales are essential; values need not be equal. |
| `Reduction.checkFrom_sign` | The accepted chain preserves the product of its ordered factor signs and initial accumulator. Chain length and factor binding come from replay. |
| `interpret_power` (private) | The actual repeated-squaring polynomial power agrees with interpreted powers under the coefficient laws. Zero and one exponent branches are explicit. |
| `fold_sign` (private) | The executable multiplication fold retains the sign of its initial accumulator and the product of all factor signs. |
| `moment_sign` (private) | Relates the moment's sign to repeated indexed factors. Repetitions and the executable zip behavior are preserved. |
| `moment_entry` | The polynomial moment's integer sign equals the exact matrix entry. Both sides have the same truncated-zip behavior even before shape guards. |
| `moment_congr` | Pointwise equality of ordered query signs suffices for moment-sign equality; polynomial value equality is unnecessary. |
| `Reduction.check_sign` | An arbitrary accepted reduction has the requested full moment's sign at every head root. It consumes checked identities rather than producer provenance. |
| `checkMoment_sign` | Both direct and reduced actual query operands have the original moment sign. Root-sum correspondence remains a separate theorem. |

## ReductionProducer

| Declaration | Assessment |
| --- | --- |
| `ReductionStep.build_checks` | Actual pseudo-division and normalization produce positive scales, exact identity, factor index and strict remainder-degree guard on a nonzero head. |
| `Reduction.buildFrom_checks` | Every executed finite factor chain passes replay, including an empty chain. It reuses the one-step producer law. |
| `Reduction.build_checks` | The top-level producer passes the full checker on positive degree, matched query/exponent lengths and bounded exponents. It does not generalize reduction to invalid shapes. |

## Reencode

| Declaration | Assessment |
| --- | --- |
| `endpoint_eval` | The actual stored boundary polynomial evaluates to the strict-bound difference even for noncanonical coefficients. Only zero, one and subtraction correspondence are needed. |
| `endpoint_lower` | Positive sign of the executed boundary polynomial characterizes strict lower-bound membership; endpoint roots are excluded. |
| `endpoint_upper` | Negative sign of the same polynomial characterizes the strict upper bound. The three-valued sign laws justify the integer minus-one test. |

## ReencodingProducer

| Declaration | Assessment |
| --- | --- |
| `Descriptor.buildReencoding_invalid` | Invalid nonzero/squarefree/endpoint domain returns actual absence through shared preparation. Root membership by itself does not make a repeated head valid. |
| `Descriptor.buildReencoding_absent` | When the original selected root is absent from the target domain, the actual joint table has no matching constraint row and production returns absence rather than an internal error. |

## ReencodingRefinement

| Declaration | Assessment |
| --- | --- |
| `Descriptor.reencoding_rows` | An arbitrary accepted joint table containing the source root has exactly one count-one matching row. This does not yet establish uniqueness of the target derivative word alone. |
| `Descriptor.reencoding_fiber` | Mathematical head equality and containment in the old root domain let the old partial word establish uniqueness of the target full-word fiber without Thom injectivity. |
| `Descriptor.refinement_fiber` | Specializes the contained-domain fiber theorem to the same literal head. Membership of the selected root remains necessary. |
| `Descriptor.buildReencoding_congr` | The executed producer builds fresh evidence for a zero-difference equal head on a valid contained domain retaining the source root. It does not reuse stale literal evidence. |
| `Descriptor.buildReencoding_refinement` | The same-head smaller-domain constructor succeeds under validity, source-root membership and containment. It is a scoped refinement theorem, not general target-head totality. |

## RootList

| Declaration | Assessment |
| --- | --- |
| `Descriptor.buildRoots_empty` | A valid root-free domain produces an actual empty list. Both table extraction branches are discharged without assuming output success. |
| `Descriptor.buildRoots_subsingleton` | Actual enumeration succeeds on valid domains of at most one root, without a Thom ordering assumption or rational separation. |
| `Descriptor.buildRoots_constant_success` | Nonzero constant heads on valid domains return an empty list. The zero polynomial is excluded by domain validity. |
| `Descriptor.buildRoots_linear` | Degree one supplies the small-root-set premise for actual enumeration. It still permits no root in the requested interval. |
| `Descriptor.buildRoots_domain` | Successful enumeration implies the caller's exact domain through preparation soundness over an ordered field; no root-sum theorem is needed. |
| `Descriptor.buildRoots_none_iff` | The absent-domain result characterizes invalid domains, independently of real-closedness or successful extraction. A valid empty result is distinct from absence. |
| `Descriptor.buildRoots_coverage` | Any successful actual list covers all distinct interval roots exactly once. It does not prove unconditional production or strict ordering; those are separate Thom contracts. |

## RootModel

| Declaration | Assessment |
| --- | --- |
| `signsAt` | Maps the original ordered queries to integer signs at one point. Conversion and embedding theorems characterize changes of representation and ambient field. |
| `rootObservations` | Uses one observation per distinct head root while retaining repeated sign words at different roots. It does not count polynomial root multiplicity. |
| `rootObservations_valid` | Every observation has the exact query arity and ternary coordinates; no table acceptance or successful construction is assumed. |
| `rootObservations_take` | Query prefixes give matching prefixes at each root of the unchanged head/domain. The one-way simp annotation normalizes observation slicing. |
| `rootObservations_drop` | Query suffixes give matching suffixes over the same root set, including out-of-range drops. |
| `Node.check_values` | Arbitrary accepted query certificates and checked reductions make each stored integer value the actual root moment. Natural casts and the real-closed root-sum foundation remain explicit. |
| `Replay.check_domain` | Even an accepted empty-support table retains independent query evidence for the complete mathematical domain. |
| `Replay.check_interprets` | Accepted children interpret the exact balanced query slices over the same head roots. It supplies the semantic premise of finite support induction. |
| `Replay.check_support` | Arbitrary accepted replay retains precisely all realizable words. Candidate completeness comes from recursive coverage, not invertibility alone. |
| `Replay.check_counts` | Counts occurrences of words among distinct roots, including zero counts and empty supports; these are not polynomial multiplicities. |
| `Replay.count_roots` | Sparse lookup equals the cardinality of roots realizing the requested ordered word, and omitted words have zero count. |

## RootProducer

| Declaration | Assessment |
| --- | --- |
| `query_values` | Actual prepared query production supplies the finite moment model, including preprocessing and reduction. Supplied preprocessing must be checked; the head/domain/sign are explicitly bound. |
| `query_model` | Root observations satisfy that model at every actual balanced slice, using the same preprocessing slices and unchanged root domain. No solver result or support completeness is a premise. |
| `buildPrepared_roots` | Valid prepared domains and lawful coefficients force actual BKR construction and exact counted invariants at every node. The root-sum theorem supplies the finite model internally. |
| `Descriptor.build_noError` | Every raw input returns an outer successful diagnostic result under lawful coefficients. Inner invalid, absent or ambiguous results remain possible. |
| `Descriptor.build_of_unique_root` | Matching context, well-formed word, actual prepared domain and one realizing root force accepted descriptor construction. |
| `Descriptor.build_success_iff` | Gives the exact context, shape, domain and count-one criterion in both directions for the actual constructor. |
| `Descriptor.validate_success_iff` | Transfers the same complete criterion to the public option-valued validator, without silently conflating invalid and successful-empty cases. |
| `Descriptor.build_valid_cases` | On valid raw input, zero, one and multiple realizing roots yield absent, accepted and ambiguous inner results respectively. Counts refer to the jointly requested word. |
| `Descriptor.build_success_formal` | Expresses the exact constructor criterion with formal derivatives, justifying executable indexing by the well-formedness premise. |
| `Descriptor.validate_success_formal` | Gives the corresponding formal-derivative criterion for validation without duplicating construction. |

## SelectedProducer

| Declaration | Assessment |
| --- | --- |
| `Descriptor.signs_rows` | An arbitrary accepted joint table has one count-one row extending the validated source word; its suffix is evaluation at the original root. Source uniqueness suffices without Thom order. |
| `Descriptor.buildSigns_success` | Actual preparation, table construction and final guards succeed for any ordered query list on an accepted descriptor. No successful selected-sign result is assumed. |
| `Descriptor.buildSigns_roots` | Combines actual success with exact original-root signs, including empty and repeated queries. |
| `Descriptor.signAt_success` | Identifies the successful singleton certificate used by the actual total wrapper and excludes its internal error fallback. |
| `Descriptor.signAt_correct` | Total singleton sign is evaluation at the original root, with explicit producer laws rather than mere accepted-output soundness. |

## SelectedRoot

| Declaration | Assessment |
| --- | --- |
| `Descriptor.existsUnique_root` | Count-one accepted replay selects one point jointly satisfying the interval and derivative word. Partial words are permitted when count-one evidence establishes uniqueness. |
| `Descriptor.root` | Classical choice supplies a semantic value, not a second executable root algorithm. `root_spec` and `root_unique` encapsulate the choice. |
| `Descriptor.root_spec` | The selected value belongs to the exact interval root set and satisfies all stored query signs at that same point. |
| `Descriptor.derivatives_at` | Validated indices make executable derivative queries the formal iterated derivatives at any point. It needs no root semantics. |
| `Descriptor.root_derivatives` | The selected root realizes the formal derivative signs at the named indices, preserving slot order. |
| `Descriptor.root_unique` | Any point in the same root set with the same complete requested word equals the choice; an unrelated root or separately satisfied signs do not suffice. |
| `Completion.root_eq_source` | Checked completion bindings and selection of the full word preserve the old root using source uniqueness, without Thom ordering. |
| `Completion.signs_at_source` | Every completed formal derivative sign is evaluated at the original selected root, not a fresh independent selection. |
| `SelectedSigns.values_at_root` | Accepted joint determination ties every requested sign to the original root. Coverage and actual counts are used before extracting the word suffix. |
| `SelectedSigns.value_at_root` | The one-query accessor projects the same semantic sign; the singleton vector dimension justifies indexing. |
| `Reencoding.exists_root` | Accepted joint count-one evidence supplies a target point satisfying both target word and all source constraints simultaneously. |
| `Reencoding.target_constraints` | Target count-one uniqueness forces that joint point to be the target's selected root. No freedom to select another target root remains. |
| `Descriptor.constraints_head` | The first copied constraint implies the original defining equation; sign-code zero reflects actual evaluation zero. |
| `Descriptor.constraints_queries` | The copied query prefix retains the old derivative word. Accepted shape supplies the exact prefix length. |
| `Descriptor.constraints_bounds` | The copied suffix retains both finite endpoint sign conditions in order; infinite endpoints contribute no fictitious polynomial. |
| `castSignPos` (private) | Integer sign code one is equivalent to positivity. Used in strict endpoint semantics, with no real-closedness requirement. |
| `castSignNeg` (private) | Integer sign code minus one is equivalent to negativity and supplies the strict upper-endpoint interpretation. |
| `Descriptor.constraints_interval` | Copied finite signs express the old open interval. Acceptance excludes impossible infinite orientations. |
| `Descriptor.head_ne_zero` | Positive stored degree plus zero-reflecting interpretation excludes a zero head, independently of root-sum semantics. |
| `Descriptor.constraints_at_root` | The original selected point satisfies defining, derivative and strict endpoint constraints simultaneously. |
| `Descriptor.constraints_iff` | The actual copied constraints characterize exactly the original selected root; this is the public encapsulation needed by general re-encoding. |
| `Reencoding.root_eq_source` | Joint accepted evidence and the constraint characterization preserve the exact source value across different heads and intervals. |
| `Comparison.eq_root` (private) | Equal checked full words on the common literal domain imply equal original roots via count-one uniqueness and re-encoding preservation. Strict Thom order is unnecessary. |
| `Comparison.root_eq` (private) | Equal original roots give identical common full words and the equality branch of the finite comparator. Valid positive degree excludes empty guarded words. |
| `Comparison.eq_iff_root_eq` | Encapsulates both equality directions for arbitrary checked comparisons, independently of strict-order correctness. |

## Solve

| Declaration | Assessment |
| --- | --- |
| `solveScaled_eq` | The supplied checked scaled inverse recovers the exact counts and passes divisibility, nonnegativity and final system guards. It returns the same system, not merely some accepted result. |

## TableProducer

| Declaration | Assessment |
| --- | --- |
| `buildTablePrepared_success` | Actual sparse-table production succeeds for every query list on a valid prepared domain, using constructed BKR replay. |
| `determinePrepared_success` | The total prepared wrapper returns that actual successful table, excluding its empty-table error fallback. |
| `determinePrepared_correct` | Every requested word count equals its semantic root-fiber cardinality, including zero counts for omitted words. |
| `determine_isSome` | Availability is exactly shared domain validity over an ordered field. This is a domain-only contract; real-closedness and producer-value correctness are not needed. |
| `determine_correct` | Actual returned tables have the caller's exact valid domain and all semantic counts. Real-closedness and producer laws exclude misleading fallback values. |

## Tensor

| Declaration | Assessment |
| --- | --- |
| `productVector_toList` | The indexed Cartesian product is exactly the executable ordered list product, not a permutation of it. |
| `momentMatrix_product` | Concatenation produces the exact tensor matrix when left exponent/sign lengths agree. That premise prevents zip truncation across the join. |
| `matrixEquiv_tensor` | The executable tensor has standard product indexing, with the right coordinate varying fastest; zero-dimensional factors are included. |
| `tensor_mul` | Tensor multiplication agrees with the exact native matrix multiplication through the representation equivalence. |
| `tensor_identity` | Tensoring scaled identities multiplies denominators without changing the parent index order. |
| `tensor_inverse` | Composes two scaled child left inverses into the parent scaled identity; no rational inversion or semantic-root premise is introduced. |

## Thom

| Declaration | Assessment |
| --- | --- |
| `sign_int_inj` (private) | Equality of integer ternary codes reflects equality of sign constructors. This justifies moving executable words into the foundation's sign-valued encoding. |
| `sign_int_lt` (private) | Integer codes preserve strict order of sign constructors, supplying the executed comparison orientation. |
| `RawDescriptor.full_unique` | Tau Ceti Thom injectivity and polynomial Rolle derived from real-closedness establish uniqueness among roots of a nonzero head, including non-Archimedean fields. |
| `RawDescriptor.full_fiber` | Every realized full word has a singleton fiber within any supplied finite root set. The point's membership and nonzero head are explicit. |
| `RawDescriptor.full_lt` | The actual highest-first comparator agrees with strict root order by the last derivative-sign disagreement and next common sign. No rational separator is used. |
| `RawDescriptor.full_order` | Mathematical totality discharges all three branches, giving an actual successful comparator equation rather than conditional acceptance. |
| `RawDescriptor.full_lt_iff` | Encapsulates exact strict-order meaning of the finite comparison without requiring downstream unfolding. |
| `Descriptor.full_signs` | A validated full descriptor stores the complete reconstructed word at its own root. The full-index applicability premise is explicit. |
| `Descriptor.fullOrder_root` | Applicable guarded descriptors with the same literal head always compare correctly. Accepted positive degree and full indices discharge nonempty-word guards. |
| `Comparison.order_root` | Arbitrary checked common-head comparisons return mathematical order of the original roots through root-preserving re-encodings. |

## ThomReencoding

| Declaration | Assessment |
| --- | --- |
| `Descriptor.buildReencoding_success` | A valid target domain containing the source root forces actual joint re-encoding success. Thom injectivity supplies uniqueness of the target word alone; old constraints supply the joint row. |
| `Descriptor.buildReencoding_isSome` | Actual successful target re-encoding is equivalent to full target-domain validity and source-root membership, incorporating invalid and absent results from the separate producer theorems. |

## ThomRoots

| Declaration | Assessment |
| --- | --- |
| `Descriptor.fullOrder_strict` | Different realized full words on one head force an actual strict comparison. Equal-root and diagnostic branches are excluded by semantic full-word correctness. |
| `Descriptor.rootsFromTable_success` | The executed extraction and insertion succeed on supplied distinct count-one full rows. Public root production separately derives these finite premises. |
| `Descriptor.buildRoots_success` | Every valid domain forces actual root-list production. Nonzero constants are handled separately; Thom singleton fibers and strict totality discharge general extraction. |
| `Descriptor.buildRoots_isSome` | Characterizes complete list production exactly by original domain validity, pairing totality with successful-output domain soundness. |
| `Descriptor.buildRoots_ordered` | Interprets the executed sorting result as strict mathematical order of the returned roots, rather than sorting a separately defined semantic list. |
| `Descriptor.buildRoots_roots` | Combines actual success, exact distinct-root coverage, no duplicates and strict sorting over finite or infinite endpoints and noninjective storage. It does not report polynomial multiplicities. |

## TreeChecks

| Declaration | Assessment |
| --- | --- |
| `buildTreeFrom_checks` | Every successful executed recursive tree passes independent replay, including child slices, Cartesian support bindings and supplied preprocessing. This does not prove construction totality. |
| `buildTree_checks` | Top-level shared preprocessing supplies the recursive checker invariant from the actual positive-degree reduction guard. |
| `buildPrepared_eq` | Once actual tree construction succeeds, the final replay guard cannot introduce an internal error; its proof retains the same tree. |

## TreeSolve

| Declaration | Assessment |
| --- | --- |
| `QueryValues` | Requires actual prepared-query values to equal finite observation moments for all valid rows. Neither solved counts nor accepted output is a premise. |
| `QueryModel` | Extends that independent query-value obligation along the exact balanced slices and preprocessing slices. Observation occurrence multiplicity is retained. |
| `Node.Counted` | Records system acceptance, the actual rank witness, actual moment values, retained-support coverage and exact counts separately. `counts` follows from `checked`, `values` and `cover` via `System.foundation_counts` and support inclusion. Retain it as a convenient exact-count projection of the producer invariant; callers can use the bundle without reconstructing that derivation. The other fields preserve the independent checker, rank, moment and coverage obligations. |
| `Replay.Counted` | Carries the counted invariant at every node over the same recursively sliced observations, not merely the final root node. |
| `Replay.Counted.node` | Projects the local invariant without discarding the recursive statement at the call site. Unrelated arithmetic instances are omitted. |
| `buildNode_counted` | Given independently complete candidate columns and query values, actual node construction succeeds and its counted invariant follows. Coverage is never inferred from the inverse equation. |
| `moments_toList` | Literal list equality characterizes ordered finite moments when dimensions are transported between bases and products. |
| `leaf_system` (private) | Empty and singleton leaves have checked candidate systems covering every typed observation. Shape and ternary validity establish completeness before solving. |
| `buildTreeFrom_complete` | Finite query models and typed observations force the actual balanced producer to succeed. Child completeness constructs the parent candidate before solving, including empty observations/supports. |
| `buildTree_complete` | Shares actual root preprocessing with the same finite query model. Root-sum semantics still supplies that model separately. |
| `buildPrepared_complete` | Composes finite construction totality with independently proved algebraic replay acceptance. `RootProducer` supplies the remaining semantic query model for actual roots. |
