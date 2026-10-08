# Companion declarations

Names are relative to `HexSturmMathlib`, except in the indicated namespaces.
The assessment follows the [manifest](manifest.json). Each interpretation
retains its actual arithmetic/sign hypotheses; zero reflection permits
noninjective coefficient storage.

## Domain

| Declaration | Assessment |
| --- | --- |
| `EndpointLt` | Infinite endpoint order is structural; finite comparison uses the specified interpretation. Equal infinities and reversed endpoints are excluded. |
| `Nonvanishing` | Only finite endpoints impose polynomial evaluation conditions; infinity carries no artificial finite value. |
| `Domain` | Includes nonzero interpreted head, squarefreeness, strict endpoint order and nonvanishing at both finite endpoints. Successful endpoint checks alone do not establish squarefreeness. |
| `endpoint_lt` | Uses subtraction preservation and the supplied negative-sign equivalence. No field/order instance is asserted on storage. |
| `endpoint_nonvanishing` | Horner correspondence and zero-sign reflection justify the executable guard; it omits unused order/inverse premises. |
| `checkEndpoints_iff` | Characterizes exactly the nonzero-head and endpoint guards. Squarefreeness is deliberately absent from this intermediate contract. |
| `normalize_eq` | Requires a nonzero polynomial, zero reflection, multiplication/negation/inversion preservation and the negative-sign law. These give the positive factor and scaling identity, including negative leading coefficients; positivity alone uses no inversion. The normalization does not force monic entries. |
| `chain_checks` | Applies the shared producer theorem to the actual normalization and nonzero head. It does not assume successful example outputs or oracle-produced witnesses. |
| `query_isSome` | Characterizes the actual producer's success on arbitrary query polynomials over an ordered target field. Storage needs neither injectivity nor a field instance. |
| `prepare_isSome` | Transfers the same domain characterization through operational preparation/query agreement. |
| `prepare_sound` | Combines semantic domain validity and literal sign/head/endpoint bindings of a successful prepared result. |
| `prepared_domain` | Any prepared object has the mathematical domain under a lawful interpretation of its bound sign function. The exact sign-function equality is essential. |
| `withEndpoints_isSome` | Characterizes retargeting on the new interval, using fresh preparation agreement rather than old endpoint evidence. |
| `withEndpoints_domain` | Validates the returned object's head at the requested new endpoints; core bindings separately retain its sign and chain. |
| `certify_checks` | Actual produced certificates pass literal replay. The explicit three-valued sign bounds supply the checker range guards. Its successful-output premise is paired with separate producer-domain theorems. |
| `certifyPrepared_checks` | A prepared object and matching semantic sign bind accepted replay to the caller's exact context and query. |
| `certifyCountPrepared_checks` | Query-one chain reuse still passes the complete checker at current endpoints and context. It reuses the full prepared-certificate law. |
| `check_domain` | Arbitrary accepted replay gives domain validity through the supplied squarefree witness and endpoint checks. It needs no producer equation or storage inversion. |
| `orderSign_spec` | Canonical ordered coefficients supply positivity, negativity, zero and range laws. The result does not require ordered-ring compatibility for the three-way comparison itself. |

## Soundness

General value contracts require an ordered real-closed target; the
domain-only `rootCount_isSome` explicitly omits real-closedness. Arbitrary
accepted replay needs no negation/inverse dictionary on storage, while actual
query production requires their preservation laws.

| Declaration | Assessment |
| --- | --- |
| `orderSign_eq` | Identifies the canonical executable sign with the mathematical sign using only ordered comparison and zero. |
| `sign_spec` | Semantic sign agreement supplies all four domain/checker sign facts without unrelated coefficient arithmetic or real-closedness hypotheses. |
| `check_sound` | Accepts arbitrary supplied certificates and proves domain plus signed root sum. There is no producer-provenance premise. Literal bindings remain supplied by the checker. |
| `queryPrepared_sound` | Derives the prepared query value by applying arbitrary-certificate soundness to its actual accepted produced certificate. The sign-function binding is explicit. |
| `countPrepared_sound` | Converts prepared query one to the cardinality of distinct roots in the current open interval. It does not count multiplicities. |
| `countPrepared_nonneg` | Establishes nonnegativity of the actual integer answer before natural conversion. |
| `query_sound` | Extracts the actual certificate from successful query production and applies its acceptance/soundness laws. This value-only projection remains useful beside `query_spec`. |
| `query_spec` | Adds the successful producer's domain to its value contract, retaining the same original head, query and endpoints. |
| `query_iff` | Gives both directions: a lawful domain and its root-sum value force the producer to return that value. This includes general production, not just accepted-output soundness. |
| `query_count` | Query one is the distinct-root cardinality by unit preservation and the shared root-sum-one theorem. |
| `query_nonneg` | Justifies the signed-to-natural conversion from the actual produced answer. |
| `query_bound` | Bounds absolute query value by root cardinality and then head degree; it uses zero-reflecting polynomial degree correspondence. |
| `query_sign` | On an explicitly singleton semantic root set, the signed sum equals the query's sign at that same root. It does not independently select another root. |
| `rootCount_eq` | Natural count equals the semantic cardinality by recovering query one and proving the conversion exact. |
| `rootCount_isSome` | Characterizes natural-count success on the same domain as query one; this domain-only contract needs no real-closed target. |
| `rootCount_query` | Retains both actual natural-count production and exact casting back to the successful integer answer. |
| `rootCount_map` | Whole-Option agreement includes failures and lawful successful values, so conversion does not silently replace a valid signed answer. |

## Reduced

| Declaration | Assessment |
| --- | --- |
| `queryReduced_eq` | Whole-Option equality with the original query uses lawful storage division, interpretation of the remainder and equality of query values at head roots. It includes identical domain refusal. |
| `queryReducedPrepared_eq` | The same value agreement applies to the actual prepared object and matching sign interpretation. Its own axiom guard checks the theorem's ordinary-kernel boundary. |

## Compare

These contracts compare actual chain/checker behavior over an ordered field;
they do not require a real-closed target or assume a shared coefficient
representation.

| Declaration | Assessment |
| --- | --- |
| `signs_eq` | Equal-size positively corresponding chain entries give identical sign arrays at corresponding finite or infinite endpoints. Strict positive factors prevent a sign flip; bounds/negative/zero laws bind each sign operation. |
| `check_congr` | Two arbitrary accepted certificates give equal values with positively scaled interpreted head/query inputs and matching interpreted endpoints. Context types and chain normalizations may differ. Each certificate still has its own literal bindings. |
| `domain_congr` | Head scaling only needs a nonzero factor: squarefreeness, roots and endpoint nonvanishing are unchanged even by negative scaling. This weaker premise is appropriate for domain alone. |
| `query_congr` | Combines domain equivalence with accepted-producer certificate comparison. Both failure and success cases are covered; positive query scaling is stronger than mere domain invariance. |

## Rational

Finite dyadic intervals are required by the integer frontend. These statements
do not extend denominator-clearing agreement to arbitrary rational endpoints
without an endpoint representation witness.

| Declaration | Assessment |
| --- | --- |
| `toPolyℝ_clearDenominators` | The cleared integer polynomial is the original rational interpretation times its positive clearing factor. Coefficient correspondence supplies the identity. |
| `query_rat_domain` | Rational and integer producers have the same success domain after positive clearing; this theorem alone says nothing about successful-value equality. Query clearing is unconstrained by domain validity. |
| `signs_rat_eq` | Positive chain-entry correspondence preserves finite dyadic endpoint sign arrays, using exact rational/dyadic evaluation laws. |
| `check_rat_value` | Arbitrary accepted rational and integer certificates give the same value. Their literal witnesses need not agree and neither is assumed to be produced. |
| `query_rat_eq` | Whole-Option agreement combines domain correspondence with actual producer acceptance and arbitrary-certificate value comparison, including common factors and zero initial remainders. |
| `query_rat_count` | Transfers rational query one through positive clearing to the existing real-root count. Clearing unit and nonzero head scaling preserve the root multiset used by the integer result. |
| `rootCount_sturm` | Successful counting supplies squarefreeness and root-free endpoints; the open count agrees with the legacy half-open count there. The proof handles nonconstant and nonzero constant heads separately, and imposes no positive-degree premise on callers. |
| `query_rat_rootSum` | Connects query-one cardinality to the shared open distinct-root sum at the same dyadic endpoints. It does not generalize to arbitrary weighted queries by this theorem alone. |
| `query_rat_nonneg` | Supplies natural-conversion evidence through the specialized real count, without needing the abstract real-closed-field query foundation in its proof. |

## IntCast

Names are relative to `HexSturmMathlib.IntCast`.

| Declaration | Assessment |
| --- | --- |
| `map_toRatPoly` (private) | The generic zero-reflecting map equals the existing integer/rational polynomial conversion coefficientwise. |
| `interpret_map` (private) | Embedded coefficients have the same real polynomial interpretation; it is used for finite evaluation signs. |
| `sign_int` (private) | Coefficient signs agree exactly under integer embedding, with three-valued bounds ruling out unrelated negative tags. |
| `sign_dyadic` (private) | Equal real values give identical rational and dyadic three-valued signs; the semantic equality premise is retained. |
| `compare_eq` (private) | Endpoint subtraction correspondence gives the exact executable comparison after dyadic embedding. |
| `evalSign_eq` (private) | Polynomial interpretation and Horner correspondence give identical finite endpoint evaluation signs. |
| `certificate_checks` | Any accepted integer certificate embeds to accepted rational replay with the same context/value and mapped finite or infinite endpoints. It uses no producer hypothesis. |

## DenominatorClearing

Names are relative to `HexSturmMathlib.DenominatorClearing`. The private
helpers are used in the public translation proofs; they do not form an
alternate chain implementation.

| Declaration | Assessment |
| --- | --- |
| `step_pos` | Positive input clearing factors and positive source step scales give positive integer step scales. This is separate from the unconditional scaling identities. |
| `cast_num` (private) | Expresses a rational numerator as its value times the stored denominator for exact scalar translation. |
| `step_spec` | Gives all three common-multiplier identities without positivity assumptions on the supplied natural factors; zero factors are allowed. |
| `clear_size` (private) | Positive denominator clearing preserves stored polynomial size, supporting nonzero and degree guards. |
| `clear_zero` (private) | Preserves the zero lookup default needed when a chain index is out of range. |
| `chain_entry` (private) | Handles both valid indices and default entries, making subsequent guards independent of an unjustified in-range assumption. |
| `step_terms` (private) | Translates each term of a scaled polynomial identity by the same multiplier; it exposes the algebra needed by both initial and remainder steps. |
| `step_add` (private) | Preserves additive identities for initial and terminal evidence. |
| `step_sub` (private) | Preserves the subtractive signed-remainder identity rather than replacing it with an unsigned remainder equation. |
| `rat_interpret` (private) | Identifies identity interpretation with the ordinary rational polynomial conversion used by the translated identities. |
| `int_interpret` (private) | Identifies integer interpretation in the rationals with the existing integer polynomial conversion. |
| `step_checks` (private) | Translates acceptance of the actual supplied rational step to acceptance of the corresponding integer step, preserving positivity and the signed identity. |
| `subIsZero_int` (private) | Reflects the integer subtraction test as equality of rational interpretations. |
| `initial_checks` (private) | Includes both head and query factors in the query-times-derivative identity; scaling only the head would be insufficient. |
| `terminal_checks` (private) | Translates supplied positive-scale divisibility evidence without computing a new quotient or assuming a constant last entry. |
| `chain_checks` | Preserves complete supplied-chain acceptance, including singleton chains, zero initial remainders and nonconstant terminal entries. A separate constant-terminal guard is still needed for squarefreeness. |
| `guards` (private) | Positive head clearing retains nonzeroness and both finite endpoint guards. The ordered dyadic interval supplies its endpoint order. |
| `lastIsConstant_eq` (private) | Preserves the separate squarefree witness's constant-terminal check through size preservation, not through a recomputed gcd. |
| `signs_eq` | Every translated chain has identical finite endpoint sign arrays under positive entry clearing, independently of producer provenance. |
| `certificate_checks` | Full accepted rational replay translates to full accepted integer replay with the exact original context/value. It combines translated guards, both supplied chains, the squarefree terminal test and renewed sign arrays. |
