# Computational declarations

Names are relative to `Hex.Sturm` except in the transport module. These are
source assessments of the [manifest's modules](manifest.json), not inferred
reference counts or phase attestations.

## Basic

| Declaration | Assessment |
| --- | --- |
| `orderSign` | Exact three-way branching for canonical ordered storage; interpreting it as the mathematical sign is a separate companion law. |
| `normalize` | Chooses the leading-coefficient magnitude through the explicit sign operation and scales by its inverse. Positivity and sign preservation require a lawful interpretation and nonzero polynomial; no positive-leading convention is imposed. |
| `PreparedDomain` | The private constructor binds sign, head, excluded endpoints, endpoint guards, a constant-terminal squarefree witness and its exact producer equation. Runtime validation is not an unconditional field theorem about arbitrary operations. |
| `PreparedDomain.ofChecked` | Reconstructs from those exact premises; merely checking some alternate chain does not supply its producer equality. The sign operation and chain are retained literally. |
| `PreparedDomain.ofChecked_data` | Exposes all five data fields together, independently of the constructor representation. |
| `PreparedDomain.ofChecked_sign` | A terminating simp projection retains the endpoint guard's exact sign function. |
| `PreparedDomain.ofChecked_head` | A terminating simp projection retains the original polynomial, rather than an equivalent scaled head. |
| `PreparedDomain.ofChecked_lower` | A terminating simp projection exposes the excluded lower endpoint. |
| `PreparedDomain.ofChecked_upper` | A terminating simp projection exposes the excluded upper endpoint. |
| `PreparedDomain.ofChecked_squarefree` | A terminating simp projection exposes the actual stored chain, not a newly computed witness. |
| `PreparedDomain.ofChecked_eq` | Restoring an existing object preserves the complete prepared value. This supplies reconstruction without requiring its private constructor in callers. |
| `PreparedDomain.withEndpoints?` | Reuses head, sign and chain while checking new endpoints. Old endpoint proofs cannot justify a different interval. |
| `PreparedDomain.withEndpoints_isSome` | Gives the exact Boolean success condition for the new endpoint guards; no semantic sign laws are silently introduced. |
| `PreparedDomain.withEndpoints_bindings` | Successful retargeting preserves head, sign and chain and binds both new endpoints. This is a literal-data law, not just value equivalence. |
| `prepare` | Validates endpoints before producing the query-one chain and requiring a nonzero constant terminal entry. The query polynomial is absent from domain preparation. |
| `prepare_ofChecked` | Supplied exact producer evidence identifies restoration with preparation. The constructor body does not execute preparation to rebuild the stored chain. |
| `PreparedDomain.withEndpoints_eq` | The whole returned Option equals fresh preparation at the new endpoints, using the retained producer equation and terminal guard. The executed retargeting body still reuses the chain. |
| `prepare_eq_some` | Exposes successful preparation's exact sign/head/endpoint bindings; it does not substitute semantic coefficient equality. |
| `queryPrepared` | Reuses the squarefree chain and builds the query's remainder chain. Reusing preparation does not avoid query-specific work. |
| `certifyPrepared` | Produces the same query evidence with the caller's literal context; context ownership is explicit. |
| `certifyCountPrepared` | Uses the stored query-one chain in both certificate positions and recomputes endpoint signs. It retains the caller's context and current interval. |
| `countPrepared` | Returns a signed integer directly. Consumers need semantic nonnegativity before a natural-count conversion. |
| `countPrepared_eq` | Proves value agreement with prepared query one using the stored producer equation, rather than assuming two independent chains coincide. |
| `certifyCountPrepared_eq` | Proves full certificate agreement with prepared query one, including context and endpoint data. |
| `certifyPrepared_value` | Query value is independent of the certificate's context label; the label remains relevant to replay. |
| `query` | Delegates to the shared producer with finite/infinite endpoint signs and the chosen normalization. Domain failure remains explicit in Option. |
| `rootCount` | Maps query one through `Int.toNat`; preservation of lawful answers depends on the companion's nonnegativity and map laws. Arbitrary sign/operation dictionaries do not make negative values valid counts. |
| `certify` | Produces certificates with literal context, polynomial and endpoint bindings, retaining the same domain failure as queries. |
| `certify_value` | Whole-Option agreement includes failures and successful values; changing the certificate context does not change query value. |
| `query_prepared` | Every retained prepared object supplies successful querying on its own bound inputs. Its stored endpoint and producer proofs exclude the ordinary domain failure. |
| `certify_prepared` | Gives whole certificate equality, not merely equal output values. This connects retained preparation to ordinary production. |
| `prepare_isSome` | Preparation and querying have exactly the same success domain for any query polynomial. This law is operational and precedes semantic domain correspondence. |
| `check` | Replays a supplied certificate through the shared finite checker; producer provenance is not a precondition. |
| `checkCached` | Allows reuse of a checked domain but retains full replay on cache misses and different witnesses. |
| `checkCached_eq` | Whole checker equality is the cache characterization; using a cache cannot weaken acceptance. |
| `check_bindings` | Accepted replay supplies all six literal bindings: context, head, query, endpoints and value. It does not authenticate a semantic interpretation supplied separately by the consumer. |

## Reduced

| Declaration | Assessment |
| --- | --- |
| `queryReducedPrepared` | Uses the remainder-only worker before the existing prepared query. Semantic preservation needs lawful division; an unreduced certificate remains a different literal contract. |
| `queryReduced` | Checks the domain before reduction, retaining domain refusal and avoiding reduction on rejected inputs. |
| `modImpl_eq_mod` (private) | Identifies the worker with the existing remainder projection in both degree branches. It proves operational identity, without granting field laws to arbitrary storage. |
| `queryReducedPrepared_eq` | Characterizes the actual worker through the ordinary remainder API, exposing no quotient computation to callers. |
| `queryReduced_eq_query` | Whole-Option agreement with querying the remainder handles both failed preparation and its exact successful bindings. Agreement with the *original* query is a separate semantic theorem. |

## Transport

Names here are relative to `Hex`.

| Declaration | Assessment |
| --- | --- |
| `RemainderStep.clearDenominators` | Translates a supplied identity's scales and quotient using all three entry factors. It performs no new chain production or polynomial division. |
| `SignedRemainderChain.clearDenominators` | Clears every stored polynomial, recomputes degrees and translates the supplied initial, step and terminal evidence. Initial scaling includes both head and query factors. |
| `TarskiCertificate.clearDenominators` | Retains the context while renewing integer head/query data and finite dyadic endpoints/signs. The companion law requires accepted original bindings for the supplied interval. |
| `TarskiCertificate.toRat` | Maps integer evidence and dyadic endpoints, preserving stored context/sign/value data. Acceptance follows from the companion's exact sign and arithmetic correspondence. |

## DomainOperations

Names are relative to `Hex.Sturm.PreparedDomain`.

| Declaration | Assessment |
| --- | --- |
| `changeOps` | Transports a prepared object along equal dictionaries on the same carrier. All seven equalities matter to the endpoint or producer proofs; this is not a change of coefficient representation. |
| `changeOps_data` | Exposes literal sign/head/endpoint/chain preservation despite dependent instance parameters. The verbose statement retains the actual source and target dictionaries. |
| `changeOps_self` | Identity transport preserves the whole object through the public reconstruction law, without rerunning validation. |
