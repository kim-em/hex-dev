# hex-sign-det-mathlib

Algebraic correspondence for BKR moment reduction over the shared coefficient
interpretation. This development companion is not yet released.

`ReductionStep.check_sign`, `Reduction.check_sign` and `checkMoment_sign` prove
that arbitrary accepted reduction evidence preserves the full moment's sign at
every root of the head polynomial. They use checked zero-difference identities
and positive scales, with no field instance or injectivity assumption on the
coefficient representation.

`ReductionStep.build_checks` and `Reduction.build_checks` prove acceptance of
the actual producer using the shared pseudo-division and normalization
correspondence. No parallel polynomial algorithm or root-sum premise is used.
Conformance includes universal noncanonical instantiations, literal ordinary
kernel acceptance/rejection, and theorem axiom inventories.

`QueryReduction.build_checks` proves acceptance of the actual shared query
preprocessing. `QueryReduction.check_signs` proves preservation of the complete
indexed sign vector for arbitrary accepted witnesses. `Node.check_sign` composes
this fact with reduced-moment replay, identifying the sign of each actual Tarski
operand with the original moment. The finite `slice_checks` theorem verifies
the child-sublist restrictions used by the producer without rerunning division.

`derivativesFrom_get` identifies every emitted descriptor derivative with the
formal iterated derivative under the shared interpretation, using explicit
natural casts. It does not require a field instance on coefficient storage.

`System.retained_rank` proves that removing zero-count columns preserves full
column rank. `basis_checks`, `basis_rank`, `basis_columns` and `basis_inverse`
verify the actual integer rank producer's retained basis, exact column order
and scaled left inverse. `Node.basis_matrix` identifies the selected minor
with its actual retained exponent/sign vectors. `Node.product_inverse` proves
the tensor witness identity and identifies both vector orders with the exact
list products used by `buildTreeFrom`. `solveScaled_eq`
proves that the integer solver recovers any accepted system's counts without
rounding or sign clamping. These finite algebra results do not assume roots
or query semantics and do not yet prove completeness of the full constructor.

`solveSystem_complete` proves that the actual rational solver also succeeds
on every accepted integer system, preserving its input orders and exact counts.
It uses the core rank theorem at the executable rational field instance, then
proves positivity and divisibility of the chosen denominator and its literal
integer inverse identity. The shared denominator encoder has corresponding
acceptance and decoding proofs in `HexMatrixMathlib.Rational`.
`System.check_counts` constructs a checked system from finite observations
covered by its candidate support. `empty_system` and `singleton_system` provide
the two complete leaf systems, with their explicit inverses checked by the
ordinary kernel before any solving or pruning.
`system_counts` requires only the literal shape guards, a scaled inverse and
complete support: column distinctness, nonnegative counts and both system
identities follow from those inputs.
`Node.product_system` applies this construction to the actual child bases and
their Cartesian product, deriving all parent-system checks from complete
child supports without assuming an accepted parent.

`buildNode_spec` and `buildNode_evidence` connect successful construction to
its exact context, domain, ordered rows/columns, retained rank certificate,
indexed reductions and prepared query certificates. `buildNode_checks` proves
local replay acceptance under the shared generic coefficient interpretation
laws, using the existing prepared-query and reduction producer theorems.
`buildTreeFrom_checks` propagates accepted preprocessing slices and child
evidence through the actual balanced recursion. `buildTree_checks` and
`buildPrepared_eq` show that successful tree construction passes the final
replay guard, including noncanonical coefficient representations. These
theorems do not establish that tree construction always succeeds: excluding
all finite solving failures and interpreting query values remain separate
obligations. They do not assert arbitrary-certificate root-sum soundness.
`buildNode_complete` supplies the finite assembly step for both rational and
scaled solving: a checked candidate system, a matching supplied inverse when
present, and equality of its values with the actual prepared queries produce
a node with exactly its counts. Candidate support and query-value semantics
must be established independently; neither follows from this assembly lemma.
`Node.parent_system` transports the finite child-product system to the exact
list-length dimension used by `buildTreeFrom`, retaining literal row/column
orders, counts, values, denominator and its transported tensor inverse. Thus
the parent construction and the node assembly lemma use the same dimension
and inverse witness.

`CommonProduct.check_roots` proves the root-union property from arbitrary
accepted literal multiplication/division identities under noninjective coefficient
interpretation. It neither assumes a gcd normalization nor supplies squarefreeness;
the latter remains a separate shared-domain check. `endpoint_eval`, `endpoint_lower`
and `endpoint_upper` prove the semantics of the actual finite-boundary polynomials
used by joint re-encoding.

Complete sign-table and Thom semantics, total producer correspondence and
Phase-4 evidence remain required. The root-sum/replay bridge in #10389 and the
specified Tau Ceti BKR/Thom foundations remain separate proof gates; the
polynomial identities above do not discharge them. See the
[specification](SPEC/hex-sign-det-mathlib.md) for the complete assignment.

```sh
lake build HexSignDetMathlib +HexSignDetMathlib.Conformance
```
