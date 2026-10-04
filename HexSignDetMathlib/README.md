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
or query semantics; their composition with finite query interpretation is
described below.

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
`foundation_moments` and `System.foundation_counts` apply Tau Ceti's finite
moment and count-recovery theorems to the actual ordered vectors. List positions
index the observations, preserving repeated conditions. Coverage is supplied
separately from the accepted matrix identities; the supplied scaled integer
inverse interpreted over the rationals provides the foundation's left inverse.
`Replay.foundation_complete` specializes the existing split-tree induction
to this bridge at every solve. Leaves and child support products supply
candidate coverage before that node is solved or pruned; shared query
semantics supply the actual moments. Root support, counts, sparse lookup
and selected-root signs
consume that specialization. No coefficient representation is made into
a field, and the executable checker gains no companion dependency.
The companion's finite-system and counted-node producer proofs use the same
imported moment and count-recovery bridges.
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
theorems concern successful tree construction. They do not assert
arbitrary-certificate root-sum soundness.
`buildNode_complete` supplies the finite assembly step for both rational and
scaled solving: a checked candidate system, a matching supplied inverse when
present, and equality of its values with the actual prepared queries produce
a node with exactly its counts. Candidate support and query-value semantics
must be established independently; neither follows from this assembly lemma.
`Node.parent_system` transports the finite child-product system to the exact
list-length dimension used by `buildTreeFrom`, retaining literal row/column
orders, counts, values and denominator. Its inverse is the shared
`parentInverse` definition called by the actual parent construction, so the
dimension transport and inverse witness cannot drift between those sites.

`buildTreeFrom_complete` connects these steps through the actual balanced
recursion. `QueryValues` states the finite interpretation of the actual prepared
query on every valid exponent row, using the actual preprocessing and reduction.
`QueryModel` requires this interpretation along the same query/preparation
slices as the constructor, restricting finite observations with multiplicity.
It mentions no output tree, support completeness, inverse, count correctness,
solver success or accepted replay. Given that model and well-shaped observations,
the theorem constructs a successful tree with exact counts, complete retained
support and interpreted moment values at every node. Leaf systems and complete
child supports provide the candidate systems before each solve, including empty
observations and zero-dimensional parent products.
`buildTree_complete` handles shared root preprocessing; `buildPrepared_complete`
composes the induction with independent algebraic replay acceptance under the
ordinary generic coefficient laws. The universal noncanonical instantiation and
exact standard-axiom inventories are checked in conformance. An ordinary-kernel
constant-head probe accepts an empty observation model and rejects a falsely
claimed root using the actual constant query value.
`Descriptor.build_ok_ofPrepared` isolates the finite constructor's only
internal failure path; `Descriptor.build_noError` uses actual root-query
interpretation to rule that path out for lawful coefficient fields. The theorem
does not by itself classify the input diagnostics.
`Descriptor.build_of_unique_root` additionally proves that a well-formed raw
descriptor with exactly one matching real root is produced by the actual
constructor. The result retains the exact raw input by `Descriptor.build_raw`.
`Descriptor.build_success_iff` gives the converse and characterizes successful
construction by exact context, well-formedness, mathematical domain validity
and a unique matching root.
`Descriptor.validate_success_iff` transfers this exact criterion to the public
option-valued validator, and `Descriptor.validate_success_formal` states it with
formal iterated derivative signs. The diagnostic constructor remains available
to callers.
`RawDescriptor.querySigns` identifies the executable query word with signs of
formal iterated derivatives at every point. `Descriptor.build_success_formal`
states the same success criterion using those formal derivatives.
The Mathlib-free `build_context`, `build_domain` and `build_malformed` lemmas
identify their corresponding input diagnostics without appealing to root
semantics. `build_valid_cases` completes the classification on valid, well-formed
inputs: zero matching roots yield `.absent`, one yields a descriptor, and more
than one yields `.ambiguous`.
The existing `HexSignDet.Conformance` cases run the recursive producer on
two and twelve queries with independently supplied sign counts, including a
root-free constant head. The finite theorem applies to those same construction
paths when its query-value model is established.

The model is a finite proof boundary, not an executable argument. In the development-only
`HexQuerySemantics` target, `RootModel` interprets arbitrary accepted node and
child query evidence as moments of actual roots, then proves exact support and
counts for every sign condition, including omitted ones. `RootProducer` derives
the finite query model for the actual prepared producer and proves its success
and counts from the shared proved root-sum statement. `SelectedRoot` proves that
accepted count-one partial and full descriptors select a unique root, and
`root_derivatives` identifies their signs with formal iterated derivatives
through `derivativesFrom_get`. `SelectedSigns.values_at_root` and
`value_at_root` prove that every checked requested sign equals evaluation at
that same selected root, including the public one-query accessor.

`Dag.selectedSigns_values` applies this correspondence to an arbitrary supplied
BKR graph and claimed sign vector. Accepted graph replay retains its literal
query evidence; every claimed sign equals evaluation at the original descriptor's
selected root. The executable graph and byte interfaces remain Mathlib-free.
The compiled `hexsigndet_field_checks` executable exercises graph memo
selection, byte decoding and replay of existing producer evidence;
`HexSignDet.CrossCheck` checks literal acceptance and rejection in the
ordinary kernel.

`TableProducer` proves success of `buildTablePrepared` and the ordinary total
`determinePrepared` API under the same coefficient-interpretation laws. Its
correctness theorem relates every lookup to the cardinality of the actual
root/sign condition, including omitted words, empty queries and root-free
domains. `determine_isSome` proves that the option-valued frontend succeeds
exactly on the shared valid root domains; this validity result does not use the root-sum
theorem. `determine_correct` gives all returned root counts and uses the
shared proved root-sum theorem, as do the producer-success results. These proofs follow
the actual prepared BKR producer and
exclude its internal-error fallback, without assuming successful construction
or injectivity of coefficient representations.

`Completion.root_eq_source` proves that accepted full-derivative completion
preserves the selected real root; `Completion.signs_at_source` identifies every
returned derivative sign at that original root. These results use checked
count-one tables and derivative identities without assuming Thom order.
`CompletionProducer` proves `Descriptor.buildCompletion_success` for every
validated descriptor under the existing lawful coefficient interpretation.
It constructs the prepared full-derivative BKR table and proves that exactly
one count-one row restricts to the source's partial word, excluding every
internal error of the actual producer. Empty partial words are included.
`Descriptor.complete_correct` proves that the total accessor preserves the
original selected root, retains literal source bindings and returns all formal
derivative signs in canonical slot order. No injectivity of coefficient
representations or Thom ordering theorem is required. These semantic results
depend on the same shared proved root-sum theorem.
`Reencoding.root_eq_source` proves that checked re-encoding keeps that real root
when the defining polynomial and interval change. Its proof uses the copied
equation, derivative word and strict endpoint signs, plus acceptance of the
source descriptor to rule out impossible infinite endpoint orientations.
`Descriptor.constraints_iff` proves that the defining equation, selected
formal-derivative signs and strict finite endpoint queries used by re-encoding
identify exactly the source root. `Descriptor.buildReencoding_absent` in
`HexSignDetMathlib.ReencodingProducer` proves that the actual constructor
returns `none` if that root is absent from the target domain, establishing
preparation and joint table construction from the input. These results use no
separating interval, Archimedean or injective representation assumption and
use the shared proved root-sum theorem.
`Descriptor.buildReencoding_invalid` separately proves ordinary absence for
invalid mathematical target domains, even if their open-interval root set
contains the source root. It uses shared preparation correspondence and has
no root-sum theorem dependency.
`Descriptor.buildReencoding_congr` proves success when a target defining
polynomial has a zero difference from the source polynomial, even if their
stored coefficients differ. Its valid target domain must contain the selected
root and have its roots contained in the original domain. The proof establishes
preparation and both actual producers and preserves that root using the source
partial selection's uniqueness. `RawDescriptor.full_congr` supplies agreement
of the freshly reconstructed derivative signs under mathematical polynomial
equality. Literal head, context and endpoint checks still require fresh evidence.
`Descriptor.buildReencoding_refinement` specializes this result to the same
stored head. Neither result needs general Thom injectivity or rational isolating
bounds; both use the shared proved Sturm–Tarski theorem.
`Descriptor.buildReencoding_success` in `HexSignDetMathlib.ThomReencoding`
proves actual success and root preservation for any valid target head and
interval containing the source root. Neither equality of defining polynomials
nor containment in the old interval is required. Tau Ceti Thom injectivity
makes the target full word count one; the source equation, partial derivative
word and endpoint constraints select the original root in the joint table.
Conformance re-encodes the actual cubic value into a quadratic head with an
additional root, rejected only by the source equation or only by the old
interval. A specialization also uses noninjective coefficient storage.
`Descriptor.convert_success` and `Descriptor.convert_root` in
`HexSignDetMathlib.Convert` prove that rebuilding a descriptor after a
value-preserving coefficient and context change succeeds and preserves its
selected root. The source's count-one condition transfers through the two
lawful interpretations; target derivatives are freshly reconstructed, not
copied. The coefficient converter need not preserve arithmetic as literal
representations. Both carriers may be noninjective, and finite/infinite bounds
are included. No general Thom injectivity, Archimedean assumption or field
instance on representation coefficients is required. These results use
the proved shared Sturm–Tarski theorem.
`Descriptor.root_map` in `HexSignDetMathlib.Embedding` proves that interpreting
the same validated descriptor through an ordered embedding of real closed
fields selects the image of its original root. The two coefficient
interpretations must agree through that embedding. `Descriptor.root_comp`
specializes this result to their composition and derives the target arithmetic
and sign laws. These results include partial encodings, noninjective stored
coefficients and finite or infinite endpoints. They change the semantic field;
changes to stored coefficients or literal contexts still use checked conversion.
`Comparison.eq_iff_root_eq` proves that a successful common-product comparison
returns equality exactly when the original selected real roots coincide. It
uses the common full derivative word and count-one descriptors.
`Comparison.order_root` identifies all three returned orders with the order of
the original selected roots, using their root-preserving re-encodings and the
actual full-word comparator theorem.
The executable API retains its internal diagnostics for arbitrary coefficient
operations. The companion rules out selected-sign, completion, enumeration and
comparison errors under lawful coefficients. The domain-exact total table
wrappers are available.

`Descriptor.buildSigns_success` proves that the actual selected-sign producer
succeeds for every validated descriptor and finite ordered query list under
the shared lawful coefficient interpretation. `Descriptor.signs_rows` shows
that the complete joint table has exactly one count-one row extending the
descriptor's derivative signs. Domain validity supplies preparation, and
`buildPrepared_roots` supplies the actual table before its final guards are
discharged by the Mathlib-free `buildSigns_ofTable` theorem.
`Descriptor.buildSigns_roots` identifies the returned signs with evaluation at
the original selected root, including empty and repeated queries. These
results use the shared proved root-sum theorem, without a Thom order assumption.
`Descriptor.signAt_success` proves that the public total single-query operation
uses an actual successful checked result and never its diagnostic error fallback.
`Descriptor.signAt_correct` equates its integer with the evaluation sign at the
original selected root, also relative to the shared proved root-sum theorem. Neither the
operation nor these theorems require an
injective coefficient representation; the executable uses ordinary operations
and carries no companion field-law package.
The cubic-field checks use ordinary `QAdjoin` arithmetic over ℚ(∛2) and
retain the selected real embedding. They reject changed sign vectors and query
order in selected-sign replay, and test context, defining-polynomial and
derivative-slot rejections in both descriptor validation and selected-sign
replay.

`QueryHandle` proves that `Descriptor.prepareQueries` succeeds for every
validated descriptor under the same coefficient-interpretation laws. Prepared
singleton and joint queries use exactly the existing selected-sign producer
and retain the original root, empty/repeated query positions and zero signs.
`QueryHandle.signAt_correct` identifies the cached total result with evaluation
at that root, and `signAt_success` excludes its diagnostic fallback. These
semantic guarantees use the shared proved root-sum theorem. The finite producer/result
agreement proofs have only the standard kernel axioms. Actual cubic-field and
noncanonical-carrier conformance rejects copied evidence after context,
interval, selected-word and semantically equivalent representation changes.
Only preparation is retained; joint table construction and replay still run
for each query list.

`RootList` proves `Descriptor.buildRoots_coverage`: every successful actual
root list contains every mathematical root in the requested interval exactly
once. The proof uses the actual complete table, preserved full sign words and
uniqueness of each accepted descriptor. It does not assume rational separators
or injective coefficient representations. It uses the shared proved root-sum
theorem. `Descriptor.buildRoots_empty` proves actual success with an empty list on
valid root-free domains; `buildRoots_constant_success` covers nonzero constant
heads. `buildRoots_subsingleton` proves actual success on valid domains
containing at most one mathematical root, including linear heads and isolating
intervals. `buildRoots_linear` supplies the degree-one corollary directly. Table
production success and the root counts use the same root-sum theorem throughout;
none of these success proofs needs a Thom theorem.
`buildRoots_none_iff` characterizes invalid mathematical domains exactly,
and `buildRoots_domain` proves validity of the original input without using the root-sum theorem.
`Descriptor.buildRoots_success` in `HexSignDetMathlib.ThomRoots` proves actual
success on every valid domain, not just domains containing at most one root.
`RawDescriptor.full_fiber` derives count one for every realized row, table-word
distinctness excludes duplicate insertion, and `Descriptor.fullOrder_root`
discharges every actual comparison guard. `Thom.insert_success` and
`rootsFromTable_success` follow the existing recursive operations.
`Descriptor.buildRoots_ordered` interprets the existing finite sorting result
as strict mathematical order. `Descriptor.buildRoots_roots` combines actual
success, exact coverage, no duplicates and strict ordering. Constants and
finite/infinite endpoints are included. The generic interpretation admits
noninjective coefficient storage and any real closed target field, including
non-Archimedean ones. `Descriptor.buildRoots_isSome` states actual success iff
the original domain is valid, supplying the SPEC’s `roots_isSome` contract;
`buildRoots_roots` supplies its `roots_correct` contract.
Conformance enumerates the three roots of a cubic over ℚ(∛2), including a
zero derivative sign, reports empty results for constants and invalid domains
separately, and enumerates 0 and ε using actual ordered rational-function
coefficients, checking their selected signs and order and rejecting a changed
context. These roots have no rational separator.

`CommonProduct.check_roots` proves the root-union property from arbitrary
accepted literal multiplication/division identities under noninjective coefficient
interpretation. It neither assumes a gcd normalization nor supplies squarefreeness;
the latter remains a separate shared-domain check. `endpoint_eval`, `endpoint_lower`
and `endpoint_upper` prove the semantics of the actual finite-boundary polynomials
used by joint re-encoding.

`HexSignDetMathlib.Thom` connects the actual reconstructed derivative words to
Tau Ceti's Thom identity and strict order theorems. `RawDescriptor.full_unique`
proves uniqueness among roots of a nonzero head; `full_fiber` gives each
realized full word count one. `full_order` proves that the existing recursive
largest-differing-index comparison always returns the mathematical order.
`Descriptor.fullOrder_root` proves the same result for the guarded public
comparison on applicable validated full descriptors. Polynomial Rolle is
proved from the real-closed-field axioms by Tau Ceti; it is not supplied as an
extra assumption. These results cover non-Archimedean fields and noninjective
coefficient storage without rational separators or a field instance on stored
coefficients. Conformance checks the actual foundation and bridge axiom
inventories with the ordinary kernel.

`HexSignDetMathlib.ComparisonProducer` proves that the actual common-product
comparison succeeds for every pair of validated descriptors in one context.
`CommonProduct.build_success` proves acceptance of the actual gcd/division
record and identifies its head with the least common multiple up to a unit.
`build_squarefree` supplies squarefreeness from the two source domains.
`Descriptor.buildReencoding_full` proves that successful production supplies
canonical full words, a property not assumed for arbitrary accepted re-encodings.
`Descriptor.compare_success` excludes the total operation's diagnostic fallback;
`compare_correct` and `compare_eq_iff`, `compare_lt_iff`, `compare_gt_iff` give
its mathematical meaning for the original roots. The generic laws explicitly
include preservation of ordinary division and do not impose a field instance
or injective interpretation on stored coefficients.

Actual coefficient/context and graph byte roundtrips are proved by the
computational codec laws. Cross-level coefficient-sign dependencies and
sharing, remaining conformance/examples and Phase-4 evidence remain required. Root-sum/replay soundness follows from the shared
proved theorem; finite BKR proofs consume Tau Ceti moment/count recovery, and
root identity and strict comparison consume Tau Ceti Thom theorems.
See the
[specification](SPEC/hex-sign-det-mathlib.md) for the complete assignment.

Computational checks over genuine number fields (the cubic field ℚ(∛2), the
quartic common field of √2 and √3, noninjective rational storage and nested
infinitesimal fields) are compiled and run natively by the Mathlib-free
`hexsigndet_field_checks` executable (`conformance/HexSignDet/FieldChecks.lean`).
`conformance/HexSignDetMathlib/FieldConformance.lean` instantiates each producer
correctness theorem once at ℚ(∛2) or the noninjective carrier, with axiom
inventories.

```sh
lake build HexSignDetMathlib +HexSignDetMathlib.Conformance +HexSignDetMathlib.FieldConformance
lake build hexsigndet_field_checks && .lake/build/bin/hexsigndet_field_checks
```
