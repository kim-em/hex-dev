# hex-sign-det

The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-sign-det)
explains the public computation and its mathematical hypotheses with checked
examples in `hex-dev`.

Finite BKR construction and replay over the shared HexSturm prepared-query
API. This development library is Mathlib-free and is not yet released.

The library records Phase 4. The [performance report](../reports/sign-det-performance.md)
links the retained measurements, comparisons, profiles and coverage limits;
the [conformance report](../reports/sign-det-final-conformance.md) links the
independent root/sign oracles and coefficient-field examples. CI builds the
compiled benchmark and runs `list` and `verify`.

`System.check` validates the integer moment system, including exponent/sign
codes, vector lengths, distinct columns, nonnegative counts, a nonzero scaled
left inverse, and the exact moment equations. `System.unique` proves that
accepted counts are the unique integer solution. `System.mem_support` proves
that pruning retains every positive coordinate of any solution of that system;
`mem_product` supplies the elementary child-support concatenation step.

`Replay.check` accepts a finite tree of literal `Node` records. Empty-query
leaves use the one-condition system and singleton leaves use all three signs.
Internal nodes check both children on the balanced ordered query split, derive
candidate columns from their retained supports, and derive moment rows from
their retained row bases. Every node checks its supplied Tarski certificates and
HexRank certificate; an empty system obtains its domain/root evidence through
its checked children. Retained columns are computed by removing exactly the
zero counts, and the row basis preserves their order. The scaled left-inverse
identity is checked directly; no conversion from a differently ordered rank
witness is assumed.

`Replay.signOperands` gives a conservative finite list of coefficient values
whose signs determine the tree checker's result. `Replay.check_sign_congr`
proves that agreement on those signs preserves both acceptance and rejection,
including malformed supplied witnesses. The shared Tarski and chain APIs expose
`signOperands` and `check_sign_congr` too; the existing `rcf` coefficient adapter
uses these same inventories and proofs. Finite endpoints require their order
difference and polynomial evaluations; infinite endpoints require leading
coefficients. Zero is an extra conservative chain operand. These lists describe
result dependencies, not an ordered trace of runtime sign calls, and retain
repeated occurrences. A finite cache need not be lawful outside its keys, but
callers must prove agreement at every required operand before transferring the
original checker's soundness. The `Dependencies.Graph` envelope binds cross-level references to full
subjects and routes checked packet results. Consumer readers reconstruct
contexts and supply the intermediate coefficient evidence described below.
`Dag.signOperands` covers every serialized entry, including entries unreachable
from the root. `Dag.replay_sign_congr` preserves failure and the exact returned
tree under finite sign agreement; `Dag.check_sign_congr` preserves the Boolean
result. These proofs follow the actual memoized prefix fold without expanding
and rechecking a recursive tree. A cache law for the selected root's reachable
entries alone does not suffice, since graph replay checks all stored entries.
`Dag.descriptor_sign_congr` preserves the raw descriptor and literal evidence.
`Dag.decodeBytes_sign_congr`, `Dag.decodeDescriptor_sign_congr` and
`Dag.decodeSigns_sign_congr` preserve
exact errors and successful data under agreement on the actual decoded graph;
they do not prove parser/printer byte roundtrips. Callers holding a decoded graph
can use its `replay?`, `descriptor?` or `selectedSigns?` interface and the corresponding congruence
to reuse that graph without parsing the same bytes again.
Inventories retain repeated occurrences, so consumers may deduplicate
keys while proving membership covers the whole inventory.

`Dag.replay?` accepts a topologically ordered array of same-level BKR entries
and a root index. References address earlier accepted entries only. Each entry
checks its own query/matrix certificates once; both child edges still bind the
exact ordered query slices, support product, row product and fixed caller
context/head/interval. The returned tree shares accepted child values and
carries a proof of the original `Replay.check` result. Invalid unreachable
entries, forward edges, cycles and missing roots are rejected as well.
`Dag.descriptor?` consumes that proof directly, checks raw descriptor shape and
count one, and preserves the complete raw descriptor. Ordinary-kernel probes
cover the full derivative graph, repeated references to one child, selected-root
extraction and truncated/cyclic graphs.

`Dag.validate?` exposes the same checked graph fold as a reusable memo.
`Dag.select?` binds an entry index to its exact ordered queries, while
`SelectedSigns.ofMemo?` also checks the descriptor prefix and unique extending
row. Several selections can reuse one validated memo without rerunning its
query or matrix checks. Context, head and endpoints are fixed in the memo's
type. `SelectedSigns.readMemo?` supports independently constructed descriptors:
`Dag.bindDomain?` first checks literal head and endpoint equality and transports
only the proofs, preserving every stored tree. Different bindings reject.
Validation checks every entry, including unreachable entries; selection
rejects an absent index or a different query list. `Dag.selectedSigns_memo`
proves literal agreement with the existing one-result interface.
`Dag.validate_nodes`, `Dag.validate_size` and `Dag.validate_get` preserve entry
indices and nodes. `Dag.validate_expands` also preserves the full literal
subtrees and child references at every accepted index.

The conformance examples also select the roots −1 and +1 of `X² − 1` on the
whole line using opposite first-derivative signs. One validated graph then
supplies `sign X = −1` and `sign X = +1` at those independently constructed
descriptors; substituting the positive sign at the negative root rejects.

`Dag.selectedSigns?` checks a supplied graph for the descriptor's derivative
queries followed by the caller's ordered query list. It accepts exactly the
claimed sign vector when the checked table has one extending row of count one.
It reuses the checked graph's evidence without repeating tree replay or calling
a sign producer. `Dag.selectedSigns_evidence` preserves the exact claimed signs
and literal replay; `Dag.selectedSigns_checked` connects them to the existing
selected-root checker. `Dag.selectedSigns_replay` also preserves rejection of
an incorrect claim on an accepted graph, and `Dag.selectedSigns_encode` accepts
every encoded checked selected-sign tree with its exact original evidence.
`Dag.selectedSigns_encode_eq` also preserves rejection for arbitrary encoded
trees and claims. The companion's `Dag.selectedSigns_values` proves
agreement with mathematical evaluation at the descriptor's selected root.
`Dag.selectedSigns_sign_congr` transfers this result between sign functions
that agree on every stored graph operand, provided both descriptors have the
same raw root identity. Source-descriptor validation has its own coefficient
sign dependencies, which consumers must also discharge.

`Dag.encode` converts supplied trees using bottom-up hash consing. It preserves
first-occurrence order and shares entries only after exact equality of every
node field and both child indices. Hash collisions, different witnesses and
stale contexts cannot substitute one literal entry for another. Conformance
includes deliberately colliding inverse witnesses and repeated internal
subtrees from the actual producer. Encoding supplies raw evidence; callers use
`Dag.replay?` to validate it. For every accepted input tree, `Dag.replay_encode`
proves that checked graph replay returns that same literal tree with its original
caller bindings; `Dag.check_encode` gives Boolean acceptance. The proof follows
the actual hash-table insertion and recursive encoder, maintaining acceptance
of every graph entry and exact cache bindings. It uses no root-sum premise.
`Dag.expand?` reconstructs the literal tree without validating mathematical
claims. `Dag.expand_encode` proves an exact roundtrip for every tree, including
malformed witnesses. `Dag.replay_expands` identifies the expansion of an
arbitrary accepted graph with its checked tree. Consequently
`Dag.check_encode_eq` proves equality of the graph and tree checker results
for every input, preserving rejection as well as acceptance. Ordinary-kernel
probes exercise a forged inverse witness through these theorems.
Encoding visits every input tree occurrence, including repeated subtrees;
the [replay evidence](../reports/sign-det-proof-model.md) measures checking
supplied graphs rather than isolated encoder throughput. The versioned
[byte codec](Codec/README.md) serializes every literal field and checks dimensions,
indices, earlier references and full context/domain bindings before replay.
`Dag.decodeBytes` retains the ordinary tree checker's evidence;
`Dag.decode_replays` connects it to the actual decoded graph. `Dag.decodeDescriptor`
uses the same bytes for an exact requested Thom descriptor and preserves every
raw field through the existing derivative and count-one checks. Supplied coefficient
and context codecs use the shared integer-only JSON type and must preserve
their whole values. `ValueCodec.decode_encode` and `Codec.decode_graph` prove
actual byte roundtrips when printed bytes pass the lexical policy, with the
original structural bounds and subject bindings for graphs. Lower-level
coefficient-sign edges are supplied by the dependency envelope described below.

`RawDescriptor.map` maps coefficients and finite endpoints to a new
representation and context while retaining derivative indices and signs.
`Descriptor.convert` feeds that raw input to the existing descriptor builder.
It constructs fresh preparation, query, support and matrix evidence; it copies
no source replay and reconstructs derivative queries under target operations.
The supplied coefficient map must reflect canonical zero. Arbitrary conversions
retain ordinary builder diagnostics. The companion proves success and preservation
of the selected root when both lawful coefficient interpretations denote the
same converted values, including noninjective representations. They assume no
Archimedean property and apply to any lawful interpretation into a real closed field.
The nested-infinitesimal fixture tests executable context changes; it does not
supply such an interpretation or a semantic proof for that coefficient type.
Those semantic results use the proved
`HexRealRootsMathlib.Tarski.check_rootSum` theorem in `HexRealRootsMathlib/TarskiSoundness.lean`.

Context, head, interval and query-list bindings use literal equality. Tarski
polynomial identities use the shared zero-difference checks. Context values
must contain the caller's full immutable context data, including any refinement;
a hash or reused numeric identifier is insufficient. The current certificate
tree retains the head squarefree evidence in each moment. Graph replay offers
the first entry's validated domain to every node. A node reuses that domain when
it matches the node's first witness. Otherwise a node with several moments
checks its first domain's caller bindings before validating that domain once.
A single moment without a matching shared domain uses full replay directly. Later matching witnesses reuse the selected
domain; different witnesses fall back to complete replay. `Node.check_eq` proves
unconditional equality with the original result for every node and cache.
`TarskiCertificate.checkCached_eq` proves the underlying shared-kernel agreement
for arbitrary caches and certificates.
`Dag.step_eq` and `Dag.replay_eq` preserve the exact original checked step and
prefix replay, including returned trees and all rejections. Each node selects
one domain witness for reuse; other witnesses within that node still incur full
replay at each occurrence. Domain replay and literal binding costs require
performance measurements, including heterogeneous witnesses and one-moment nodes.
`Dag.cache` checks its first domain's caller bindings before creating the initial
cache, even if only one moment will use it.
Node selection considers the first witness, so a different shared witness used
only by later moments can miss. Every moment checks literal cache bindings,
including the first moment used for selection. These costs belong in that
measurement; the cache policy is not claimed to minimize witness replays.
Each moment may supply a positive-scaled reduction chain. Replay checks its
ordered factor indices, positive scales, degree bounds and zero-difference
identities, then checks the Tarski certificate on the bound reduced polynomial.
This path never expands the full product. Direct moments remain available for
comparison. Neither path runs a query producer, gcd search or row search.
`Replay.query_evidence` proves that every accepted tree reaches a checked Tarski
query, including when its root matrix is empty.

`buildTree` constructs the balanced support tree from prepared Tarski queries.
Leaves use existing rational inversion, checking integrality/nonnegativity and
clearing inverse denominators by their least common multiple. Internal nodes
combine the children's retained integer inverses by a tensor product and solve
by exact divisibility, without another rational inversion. Both paths use the
existing integer rank producer to select the retained row basis.
`nodePreparation` and `nodeReduction` define the shared preprocessing decision
and per-row operands used by both construction and its companion statements.
`buildPrepared` additionally returns
a proof that the independent replay accepts the resulting tree. Its `BuildError`
diagnostics remain available for arbitrary coefficient operations. The companion
proves construction succeeds under its lawful interpretation and the shared
proved root-sum theorem; these diagnostics are not mathematical domain failures,
and `determinePrepared` wraps the same producer with its success guarantee.
No supplied roots or guessed counts enter construction. `referencePrepared`
builds the exponential full-ternary system for small-case comparisons; production
recursion never calls it.

The companion proves that every successful `buildTree` result passes the
independent replay under the generic coefficient interpretation laws.
The proof follows the actual query certificates, integer systems, retained
bases, child preprocessing slices and Cartesian supports. Thus the final
`buildPrepared` replay guard cannot fail after successful tree construction
under those laws. This acceptance theorem does not rule out construction
failures or establish root-count semantics.

Construction reduces moments by default after each indexed multiplication,
using the shared positive pseudo-division and normalization routines. The
optional `reduced := false` mode constructs full products, as does the reference
solver. Constant heads use the direct path and their zero-root domain evidence.
`QueryReduction` preprocesses every original query once. All moment rows and
balanced child sublists reuse those reduced operands and their indexed
polynomial witnesses. Child slices rebind local indices without rerunning
pseudo-division. Each node checks its preprocessing against the original query
list before using the reduced factors. The current tree repeats these checks
across nodes; DAG replay shares validated entries. The performance report
accounts for the actual production and replay paths.
`HexSignDetMathlib` proves that produced reductions pass the checker and that
arbitrary accepted reductions preserve each full moment's sign at every root.
`Node.check_sign` composes preprocessing and moment reduction for the actual
Tarski operand; `QueryReduction.slice_checks` validates the child restrictions.
`QueryReduction.check_bounds` proves that every accepted preprocessing keeps
the original query length and supplies only zero or degree-bounded operands.
These algebraic proofs allow noninjective coefficient interpretations; they do
not assert a Tarski root-sum theorem.

The companion also proves full column rank after pruning, correctness and
column order of the actual retained rank certificate, and its left-inverse
identity. Tensor correspondence preserves the exact Cartesian-product order.
`Node.basis_matrix` identifies the selected minor with the actual retained
exponent/sign vectors. `Node.product_inverse` then proves the parent witness
identity with the precise retained row and support lists used by `buildTreeFrom`.
`solveScaled_eq` proves that solving a checked integer system recovers its
counts, including zero dimensions and non-unit denominators. The companion
combines these finite facts with the actual root-query semantics to prove
producer completeness relative to the shared proved root-sum theorem.

`count_moments` proves the finite counting identity on an independently complete
candidate support. `Replay.support_complete` then proves recursive coverage and
exact counts for the actual checked tree, conditional on `Replay.Interprets`:
each node's moments must be the sums over the same finite observations restricted
to its query positions. `Replay.support_iff` excludes both missing and spurious
positive conditions. The companion establishes this explicit moment contract
from query/root semantics through the proved shared root-sum theorem; the executable
checker does not assume it, and the finite induction is not a root-sum
soundness theorem.
`Replay.support_counts` factors that same induction through a proved finite
count-recovery theorem. The companion supplies its Tau Ceti bridge at every
node; the Mathlib-free specialization uses `System.counts_eq`. Neither
specialization changes the executable tree or its candidate order.

The conformance target includes recursive rational examples with supplied exact
roots, malformed matrices and tree mutations, and ordinary-kernel literal
acceptance/rejection probes. In particular, the omitted-support forgery for
`x²−1` passes local matrix/query checks and fails recursive replay. These tests
are regressions, not the complete independent-oracle or Phase-4 evidence suite.
Construction regressions also cover irrational roots, finite intervals, twelve
repeated queries, exact-conversion rejection and full/reduced small-case agreement.
A downstream ordinary-kernel probe instantiates the recursive moment contract
on a two-query tree, and compiled replay independently checks that same tree.
The fixture emitter compares 59 rational cases against independent FLINT
`qqbar` root/sign evaluation and the existing real-algebraic API, including
complete sparse counts and invalid-domain cases. The oracle rejects omitted
conditions even when totals agree. Another 27 fixtures compare descriptor
validation, completion, selected-query signs and full encodings in numerical
root order against FLINT. Ten comparisons and five re-encodings additionally
check common-head squarefreeness/divisibility and numerical root identity. See the [fixture provenance](../conformance-fixtures/HexSignDet/README.md).
The numeric context labels in those fixtures exercise literal binding over the
fixed rational base. Separate common-field fixtures use actual algebraic
coefficients and selected embeddings. The nested certificate and refinement
checks are described below; full tower integration belongs to hex-real-closure.

`SignTable` has a private constructor and stores distinct well-formed sign rows
with strictly positive natural counts. `SignTable.ofSystem` extracts positive
coordinates from a checked integer system; `Replay.table` requires the full
recursive replay. Its total `count` returns zero for omitted conditions.
`Replay.table_count` proves every lookup equals the finite observation count
under the same explicit `Replay.Interprets` contract. Structural table validity
alone does not prove root completeness. `buildTablePrepared` exposes sparse
construction while retaining the internal diagnostics of `buildPrepared`.
`Replay.count_table` is the representation adapter from independently proved
support coverage and exact integer counts to this same sparse lookup.
`SelectedSigns.signs_of_count` similarly shares the selected-sign lookup
argument with the companion, while `signs_eq` keeps its Mathlib-free contract.

`Descriptor.prepareQueries` constructs a `QueryHandle` for successive queries
at the same validated root. It retains the exact prepared squarefree domain.
`QueryHandle.buildSigns` and `signAt` use the same selected-sign producer as the
ordinary descriptor APIs; the finite agreement proofs preserve their results.
The handle is indexed by the original descriptor, including its context,
interval and derivative word. `checkSigns` retains the ordinary literal replay
checks, so evidence from another selection or changed representation is rejected.
The companion proves handle construction and every prepared query succeed
under lawful coefficients, with the shared proved root-sum dependency.
Preparation is shared; each query list still builds its joint table and runs
independent replay. No query-answer cache or performance speedup is claimed.

`determinePrepared context domain queries` returns the table directly using
that same checked producer. Its internal-error branch prints a diagnostic and
returns an empty table; `determinePrepared_success` excludes that branch under
the lawful coefficient-interpretation assumptions using the shared proved
root-sum theorem. Each call constructs the BKR evidence and runs its full
independent replay check. `determine sign context
head lower upper queries` first prepares the root domain and returns `none`
exactly for an invalid domain. Valid domains without roots return an empty
table. Empty query lists count all roots at the empty sign word; zero and
repeated queries keep their positions. The companion proves exact root counts
for every word, including zero for omitted words, using the same shared
proved root-sum theorem. Use `buildTablePrepared`
for explicit diagnostics, or `buildPrepared` to retain the replay certificate.

`RawDescriptor` records its full context, root domain, distinct derivative
indices and sign word. `RawDescriptor.check` reconstructs the formal derivative
queries, checks the complete table replay and requires count exactly one.
`Descriptor.ofReplay?` retains accepted evidence with its sign operation and
context bound in the type. It validates supplied evidence, not mathematical
nonexistence when a supplied certificate fails. `Descriptor.build` constructs
the evidence, distinguishing absent and ambiguous conditions, malformed inputs,
invalid domains and context mismatches. Internal BKR failures retain a separate
outer diagnostic result in this Mathlib-free executable; the companion proves
that branch unreachable under a lawful coefficient interpretation.
`Descriptor.validate` returns `some` exactly when this constructor succeeds and
provides the public option-valued validation operation. The companion proves
that success means the raw descriptor selects one real root. For an arbitrary
unlawful sign function, `validate` also maps an internal construction error to
`none`; `Descriptor.build_noError` rules that case out under the companion's
coefficient laws.

`Thom.compareSigns` implements
the largest-differing-index rule as a finite operation on sign words; root
comparison still requires realized full encodings of the same head and the
companion's Thom foundation. It is not the public descriptor `compare` API.

`Descriptor.buildCompletion` computes a full derivative table and selects the
count-one word whose indexed signs agree with the old descriptor. Its
`Completion` result retains a validated descriptor and checked literal domain,
context and partial-sign agreement. Missing slots fail `Thom.select`; they are
never filled with zero. `Descriptor.buildSigns` checks a joint table on the
selected derivatives followed by the exact requested queries. `SelectedSigns`
retains the full replay, a fixed-length sign vector and the assertion that
filtering gives exactly its count-one row. `SelectedSigns.signs_eq` proves
agreement for every matching finite observation under `Replay.Interprets`.
`Descriptor.signAt` returns an ordinary integer for one polynomial using the
same checked joint-table construction. Its explicit internal-error branch
emits a panic diagnostic in compiled execution and returns zero;
`Descriptor.signAt_success` in the companion proves that branch
unreachable under lawful coefficient interpretation, and `signAt_correct`
identifies the result with evaluation at the selected root. The executable
operation takes no companion proof package. Each call prepares its domain,
constructs a checked table and repeats its replay in selected-sign extraction.
Use `buildSigns` for several queries to share one table. Preparation and replay
work is shared with the table and completion callbacks in the
[performance report](../reports/sign-det-performance.md). `signAt` itself has
no separate timing registration. Its extra replay is a constant number of
calls to the existing checker, rather than a new asymptotic factor; no claim
that this overhead is negligible follows from the component measurements.

`Descriptor.complete` exposes the completed descriptor directly. It calls the
same `buildCompletion` producer. An internal error prints a diagnostic and
returns the original validated descriptor; the companion proves this branch
unreachable when coefficient arithmetic and signs have their specified
interpretation. The fallback retains the source's indices and may still be
partial; `complete_correct` proves fullness under those interpretation laws.
Completion retains the exact head, interval and context,
including for an empty partial encoding that selects a unique root. Call
`buildCompletion` when the completion evidence or explicit diagnostics are
needed. Each call constructs and checks its full derivative table, then checks
that replay again when constructing the returned descriptor. It does not cache
a previous completion.

`Descriptor.buildRoots` enumerates full derivative encodings, validates each
count-one row, and inserts them by Thom order. `rootsFrom_perm` proves that
successful construction preserves all input encoding words. Insertion checks
the common head and canonical full derivative slots before comparing.
`ThomOrder` proves transitivity and reversal directly for `compareFrom`, lifts
them through sign-shape validation and literal descriptor guards, and supplies
the laws used by `insert_sorted` and `rootsFrom_sorted`. These finite strict
sortedness proofs require no caller-supplied comparator laws. The companion's
`Descriptor.fullOrder_root` relates applicable full comparisons to strict
mathematical root order using Tau Ceti's Thom theorems.
`Descriptor.buildRoots_success` rules out insertion and extraction errors for
every valid domain under lawful coefficients; `buildRoots_roots` proves the
actual result covers every root exactly once in strictly increasing order.
No rational separators or injective coefficient storage are required.
For positive-degree heads, `rootsFromTable` extracts every descriptor from the
same accepted full table. Its proof-backed row constructor reuses the literal
query/context bindings, derives sign shape from the table, and establishes
count one from membership. Each row performs its count guard and insertion;
it does not rerun the complete replay, rebuild derivatives or test full-slot
distinctness. `rootsFromTable_eq` proves exact agreement with the literal
per-descriptor checking path, including diagnostics. `buildRoots_spec` connects
both degree branches of the public entry point to the actual prepared table;
`buildRoots_perm` and `buildRoots_sorted` give its row preservation and finite
strict sortedness. `buildRoots_raw` binds every returned descriptor to
the requested context, head, interval and full derivative slots.
`buildRoots_none` proves that the absent-domain result occurs exactly when
preparation fails. `buildRoots_ofEmpty` proves actual empty-table success in
both degree branches, without any ordering premise. `buildRoots_ofSingle`
proves actual success for one unit-count row without any comparator premise. These finite proofs have
no admitted dependencies.
`buildRoots_constant` proves that any successful constant-head result is empty
using descriptor shape alone. Constants retain the literal checking path.
Each descriptor still constructs its full index list. Every insertion comparison
rebuilds both canonical index lists and compares the heads; for N descriptors
of degree n this can add O(N²n) guard work. Since N≤n, this contributes at
most O(n³), within the SPEC's conservative production bounds. Hoisting could
reduce repeated guard work, but no measurement here isolates that gain or
claims optimal root-list construction.

`CommonProduct.build` uses the shared polynomial gcd and division to form a
common head. Replay checks the exact context/old heads and three polynomial
zero-difference identities: the head divides the old product and each old head
divides the common head. `CommonProduct.check_roots` proves that arbitrary
accepted identities give exactly the union of the old root sets. A separate
prepared-domain check is essential: the unreduced product can satisfy all three
identities while still having repeated factors.

`Descriptor.buildReencoding` determines signs on the target domain, including
its full derivatives and the old defining equation, selected derivatives and
strict finite-endpoint queries. It retains joint count-one evidence and a
validated target descriptor. Invalid target domains and absent selected roots
return `none`; internal invariant failures remain diagnostic. The companion
proves that each actual endpoint query expresses its strict bound.
`Descriptor.buildReencoding_refinement` proves that the actual algorithm succeeds
when a valid interval for the same head retains the selected root and its root
set is contained in the original domain. The output preserves that root and
has fresh evidence bound to the new interval. The old validated partial word
supplies uniqueness, so this proof applies to noninjective representations
and non-Archimedean coefficient interpretations without a general Thom
injectivity theorem. `Descriptor.buildReencoding_congr` also permits a differently
stored head with a zero difference from the original polynomial. Fresh evidence
retains the new literal head binding. `Descriptor.reencoding_rows` proves the unique joint row
whenever any target contains the source root. `RawDescriptor.full_unique` and
`full_fiber` use Tau Ceti Thom injectivity to prove target full-word uniqueness.
`Descriptor.buildReencoding_success` establishes actual producer success and
root preservation for any valid target polynomial and interval containing the
source root, including a different head or an enlarged root domain.
`Descriptor.buildComparison` re-encodes both roots on the common head over the
whole line, then applies the guarded full Thom rule. It retains both joint
replays and the common-product witness. This handles shared roots, different
old intervals and equivalent noncanonical coefficient expressions without
comparing unrelated derivative vectors. `Descriptor.compare` returns the order
directly. For identical stored heads it uses two completions and compares their
full encodings directly, even across distinct intervals; it runs no common-head
gcd or joint re-encoding on that path. Distinct representations, including
representations of the same mathematical polynomial, retain the joint path. Its diagnostic fallback returns `eq`; the
companion's `buildComparison_success` and `compare_success` prove that branch
unreachable under lawful coefficient interpretations, including preservation
of ordinary division, including division by zero with value zero.
`compare_ofError` fixes the fallback value exactly. `buildOrder_roots` proves
actual success and mathematical order for both paths. `compare_correct` and the three order equivalences relate
the total result to the original selected roots. The computational operation
requires no companion proof package. `CommonProduct.build_success` proves
acceptance of the actual gcd/division record even for zero inputs;
`build_squarefree` proves squarefreeness of the actual head for squarefree inputs.
Arbitrary accepted records still require their separate prepared-domain check.
A comparison of different stored heads currently constructs four BKR tables
and four prepared domains; the equal-head path constructs two completion
tables: joint re-encoding evidence and a
separate target descriptor for each side. The
[joint](../reports/sign-det-joint-performance.md) and
[shared-root](../reports/sign-det-shared-roots.md) reports account for these paths.
The fixed number of preparations and table calls adds a constant factor to
the stated per-comparison bounds. Sharing could reduce that factor; the
measured small cases and recorded stress-case limits make no optimality claim.

The total table APIs and selected-root operations have producer success and
root correspondence proofs. Their diagnostic fallback values are specified
in the [API contract](SPEC/hex-sign-det.md). The integer-only JSON codec has
literal and byte roundtrip proofs, and the coefficient-level dependency
envelope retains shared lower-level evidence with complete subjects. Consumer
readers reconstruct contexts and prove the exact coefficient facts before
using them; ordinary coefficient arithmetic can still compute signs.
Sample-point and tower integration belong to
[#10378](https://github.com/kim-em/hex-dev/issues/10378), and tactic integration
belongs to [#10358](https://github.com/kim-em/hex-dev/issues/10358). The root
semantics proofs consume the shared proved root-sum theorem and the Tau Ceti
BKR and Thom foundations. See
the [performance report](../reports/sign-det-performance.md) for measured
inputs, evidence dispositions and practical limits.

The extension conformance target uses the existing `RationalFn Rat` and
`RationalFn (RationalFn Rat)` coefficient fields with explicit exact signs at
successive positive infinitesimals. Its independent oracle is pinned to
`z3-solver==4.15.4.0` and numeric runtime version `(4, 15, 4, 0)`;
its RCF API constructs roots and compares them exactly. Every fixture records the ordered
coefficient levels and starts a fresh oracle context. The corrected
`(εx²−1)(εx³−1)` example exercises the two positive partial descriptors,
completion, root order, selected signs and cross-polynomial re-encoding without
a rational separator. Two-level fixtures isolate `δ` from `ε` and `ε+δ` using
an endpoint `2δ`. Interval refinement narrows `(0,2δ)` to `(δ/2,3δ/2)`,
retaining δ with the full word `(+,-,+)` even though no positive rational lies
between those endpoints. The independent oracle checks the selected-root
identity after refinement. Both coefficient levels reject changed context, head and
derivative-query bindings, and reject a multi-query table presented as a leaf.
These leaf-arity checks do not test an identity-preserving incomplete support
forgery. The oracle enforces each case’s coefficient depth and the corrected
Passmore polynomial, and checks all five descriptor-error reasons. It separately
rejects forged counts, reordered roots, altered encodings and context metadata.
These test-only sign callbacks do not implement the ordered-function provider;
tower-generated coefficient proofs remain a consumer responsibility. The
shared nested evidence, literal DAG serialization and performance evidence
are described below and in the linked reports.

Build the library and its regression target with:

```sh
lake build HexSignDet +HexSignDet.Conformance hexsigndet_emit_infinitesimal
.lake/build/bin/hexsigndet_emit_infinitesimal > conformance-fixtures/HexSignDet/infinitesimal.jsonl
python3 scripts/oracle/sign_det_z3.py --check
python3 -m unittest scripts.oracle.test_sign_det_z3
```

Run only the nested refinement API example with
`.lake/build/bin/hexsigndet_emit_infinitesimal refinement`.

The [retained representative observation](../reports/data/sign-det-refinement/f03d5daa3/metadata.json)
records one complete `refinement` process at source revision `f03d5daa3`:
3.967 seconds on chungus2, automatically selected CPU 5. It includes startup,
preparation, re-encoding, interval-binding checks and JSON output. The record
retains build freshness, clean source state, unchanged source/binary checks and
oracle-checked output. Its executable resolved through the shared build directory
of the original `hex-dev-issue-10377` worktree, as recorded in the metadata.
The freshness and hash checks bind that observation to its archived source and
binary; it is not a measurement of the current rebased implementation.
The [earlier observation](../reports/data/sign-det-refinement/ef06438d2/metadata.json)
is retained too; it predates the explicit returned-bound fields and lacks the
later clean-tree/freshness metadata. Neither is a scaling or Phase-4 verdict.

Structural expansion and checked graph replay deliberately treat unreachable
entries differently: both reject invalid references, while only replay checks
all arithmetic witnesses. An unreachable false witness can therefore coexist
with a structurally expandable root, but causes the whole graph replay to fail.
`Dag.descriptor_replay` proves exact graph/tree descriptor agreement on any
accepted supplied graph's actual replay result. For encoded trees,
`Dag.descriptor_encode` also covers rejection. Descriptor shape and context
checks run before graph replay.

`Dependencies.Graph` supplies the cross-level envelope with level and full
subject bindings. `Dag` supplies each packet's same-level BKR component.
Complete intermediate coefficient facts and context reconstruction belong to
the packet readers; the fixed-domain memo does not supply them.

`Dag.changeOps` transports a checked memo along literal equalities of the
coefficient operations. `changeOps_validate` proves exact agreement with the
actual validator, including rejection; `changeOps_nodes` preserves its literal
node list and indices. These are operation equalities, not field laws on stored
representatives or assumptions about certificate completeness.

`Dependencies.Graph` stores certificates from successive coefficient fields in
one finite array. Each entry records its coefficient level, full literal
subject, payload and references to lower-level entries. References include
both the expected level and subject. `Graph.check` rejects cycles, forward
references, equal-level dependencies, invalid result indices and mismatched
subjects, including defects in unused entries.

`Graph.validate?` takes the mathematical reader for each packet and checks
entries in order. Each reader receives only its declared, already checked
children, and its result type may depend on the complete entry. Several parent
packets can reuse one child's typed result. Local readers check the actual BKR
and coefficient evidence, including coverage of every required fact;
structural envelope checking alone does not establish sign correctness.
`Graph.validate_entries` proves that every returned memo position retains the
original complete entry. `Graph.validate_check`, `Graph.check_children` and
`Graph.check_roots` establish reference bounds, strict level decrease and full
literal bindings from actual acceptance.

`Dependencies.Graph.codec` uses the shared integer-only JSON format.
`Graph.codec_lawful` and `Graph.codec_bytes` preserve every entry, result and
reference literally. `Graph.decode` binds the ordered result levels and
subjects to the caller before checking packet contents. `Graph.decode_encode`
relates actual printing, byte parsing and local checking to the exact returned
memo and parsed graph, under the shared syntax/resource precheck.
`Decoded.results` selects the declared typed results in order using proved
index bounds, including repeated references to shared entries.
`Decoded.results_bound` and `results_size` identify their full ordered caller
bindings and length. Packet readers still supply
context reconstruction and evidence for intermediate coefficient arithmetic.

The direct nested conformance example produces two distinct upper packets
and one joint lower packet, then checks their common serialized envelope using
the existing mathematical readers and a finite coefficient reader. It tests
repeated results, false unused packets, independently valid incomplete child
packets, missing edges, wrong levels, stale subjects and altered payload
contexts. It reuses validated contexts and ordinary coefficient arithmetic;
it does not establish strict compiled arithmetic replay.

The [performance report](../reports/sign-det-performance.md) links node, edge
and byte inventories, intermediate operand observations, allocation and
process-memory records, and the measured proof-assembly costs. These records
state their coverage limits; process memory is not peak live-object accounting.
The [conformance report](../reports/sign-det-final-conformance.md) separately
records independent root/sign comparisons and adversarial checks.

`Descriptor.changeOps` and `QueryHandle.changeOps` retain validated root data
and the exact canonical prepared domain when coefficient operations are proved
equal. They transport only validity proofs; they do not prepare another domain
or produce another query. The descriptor's stored polynomial, endpoints,
context and replay remain bound. These functions support using supplied-fact
operations while assembling proofs at successive coefficient levels.

`Descriptor.ofChecked` restores a literal subject and replay only from a proof
that the existing descriptor checker accepts them. `QueryHandle.ofChecked`
requires the exact equation identifying its stored domain with `Sturm.prepare`;
`Descriptor.prepareQueries_eq` identifies the corresponding canonical handle.
