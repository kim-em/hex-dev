# hex-sign-det

Finite BKR construction and replay over the shared HexSturm prepared-query
API. This development library is Mathlib-free and is not yet released.

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
extraction and truncated/cyclic graphs. This typed graph does not yet provide a
byte decoder, lower-level coefficient-sign edges, automatic deduplication or
shared verification of the domain inside each Tarski certificate. Those
integration tasks and measured node/edge/byte costs remain required.

Context, head, interval and query-list bindings use literal equality. Tarski
polynomial identities use the shared zero-difference checks. Context values
must contain the caller's full immutable context data, including any refinement;
a hash or reused numeric identifier is insufficient. The current certificate
tree repeats the head squarefree evidence in each moment and rechecks it there;
shared domain replay remains an integration and performance obligation.
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
diagnostics expose outstanding producer-completeness obligations; they are not
mathematical domain failures and this is not yet the total `determinePrepared`
API. No supplied roots or guessed counts enter construction. `referencePrepared`
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
across nodes; finite DAG sharing and its performance accounting remain required.
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
counts, including zero dimensions and non-unit denominators. Integrating these
finite facts with root/query semantics into full producer completeness remains
required.

`count_moments` proves the finite counting identity on an independently complete
candidate support. `Replay.support_complete` then proves recursive coverage and
exact counts for the actual checked tree, conditional on `Replay.Interprets`:
each node's moments must be the sums over the same finite observations restricted
to its query positions. `Replay.support_iff` excludes both missing and spurious
positive conditions. The companion must establish this explicit moment contract
from query/root semantics through #10389; the executable checker does not assume
it, and the finite induction is not a root-sum soundness theorem.

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
The numeric context labels exercise literal binding over the fixed rational
base only; full tower/refinement context fixtures remain required.

`SignTable` has a private constructor and stores distinct well-formed sign rows
with strictly positive natural counts. `SignTable.ofSystem` extracts positive
coordinates from a checked integer system; `Replay.table` requires the full
recursive replay. Its total `count` returns zero for omitted conditions.
`Replay.table_count` proves every lookup equals the finite observation count
under the same explicit `Replay.Interprets` contract. Structural table validity
alone does not prove root completeness. `buildTablePrepared` exposes sparse
construction while retaining the internal diagnostics of `buildPrepared`.

`RawDescriptor` records its full context, root domain, distinct derivative
indices and sign word. `RawDescriptor.check` reconstructs the formal derivative
queries, checks the complete table replay and requires count exactly one.
`Descriptor.ofReplay?` retains accepted evidence with its sign operation and
context bound in the type. It validates supplied evidence, not mathematical
nonexistence when a supplied certificate fails. `Descriptor.build` constructs
the evidence, distinguishing absent and ambiguous conditions, malformed inputs,
invalid domains and context mismatches. Internal BKR failures retain a separate
outer diagnostic result until general producer completeness is proved.

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

`Descriptor.buildRoots` enumerates full derivative encodings, validates each
count-one row, and inserts them by Thom order. `rootsFrom_perm` proves that
successful construction preserves all input encoding words. Insertion checks
the common head and canonical full derivative slots before comparing.
`insert_sorted` and `rootsFrom_sorted` prove finite strict sortedness under
explicit transitivity and reversal laws for this guarded comparator. Obtaining
these laws on realized encodings and proving strict real-root order still
requires the companion's Thom foundation. An impossible
order, duplicate word or non-unit count remains an internal error pending the
Thom foundation; no default order or omitted row conceals such a failure.
For positive-degree heads, `rootsFromTable` extracts every descriptor from the
same accepted full table. Its proof-backed row constructor reuses the literal
query/context bindings, derives sign shape from the table, and establishes
count one from membership. Each row performs its count guard and insertion;
it does not rerun the complete replay, rebuild derivatives or test full-slot
distinctness. `rootsFromTable_eq` proves exact agreement with the literal
per-descriptor checking path, including diagnostics. `buildRoots_spec` connects
both degree branches of the public entry point to the actual prepared table;
`buildRoots_perm` and `buildRoots_sorted` give its row preservation and finite
conditional sortedness. `buildRoots_raw` binds every returned descriptor to
the requested context, head, interval and full derivative slots.
`buildRoots_constant` proves that any successful constant-head result is empty
using descriptor shape alone. Constants retain the literal checking path.
Each descriptor still constructs its full index list. Every insertion comparison
rebuilds both canonical index lists and compares the heads; for N descriptors
of degree n this can add O(N²n) guard work. Hoisting that repeated work, sharing
domain checks inside the query tree and measuring all required costs remain
obligations.

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
`Descriptor.buildComparison` re-encodes both roots on the common head over the
whole line, then applies the guarded full Thom rule. It retains both joint
replays and the common-product witness. This handles shared roots, different
old intervals and equivalent noncanonical coefficient expressions without
comparing unrelated derivative vectors. A comparison currently constructs
four BKR tables and four prepared domains: joint re-encoding evidence and a
separate target descriptor for each side. Sharing this work and accounting
for its cost against the required comparison bounds remain required.

The total `determinePrepared` API, producer completeness, full constructor
correspondence and the domain-exact `validate` API remain required. Completion,
root lists and selected signs still expose internal diagnostics until their
totality proofs are supplied. Comparison/re-encoding correspondence and
domain-exact totality, the consumer sample-point interface, serialization and
nested evidence sharing also remain required. The finite lemmas above do not prove
root-count correctness. Those proofs must interpret the actual query replays
through #10389 and consume the
specified BKR/Thom foundations in the companion. No semantic theorem or
performance milestone is claimed here. See the [specification](SPEC/hex-sign-det.md)
for the complete contract and [#10377](https://github.com/kim-em/hex-dev/issues/10377)
for the remaining assignment.

The extension conformance target uses the existing `RationalFn Rat` and
`RationalFn (RationalFn Rat)` coefficient fields with explicit exact signs at
successive positive infinitesimals. Its independent oracle is pinned to
`z3-solver==4.15.4.0` and numeric runtime version `(4, 15, 4, 0)`;
its RCF API constructs roots and compares them exactly. Every fixture records the ordered
coefficient levels and starts a fresh oracle context. The corrected
`(εx²−1)(εx³−1)` example exercises the two positive partial descriptors,
completion, root order, selected signs and cross-polynomial re-encoding without
a rational separator. Two-level fixtures isolate `δ` from `ε` and `ε+δ` using
an endpoint `2δ`. Both coefficient levels reject changed context, head and
derivative-query bindings, and reject a multi-query table presented as a leaf.
These leaf-arity checks do not test an identity-preserving incomplete support
forgery. The oracle enforces each case’s coefficient depth and the corrected
Passmore polynomial, and checks all five descriptor-error reasons. It separately
rejects forged counts, reordered roots, altered encodings and context metadata.
These test-only sign callbacks do not implement the ordered-function provider;
tower-generated coefficient proofs, nested semantic replay, literal DAG
serialization and all Phase-4 measurements remain required.

Build the library and its regression target with:

```sh
lake build HexSignDet +HexSignDet.Conformance hexsigndet_emit_infinitesimal
.lake/build/bin/hexsigndet_emit_infinitesimal > conformance-fixtures/HexSignDet/infinitesimal.jsonl
python3 scripts/oracle/sign_det_z3.py --check
python3 -m unittest scripts.oracle.test_sign_det_z3
```
