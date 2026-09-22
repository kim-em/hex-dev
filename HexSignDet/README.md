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

Context, head, interval and query-list bindings use literal equality. Tarski
polynomial identities use the shared zero-difference checks. Context values
must contain the caller's full immutable context data, including any refinement;
a hash or reused numeric identifier is insufficient. The current certificate
tree repeats the head squarefree evidence in each moment and rechecks it there;
shared domain replay remains an integration and performance obligation.
The checker reconstructs unreduced moment products and runs no query producer,
gcd search or row search.
`Replay.query_evidence` proves that every accepted tree reaches a checked Tarski
query, including when its root matrix is empty.

`buildTree` constructs the balanced support tree from prepared Tarski queries,
using existing rational inversion and integer rank producers. It checks rational
integrality and nonnegativity before extracting integer counts and clears inverse
denominators by their least common multiple. `buildPrepared` additionally returns
a proof that the independent replay accepts the resulting tree. Its `BuildError`
diagnostics expose outstanding producer-completeness obligations; they are not
mathematical domain failures and this is not yet the total `determinePrepared`
API. No supplied roots or guessed counts enter construction. `referencePrepared`
builds the exponential full-ternary system for small-case comparisons; production
recursion never calls it.

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
Their numeric context labels exercise literal binding over the fixed rational
base only; full tower/refinement context fixtures remain required.

The library currently exposes raw replay data and checked construction, not a
validated `SignTable` or the total `determinePrepared` API. Producer completeness,
tensor/retained-row-basis existence, reduced-moment
evidence, Thom descriptors and selected-root operations, serialization and
nested evidence sharing remain required. The finite lemmas above do not prove
root-count correctness. Those
proofs must interpret the actual query replays through #10389 and consume the
specified BKR/Thom foundations in the companion. No semantic theorem or
performance milestone is claimed here. See the [specification](SPEC/hex-sign-det.md)
for the complete contract and [#10377](https://github.com/kim-em/hex-dev/issues/10377)
for the remaining assignment.

Build the library and its regression target with:

```sh
lake build HexSignDet +HexSignDet.Conformance
```
