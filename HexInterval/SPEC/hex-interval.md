# hex-interval (exact interval data and budgeted propagation search, Mathlib-free)

`hex-interval` is the Mathlib-free computational library for interval
arithmetic. Its generic engine treats domains, operations, and facts as
opaque: it maintains a shared expression program, schedules propagation and
refinement actions, and records successful search steps. Mathlib-free function
packages may associate stable opaque keys with callbacks that compute
candidate interval facts, but those candidates remain untrusted search data.
Only [hex-interval-mathlib](../../SPEC/Libraries/hex-interval-mathlib.md)
interprets the keys as real-valued functions, reconstructs each retained step
from a soundness theorem, and constructs Lean proof terms.

The library is intended to support a standalone `interval` tactic. Integration
with `grind` is not part of this development. The scheduler and rule protocol
should nevertheless be reusable by another frontend later.

The procedure is deliberately incomplete. It tries to prove a requested bound
or to make a collection of hypotheses inconsistent within explicit budgets.
Failure means that the selected rules and search policy did not find a proof.
It does not mean the goal is false.

## Requirements

The design must satisfy all of the following.

1. Every proved endpoint is exact. The initial proof-facing format uses Lean
   core's arbitrary-exponent `Dyadic`; no floating-point value is used as a
   proved endpoint. Whether search also keeps exact-rational working facts is
   decided by the feasibility experiments below, not by the trust contract.
2. The lower and upper ends independently support strict and non-strict bounds.
   Either end may be unbounded. Empty, singleton, and whole intervals have
   canonical representations.
3. The program representation shares repeated subexpressions. A bound proved
   for one occurrence is available to every consumer of that occurrence.
4. A rule may keep private state, offer several enclosure methods for the same
   function, improve a previous result at greater effort, suggest a local
   range split, suggest a proof-level case split, or propagate a result
   backwards into its arguments.
5. The search policy is separate from rule correctness. Replacing a heuristic
   cannot affect soundness.
6. The default policy is deterministic under a step budget. Wall-clock limits
   are secondary emergency limits, not the definition of the search.
7. Search runs as compiled Lean code. The trace contains only successful facts
   needed by the final derivation. Failed probes and discarded candidates do
   not appear in the generated proof.
8. No part of the implementation, conformance suite, benchmark, or tactic
   fallback uses `native_decide`.

The fixed contracts are semantic: exact enclosures, independent strictness,
safe failure, replayable provenance, deterministic resource accounting, and
the trust boundary in the companion SPEC. The following are deliberately
empirical until measured: the physical interval representation, dyadic-only
versus rational working facts, branch-state storage, the exact derivation
constructors, eager versus lazy expression generation, policy scores and
stage order, and the preferred enclosure method for each function. A first
implementation is a hypothesis about these choices, not a reason to close the
design space.

Implementation order follows the dependency structure. The first search
milestone is the function-agnostic program, rule protocol, fact state,
worklist, and bounded extension mechanism, exercised with opaque operation
keys. Dyadic, rational, elementary-function, and Mathlib theorem backends plug
into that framework; backend-specific replay experiments do not block or
define the scheduler architecture.

The active implementation gate is to harden and compare the first complete
arbitrary-function vertical: independently assembled forward and backward
propagators, function-owned retries and split suggestions, structural
instantiation, equality transport, and external policy choice must all run
through the same engine protocol. The centered-product and reciprocal canaries
are evidence for that interface, not a reason to declare it final.
Before another rational-backend milestone, at least one non-polynomial
function package must complete semantic replay through this same path,
including any retained instantiation and equality evidence, and produce an
ordinary theorem about the caller's target. A compiled search fixture or
`#guard` is not completion of that gate. Sine is the first candidate because
it exercises the existing research experiment, but the exact function and
certificate shape remain open to evidence from implementation.

Exact-rational planning, projection, replay, and optimization therefore remain
deferred while package assembly, cache ownership, payload freezing, structural
matching, policy traces, and non-polynomial replay are still being tested; no
registry, scheduler, instantiation, or policy interface may depend on the
eventual rational representation. The checked dyadic interval domain is
sufficient as the endpoint substrate for these framework experiments.

“Compiled search” means ordinary elaboration-time Lean execution of the
untrusted planner. It does not authorize `precompileModules := true`; the Lake
target continues to follow [the repository policy](../../SPEC/design-principles.md#lakefile),
which reserves precompiled modules for libraries exporting approved externs
and forbids them for Mathlib-importing libraries.

## Scope

The first implementation provides the data and search machinery needed for
real-valued expressions. The scheduler is independent of real semantics:
nodes and facts carry small domain and operation identifiers, and the caller
owns their mathematical meanings. The initial interval fact format is more
specific. Its cut consistency assumes a dense ordered scalar domain with an
exact dyadic embedding. The Mathlib companion first instantiates `ℝ`, and a
later `ℚ` instance is compatible with the same cuts. Direct `ℤ` or `ℕ`
semantics require domain-specific integer endpoint normalization; until then,
those types enter only through casts to `ℝ`.

The following are not initial goals:

- a complete decision procedure for nonlinear real arithmetic;
- cylindrical algebraic decomposition or another multivariate real-closed-field
  procedure;
- IEEE 1788 decorations or modal intervals;
- trusting hardware rounding, `Float`, MPFR, Arb, or an external theorem
  prover;
- representing every disconnected image as one value;
- integration with `grind`.

Optional external software may later propose bounds, range-reduction data, or
split points. Such output is an untrusted candidate. The Mathlib companion must
check it with the same theorems as a native candidate, and the native Lean rule
must remain the default and fallback. Any such hook follows the
untrusted-dispatch contract in
[SPEC.md's project-wide proof policy](../../SPEC/SPEC.md#project-wide-proof-policy):
availability is never mentioned by a theorem, rejection falls back to native
Lean, and only independently checked candidate data crosses the boundary.
This SPEC presently approves no `@[extern]` planner hook. Adding one requires a
SPEC revision naming its versioned symbol and candidate schema, shape
validator, checker soundness theorem, and native absence/rejection fallback.

## Interval representation

The semantic shape is intentionally small. The exact constructors and the
placement of the canonicity invariant remain experimental, but the observable
distinctions below are part of the contract. `Dyadic` means Lean core's
`Init.Data.Dyadic` type. The rounding precision used by the initial dyadic
backend is signed `Int`, as in core; negative values are needed for coarse
grids at large magnitudes.

```lean
namespace Hex
namespace Interval

/-- A lower cut. `strict = true` means `value < x`. -/
inductive Lower
  | unbounded
  | finite (value : Dyadic) (strict : Bool)

/-- An upper cut. `strict = true` means `x < value`. -/
inductive Upper
  | finite (value : Dyadic) (strict : Bool)
  | unbounded

inductive Raw
  | empty
  | bounds (lower : Lower) (upper : Upper)

end Interval
end Hex
```

`Raw` avoids shadowing Lean's `Repr` typeclass. The public `Hex.Interval` is an
opaque API with a `view : Hex.Interval → Hex.Interval.Raw` eliminator, smart
constructors, and normalization; consumers do not project its backing store.
Two internal candidates must be compared during the vertical feasibility
prototype:

1. a structure bundling `raw : Raw` with a proof of `raw.CutConsistent`;
2. plain data whose `Bool`-valued consistency and normalization are checked at
   construction or replay boundaries, without carrying a proof in every hot
   value.

The comparison measures compiled search, ordinary kernel replay, proof bytes,
allocation, and whether a proof field obstructs safe `#eval`. The SPEC freezes
neither candidate before that measurement. All public examples use the fully
qualified `Hex.Interval`, because Mathlib also has a root `Interval` type; the
public namespace is itself revisitable before release if qualification proves
awkward. Unless a block explicitly says otherwise, unqualified API sketches
below are declarations inside `Hex.Interval`.

The comments describe cuts as viewed from outside the interval. In semantic
notation, a finite lower cut `(a, false)` means `a ≤ x`, and `(a, true)` means
`a < x`. A finite upper cut `(b, false)` means `x ≤ b`, and `(b, true)` means
`x < b`.

This gives all ordinary interval shapes:

| Set | Lower | Upper |
| --- | --- | --- |
| `∅` | canonical `empty` | canonical `empty` |
| `{a}` | closed `a` | closed `a` |
| `[a,b]` | closed `a` | closed `b` |
| `[a,b)` | closed `a` | open `b` |
| `(a,b]` | open `a` | closed `b` |
| `(a,b)` | open `a` | open `b` |
| `[a,+∞)` / `(a,+∞)` | finite | unbounded |
| `(-∞,b]` / `(-∞,b)` | unbounded | finite |
| `(-∞,+∞)` | unbounded | unbounded |

`Raw.CutConsistent` says exactly that `empty` is the unique empty shape, and a
finite `bounds` pair has either `a < b`, or `a = b` with both cuts closed.
Pairs with an infinite end are consistent. Over a dense ordered domain
containing the dyadics, every consistent `bounds` value is nonempty.
`normalizeUnchecked` returns `empty` when the lower value exceeds the upper value, or
when equal finite values have at least one open cut. It is idempotent. Public
smart constructors and operations return canonical observable values under
either internal candidate. Infinite ends do not carry meaningless closure
flags. This invariant deliberately does not claim that, for example, `(0,1)`
contains an integer.

Exact `normalizeUnchecked` is only for trusted or already-preflighted inputs: comparing
two finite dyadics may align their exponents by shifting a mantissa. The
planner-facing `normalizeWithin` first computes endpoint height and alignment
shift from constructor fields and returns a distinct `resourceLimit` result
when either bound is exceeded. It never interprets a refused comparison as an
empty interval or as consistent cuts. Every future public reifier, certificate
decoder, and planner input path must use this resource-safe entry point.

The representation differs from IEEE 1788 set-based intervals in one
important respect. IEEE intervals are closed as sets of finite real numbers,
with infinities used as endpoint markers. A proof assistant must also retain
strict hypotheses and prove strict conclusions. Independent cut openness is
therefore semantic data here, not a display annotation.

### Endpoint facts

The solver stores the lower and upper facts for a node separately. An
unbounded end is the absence of a fact. A fact contains:

```lean
structure Fact where
  scope         : ScopeId
  node          : NodeId
  side          : Side
  value         : Dyadic
  strict        : Bool
  justification : JustificationId
  proofCost     : Nat
```

This sketch shows the dyadic candidate. If the backend experiment selects
exact-rational working facts, `Fact.value` becomes an opaque working-endpoint
identifier and the retained certificate projects it to an exact dyadic or
rational cut. That decision is made before the trace format is frozen.

This avoids manufacturing an intersection proof after every update. When a
new lower fact is stronger, the state changes one pointer. The corresponding
upper fact is unchanged. If two facts state the same cut, the state retains
the one with the cheaper estimated proof. Weaker facts may remain available
when they have much smaller endpoints or lead to a cheaper downstream proof.
Each scope's fact arena is append-only and immutable: “retains” means updating
a selection pointer, never overwriting a fact. The version counter belongs to
the selected `(node, side)` slot and increases whenever its selected fact
changes. Rule cache keys use those slot versions, while derivations keep the
stable `FactId` of the immutable input.

Two finite facts are contradictory precisely when the lower value is greater
than the upper value, or when the values are equal and either fact is strict.
That check uses exact endpoint arithmetic: exact dyadic arithmetic in the
initial candidate, or the selected exact comparison if the working-endpoint
experiment adopts rationals.

### Non-dyadic source facts (deferred backend candidate)

Some exact representation of non-dyadic source cuts will eventually be needed
because goal constants need not be dyadic. The table-and-outward-projection
design below is one deferred backend candidate, not an active framework
dependency or a frozen representation choice. It is not implemented further
until the arbitrary-function package, replay, and policy boundaries above have
stabilized under experiment.

In this candidate, Lean goals containing rational constants such as `1 / 3`
retain each such hypothesis as an exact source fact. At working precision `p`,
the frontend asks this library for an outward dyadic projection:

- a rational lower bound is rounded down;
- a rational upper bound is rounded up;
- an exactly dyadic rational is preserved;
- strictness is preserved when transitivity proves the projected strict cut.

Increasing effort may request a finer projection from the original rational.
It never rounds an already rounded endpoint again. This prevents accumulated
rounding drift and keeps arbitrary rational arithmetic out of the hot
propagation path.

The Mathlib-free rational path does not depend on `norm_num`. Rational source
handling, and any exact-rational working-backend candidate, run as compiled
Lean code over core `Rat`. A `Rat` already has a canonical integer numerator
and a positive, coprime natural denominator. Core's compiled addition,
subtraction, and multiplication implementations use gcd reduction and
cross-cancellation; their deliberate opacity to kernel unfolding is a replay
concern, not a limitation on compiled planning.

When a successful plan is frozen, the planner extracts `Rat.num` and `Rat.den`
into the selected raw certificate encoding. Proof-facing replay uses
transparent integer computations justified by core lemmas such as
`Rat.add_def`, `Rat.sub_def`, `Rat.mul_def`, `Rat.inv_def`, and the rational
equality and order characterizations. All such checks use ordinary kernel
reduction, including `decide +kernel` where appropriate; they never use
`native_decide`.

The Mathlib companion may optionally use `norm_num` only for a surface numeral
or cast leaf connecting goal syntax to a caller-bound rational source. It is
not used for rational planning, projection, certificate validation, arithmetic
replay, or the shared soundness argument.

Core also provides `Rat.toDyadic` together with its one-sided enclosure
theorems. An upper projection can be obtained by applying the lower projection
to the negation and negating the result. The D2 rational arm compares this
route with a small dedicated projector before duplicating any division or
rounding machinery.

The signed-denominator cross-product encoding is retained only as a minimal
soundness spike. The baseline production candidate is a shared table of raw
integer numerators and natural denominators extracted from canonical planner
`Rat`s. Before any arithmetic edge is checked, replay bounds every entry,
requires a nonzero denominator and `Nat.gcd num.natAbs den = 1`, and rejects
rather than normalizes a noncanonical encoding. Thus zero has only the encoding
`0 / 1`, denominators are positive, and inflated equivalent fractions cannot
amplify later cross-products. Every retained entry, including an unused one,
crosses this scan.

Arithmetic edges then use preflighted transparent integer identities
interpreted through `mkRat` and Core's characterization lemmas. Whether replay
should use cancellation-aware cross-products, exposed normalization wrappers,
or a hybrid remains an experimental question, as do the table's physical
layout, uniqueness requirement, and wire format. Experiments separately
measure compiled certificate production, interning, serialization, bounded
decoding, table validation, and replay; they do not compare verifier-only work
with end-to-end normalization as though the workloads were equal.

When this backend layer resumes, its first vertical projects the centered
certificate to the endpoint-erased structural skeleton below and requires
exact skeleton equality for every Dyadic/rational comparison. Its phase
boundary is:

```text
load structural skeleton
→ plan with compiled Core Rat
→ intern canonical endpoints
→ serialize
→ bounded decode
→ validate the complete raw table
→ compiled replay
→ ordinary-kernel replay
```

The first accepted cases are the dyadic-valued `x ∈ [0,1]` control, the
non-dyadic `x ∈ [1/3,2/3]` centered trace, and an odd-denominator ladder with
`d = 2^h - 1` for `h ∈ {8, 32, 128, 512, 2048}`. The latter uses sources
centered at `1/2` with radius `1/d`, so the expected square is bounded by
`1/d^2` and the centered product lower endpoint is
`(d^2 - 4) / (4*d^2)`. Scientific runs retain the full ladder; CI may retain a
bounded prefix.

Every rational entry, including an unused one, crosses encoded-byte and
integer-bit preflight before arbitrary-precision work, then positive-
denominator and coprimality validation. Operation preflight separately charges
retained endpoint size, maximum temporary integer size, and aggregate gcd,
shift, division, and cross-product work. One-step-over tests must demonstrate
rejection before the prohibited allocation. Skeleton mismatch, zero or
noncanonical denominators, inflated equivalent fractions, wrong arithmetic or
projection results, and unused oversized entries are required malformed cases.

This vertical is Mathlib-free and does not use `norm_num`. The Mathlib companion
may use `norm_num` only at an optional surface numeral/cast leaf connecting goal
syntax to a caller-bound rational source; it is not used for planning,
projection, interning, decoding, validation, arithmetic replay, or soundness.
No layer uses `native_decide`.

Projection keeps the strongest strictness justified by order. For a lower
source cut at `r`, a projected dyadic `q <= r` inherits the source strictness
when `q = r`; when `q < r`, the projected cut is strict even if the source was
closed. For an upper source cut, `r <= q` has the dual rule: equality inherits
strictness and `r < q` makes the projected cut strict. Thus rounding outward
does not unnecessarily lose a strict goal.

### Arithmetic and closure

`hex-interval` provides named operations rather than ring or field instances.
Interval addition and multiplication do not satisfy the algebraic laws that a
consumer expects from instances, and division across zero needs an explicit
policy.

The initial operations are:

```lean
namespace Hex.Interval

def intersect  : Interval → Interval → Interval
def hull       : Interval → Interval → Interval
def neg        : Interval → Interval
def add        : Interval → Interval → Interval
def sub        : Interval → Interval → Interval
def mul        : Interval → Interval → Interval
def invAt      : Precision → Interval → Interval
def divAt      : Precision → Interval → Interval → Interval
def pow        : Interval → Nat → Interval
def abs        : Interval → Interval
def min        : Interval → Interval → Interval
def max        : Interval → Interval → Interval
def split      : Interval → Dyadic → Interval × Interval
def regularize : Precision → Interval → Interval

end Hex.Interval
```

For the initial dyadic backend, `Precision` is an alias for signed `Int` and
the implementation reuses core `Dyadic.roundDown`, `roundUp`, `invAtPrec`, and
`divAtPrec` rather than reimplementing directed rounding.

The Mathlib companion proves their set-enclosure theorems. The computational
tests also check the following exactness rules.

- `intersect` chooses the larger lower cut and the smaller upper cut. At equal
  endpoints it chooses open if either input is open.
- `hull` chooses the smaller lower cut and the larger upper cut. At equal
  endpoints it chooses closed if either input contains the endpoint.
- Negation swaps the ends and preserves their openness.
- A finite endpoint of a sum is closed exactly when both contributing
  endpoints are closed.
- After the empty-input short circuit, multiplication partitions both inputs
  by sign, enumerates finite corner and zero candidates, and tracks whether
  each extremum is attained. Zero is an attained extremum whenever either
  nonempty factor contains zero, not only when a factor is the singleton zero.
  For example,
  `[0,1] * (0,1] = [0,1]`, while `(0,1] * (0,1] = (0,1]`.
- A power distinguishes zero, odd powers, and positive even powers. It does
  not implement powers by repeated interval multiplication when a direct hull
  is tighter.
- `abs`, `min`, and `max` use the same candidate-and-attainment discipline.
  In particular, `abs` contains a closed zero exactly when the input contains
  zero, and tied extrema combine the contributing closure witnesses rather
  than blindly copying one endpoint flag.
- `split I m` returns `I ∩ (-∞,m]` and `I ∩ (m,+∞)`. The children are disjoint
  and cover `I`.
- Empty is canonical. Unary image operations and regularization preserve empty;
  binary image and intersection operations absorb an empty argument; and
  `split empty m = (empty, empty)`. Hull instead has empty as a two-sided
  identity.
- `pow I 0` is `{1}` for nonempty `I`, including unbounded `I`, and is `empty`
  for empty `I`. Thus the operation is the direct image of Lean's power
  function rather than a vacuously sound but noncanonical enclosure.

The primitives whose exact images have dyadic endpoints return tight cuts,
including exact endpoint attainment. Precision-indexed inverse and division
must first be sound; their grid-tightness has the additional proof obligation
below. Conservatively closing a cut is permitted for an approximate registered
propagator, not for an exact primitive once its tightness theorem is present.

The image of reciprocal or division may be disconnected, and even `{3}⁻¹`
has a nondyadic endpoint. `invAt p` and `divAt p` return a sound
single-interval enclosure on the `2^-p` dyadic grid for the complete image
under Lean's total inverse, including `0⁻¹ = 0`. Moved grid endpoints use the
strictness rule above. Thus a positive interval bounded away from zero has the
usual reversed reciprocal cuts rounded outward, `[0,1]⁻¹` has hull
`[0,+∞)`, and an interval containing both negative and positive values has
whole-interval hull. A rule can request a split at zero before using a tighter
sign-specific result. A later `IntervalSet` with at most two components is an
isolated extension, not a reason to complicate every initial operation.

This paragraph is the target contract, not a description of the current
component canary. `Experiment.DyadicInterval.reciprocal` currently returns
`inapplicable` for singleton zero, a closed zero endpoint, or a sign-crossing
input; it implements only the sign-separated cases (including an open zero
endpoint mapping to an unbounded side). The concrete package has an executable
across-zero regression for that behavior. Implementing the connected hull of
Lean's total inverse, or selecting an interval-set result, is an explicit
experimental gap before reciprocal can claim the target contract above.

Grid-tightness remains an acceptance target, not an assumed consequence of
core's API. Core currently proves the one-sided `roundDown_le` and
`le_roundUp` lemmas but leaves the corresponding optimality characterizations
as TODOs. The implementation proves the following characterizations locally
or contributes them upstream:

```lean
Dyadic.le_roundDown
  (hy : y.precision ≤ some p) (hyx : y ≤ x) :
  y ≤ x.roundDown p

Dyadic.roundUp_le
  (hy : y.precision ≤ some p) (hxy : x ≤ y) :
  x.roundUp p ≤ y
```

These lemmas are required before the theorem API claims “tightest”. Enclosure
soundness does not wait on that optimization proof.

Lean defines functions such as inverse and logarithm on inputs where a
numerical interval library might call them undefined. The computational
operation does not choose the mathematical convention. Each companion rule
must enclose Lean's actual function or require a proved domain cut before
using a tighter theorem.

### Outward regularization

`regularize p I` widens finite endpoints onto the grid `2^-p · ℤ`. It rounds a
lower endpoint down and an upper endpoint up. It never
replaces the strongest fact in the solver. Instead, it creates a cheaper view
that a later rule may use.

If an endpoint moves, the regularized cut is strict: a moved lower endpoint
is strictly below the old lower endpoint, and a moved upper endpoint is
strictly above the old upper endpoint. An unchanged endpoint inherits its old
strictness. This is the candidate strongest sound outward view and makes
regularization idempotent without throwing away useful strict inequalities;
the same rounding-characterization lemmas used for grid-tightness must certify
both claims.

This distinction matters. Exact dyadic numerators can still grow rapidly.
Discarding a strong fact to shorten it would make the state order-dependent.
Keeping both the strong fact and a regularized working view lets the policy
trade precision against arithmetic cost without losing information.

The backend-comparison milestone also builds a separate exact-rational search
prototype. Its regularizer uses continued-fraction convergents or
semiconvergents to find low-height outward bounds under a denominator budget.
It is not silently substituted for the dyadic prototype: retained proof
traces must identify their endpoint encoding, and adopting rational working
facts requires an explicit representation revision before formats are frozen.
The dyadic backend is the first hypothesis because its bit-height contract and
kernel certificates appear simpler, not because this SPEC assumes the
experiment's outcome. The comparison records total search, proof construction,
and replay cost. A small arithmetic microbenchmark alone is not enough to
settle the public representation.

## Shared expression program

The frontend first reifies terms into a typed single-assignment base program.
Each instruction refers only to earlier instruction identifiers. Common
subexpression elimination occurs before search, so the array is also a compact
encoding of an expression DAG. The base is immutable after validation. A
separate, bounded extension mechanism may add proved-relevant expressions as
search discovers useful shapes; eager pre-materialization, epochal extension,
and fully append-only extension are candidates to compare rather than a choice
already frozen here.

Conceptually:

```lean
structure Node where
  domain : DomainId
  op     : OpId
  args   : Array NodeId

structure Program where
  operations : Array OpKey
  nodes      : Array Node
  consumers  : Array (Array NodeId)
  equalities : Array EqEdge
```

An `OpKey` identifies the semantic operation at a node, including its domain
signature and normalization variant. An `OpId` is only a compact index into
the program's operation table. A `RuleKey` instead identifies one propagation
method, with a stable name and certificate-schema version. Several
`RuleKey`s may apply to the same `OpKey`; neither the node nor its mathematical
meaning changes when the policy selects a different method. This distinction
also prevents a dynamically registered user rule from being mistaken for an
instruction understood by the fixed natural-evaluation checker.

Registrations are a validated factory layer, not the hot scheduler data.
Binding a registration to a matching node resolves its relative result and
argument slots into a concrete rule application containing an anchor, an
ordered read list, and an ordered write list. The dependency index maps each
read node to the concrete applications that must wake when its fact changes.
The scheduler sees only these concrete identifiers; it does not inspect an
operation key to infer that, for example, addition reads two arguments or a
contractor writes one of them. Later shape rules may propose validated
cross-node applications without changing the scheduler protocol.

The current arbitrary-propagator experiment gives each request a bounded,
immutable `ProgramView` containing the exact program version, operation table,
SSA node table, per-node theorem-instantiation generations, and per-node
structural expression depths. It contains no facts.
The engine constructs it only from a validated state already covered by the
operation, node, arity, generation, and structural-depth limits. Thus an
external shape rule can follow a product argument to a nested difference,
compare opaque operation keys, recover the repeated `NodeId`, and construct a
proposal without duplicating either engine-owned depth calculation. It still
receives facts only for its registration's declared watch slots. Structural
inspection does not become a hidden fact dependency.
`ProgramView.findOp?` resolves a stable `OpKey` to this snapshot's local
`OpId` and exact signature; package assembly order is never authoritative for
frontend node identifiers.
`ProgramView.depth?` exposes the engine-owned structural depth as advisory
matcher data, so a package may avoid proposing an alternate which is already
obviously too deep. It is not admission authority: the engine recomputes the
complete proposed suffix against its current depth table.
Structural inspection is restricted by a provenance contract. A matcher may
follow nodes determined by its action anchor. Every additional side node which
affects the theorem instance must be present either as a declared fact input
or as an explicit `existing` reference in the proposal. Those are the two
places engine-owned generation accounting can see it; merely calling
`ProgramView.node?` on an arbitrary identifier does not make that node a
generation dependency.
Anchor-local inspection adds no wakeup beyond the declared fact slots; a rule
which reads the whole view declares `watchesProgram`, making program extension
an explicit dependency.

The transparent structural-cursor module is the reference semantics for
bounded whole-network matching. Within each epoch it enumerates the
append-only node, equality, and concrete-application identifier spaces in that
fixed order. Each epoch freezes its three size ceilings; growth cannot move
the unseen suffix, and renewal after exhaustion exposes exactly the appended
delta. A batch consumes the minimum of its yield quantum, the epoch remainder,
and the remaining cumulative visit budget, so a final partial allowance is not
stranded.

Live ownership is stricter than the transparent model. A whole-network matcher
uses one `global` application per registration, anchored at the first node
whose operation has the declared head. Later nodes with that head do not
compile duplicate global scans. The engine stores its cursor in an array
aligned with concrete applications and keeps a prepared next cursor outside
the registry request. The package receives only the exact bounded list of
structural identifiers and engine-owned creation generations. It supplies no
cursor and no completion claim. A valid reply commits the prepared cursor and
the exact cursor-delta visit charge; a retained retry which replays an already
committed batch has zero cursor delta and does not pay for those visits again.
Cursor progress is monotone within an authenticated epoch; backwards or
cross-epoch progress is rejected. A mismatched or malformed reply commits
nothing. An unexhausted epoch requeues the same application. If append-only
growth occurs while that application is already queued, exhausting its old
frozen ceiling still requeues it when the live view is larger; queue
suppression therefore cannot lose the appended delta. Renewal exposes only
that delta.

The FIFO and replaceable-policy schedulers use the same matcher preparation.
Policy invocation keys include the batch and epoch. Exhausted matcher-visit
capacity remains a visible blocked offer whose selection reports the exact
engine resource; it cannot disappear and manufacture a false fixed point.
Policy traversal charges the configured batch bound before constructing live
invocation keys, and charges the exact retained structural-input list as part
of a suggestion key. The present implementation conservatively treats every
item in an issued batch as a causal input for theorem-instantiation generation.
A future engine-compiled matcher may return a smaller engine-validated match
certificate, but an external package may not under-report causal reads merely
to evade generation limits.

The experimental `Engine` record and transparent cursor constructors remain
public for mutation and representation comparisons. Production obtains the
authority boundary by hiding the engine constructor, not by claiming that the
reference cursor type itself is unforgeable. Selective operation-key indexes,
compiled patterns, and richer equality/application projections remain
compatible replacements for the reference enumerator; they must preserve its
batch, generation, replay, resource, and completion semantics.

`ProgramView.programVersion` equals the engine-owned version in the action for
that invocation. An append-only extension creates subsequent requests with
the new arrays and version. An anchor-local proposal may remain fresh when its
concrete application and declared fact versions are unchanged; admission still
resolves references, CSE hits, types, equalities, and generation against the
current validated program. A `watchesProgram` action instead requires the exact
program version: extension stales its old proposal and requeues the existing
application to obtain a fresh view. A meaning-changing application replacement
or watched-fact change also makes an action stale. Policy selections made
against a current snapshot retain their separate exact program-version guard.
The external registry assigns meaning to keys such as product, difference, or
a distinguished constant. The engine supplies only exact lookups and never
embeds those meanings.

This full bounded view is the smallest flexible candidate currently exercised,
not a frozen production interface. A compiled shape-pattern registration could
instead return validated bindings and a bounded match certificate, reducing
registry traversal and making structural-read cost engine-checkable. An
intermediate design could cache registry-owned bindings by canonical program
snapshot and anchor. Experiments should compare these against the view on
large shared DAGs and after repeated extensions. Any replacement must retain
the same separation: unrestricted validated structure is acceptable, but
facts and their versions remain available only through explicit watch slots.

The first concrete acceptance vertical uses two deliberately different
examples. For `z = 2*y`, the forward rule is initially inapplicable on the
one-sided-unbounded `y`, while the singleton-factor backward rule contracts
`z ∈ (2,6]` to `y ∈ (1,3]` and wakes the forward rule again. For
`x * (1 - x)` with `x ∈ [0,1]`, ordinary compositional propagation gives only
`[0,1]`; a fact-free structural rule recognizes the repeated node and proposes
`1/4 - (x - 1/2)^2`. Admission structurally validates the new node and
equality endpoints and retains an opaque payload for later semantic replay.
The alternate callback returns the candidate `[0,1/4]`, and the engine's
equality contractor narrows the original product to that fact. The identity
itself remains an obligation for the companion checker; neither semantic
pattern is built into the engine.

The caller supplies nullary nodes for free variables and named constants.
Unknown free variables begin with the whole interval. Hypotheses add source
facts. A known constant may instead have one or more nullary propagators, so a
constant such as `π` can improve its enclosure as effort increases.

The program is typed by construction in the frontend. The scheduler uses only
the compact identifiers. This avoids a dependent heterogeneous term language
inside the hot loop while leaving room for domains other than `ℝ` later.

An `EqEdge` connects two node identifiers that the companion can prove equal.
It may come from normalization, a local equality hypothesis, or a certified
instantiation. The Mathlib-free table records endpoints, scope requirements,
and a proof-recipe key; the validated companion program pairs it with the
actual equality proof. Equal nodes are not merged, so descendant equalities do
not introduce cycles.

### Bounded expression instantiation

A rule may match a shape already in the program and propose additional
expressions whose bounds make another rule applicable. This is analogous to
`grind` instantiating a theorem, but the products are expression nodes and
ordinary interval facts. Typical uses include:

- introducing the centered form `1/4 - (x - 1/2)^2` when bounding
  `x * (1 - x)`;
- deriving `1 - 2*x^2*y^2` from the source equality `x^2 + y^2 = 1` when
  bounding `x^4 + y^4`;
- introducing derivative, range-reduction, or function-specific alternate
  expressions only after their input range makes them useful;
- instantiating a monotonicity theorem by adding product or difference nodes
  that were absent from the original goal.

An instantiation proposal is retained under the selected action's versioned
`RuleKey`; its own `key : Nat` is only an untrusted family label for replay and
is not canonical authority. The proposal contains new SSA instructions,
equality or derived-fact recipes, and their opaque replay payloads. The engine
derives the canonical substitution from the selected action's anchor,
declared input facts, and existing nodes explicitly referenced by those
instructions and recipes.

For every suggestion which still has retained capacity, reply admission first
resolves its complete uncapped draft, checks operation arities and domains,
topological order, scope visibility and equality endpoints, and applies the
same CSE rule used by final admission. Only after that full structural check
does it compare `maxNodeDepth` with the freshly appended depth suffix; existing
program depths were validated when their snapshot was created. A malformed
request returns the named `ReplyError.malformedProposal` and invalidates the
whole reply before candidate facts or suggestions commit. A structurally valid
request whose new nodes exceed `maxNodeDepth` is instead an individually
recoverable loss: it is dropped and counted, does not consume retained
capacity, and later affordable suggestions in the same reply remain eligible.
The engine returns one exact kept/drop-reason plan with the accepted state.
`RuleObservation` preserves that same plan, and policy reads it directly
rather than rerunning structural validation. Losing an instantiation marks
policy completeness false, so the filtered reply cannot manufacture
saturation. Once retained capacity is exhausted, the remaining suffix is
dropped without structural validation, as it cannot enter live state. Full
admission revalidates a selected proposal against the current
append-only program before atomically updating consumer and rule indexes and
retaining opaque recipe identifiers. Policy view construction consequently
checks freshness and engine-owned generation without repeating draft
resolution.

The request has no package-claimed generation field. Policy sees the
engine-computed generation in the semantic offer key, and the accepted
instance records that same value for replay. Production must freeze every
referenced recipe value before replay. Base nodes have theorem-instantiation
generation zero. The production representation may record generation per
theorem instance or per generated product; that choice remains open below. In
either case, a new expression is not trusted merely because a trigger matched.

The authoritative recurrence for a retained instantiation is

```text
1 + max (
  the emitting application's action-creation generation,
  generations of every node in the action substitution,
  generations of every engine-issued structural matcher input,
  generations of every `.existing` reference in node drafts,
  generations of every `.existing` equality endpoint,
  generations of every `.existing` scope anchor, watch, or write
)
```

The action substitution is the action anchor followed by its declared fact
inputs, with duplicate node identifiers removed. In the reference matcher
every member of the bounded issued batch is conservative causal evidence,
including equality and concrete-application identifiers whose creation
generation is not otherwise a node reference. Proposed references are outputs
of this theorem instance, even when CSE reuses already materialized storage
for them; storage reuse cannot manufacture a proof dependency. Thus the same
append-stable proposal has the same logical generation before and after an
unrelated CSE-producing extension.

A successful equality-only or scope-only instantiation still consumes this
generation: its instance-history event records it, each newly admitted
equality edge is stamped with it, and each newly created scoped application is
stamped with it. Such an admission cannot reset a later chain merely because
it allocated no expression node. An instance which adds no node, equality, or
scoped application is instead a duplicate and does not consume an instance
event.

The current centered-product D2 vertical is deliberately narrower than this
general recurrence. Its `Center.inferredGeneration` only recognizes one
checked extension layer above an immutable base prefix and returns generation
one for that layer. It is a kernel-reduction canary for generation-boundary
validation, not the production algorithm for recomputing generations across
several accepted instantiation rounds. The scaling experiment must add
per-node provenance and exercise the recurrence above before that interface is
frozen.

The general propagation experiment uses the same admission boundary with
opaque operations. A selected proposal is resolved against an immutable
operation table, checked for typed SSA order, CSE'd against old and newly
proposed nodes, assigned an engine-recomputed generation, and committed
atomically with rebuilt rule and watcher indexes. Its two-step canary adds
`g (f x)` and then `h (g (f x))`; newly registered rules run through the
ordinary request/reply path, producing generations one and two. Exact node,
generation, structural-depth, application, queue, instance, equality, and
proposal-list limits are independent, and failure retains the preceding
snapshot. The current hot storage uses linear reference CSE and rebuilds
indexes after an extension; that validates the state transition but does not
select the production CSE or incremental-index representation.

For inspection and mutation-cost experiments this provisional `Engine` is an
exposed record. Consequently, its raw module does not enforce an authority
boundary against a caller who fabricates an entire record value. The
production engine must hide its constructor and expose checked observations
and transitions; making one transition opaque would not provide that
encapsulation and would obstruct ordinary-kernel theorems about admission.

One atomic theorem instantiation initially assigns the recurrence above to all
helper nodes, equality edges, scoped applications, and the instance-history
event it introduces. Proposed products are outputs, even when CSE reuses their
storage, so selection order cannot raise their logical generation or change
success at an exact generation cap. This measures theorem-instantiation depth
rather than expression-tree depth. Per-product or multiple-provenance
generation remains a possible refinement.

Structural expression depth is a separate engine invariant: nullary nodes have
depth zero; every fresh non-nullary node has one plus the maximum depth of its
resolved arguments; a CSE hit keeps the already stored depth. `maxNodeDepth`
caps this measure independently of `maxGeneration`. This distinction is
essential for whole-program matchers: a matcher can repeatedly propose
`g(anchor)`, `g(previous)`, and an ever longer CSE-hit prefix while every
theorem instance remains generation one. The growing-tower canary admits the
prefix through depth three, then drops the depth-four proposal without
aborting the rest of its reply. Its raw `drive` result is queue-saturated,
which deliberately says nothing about retained suggestions or propagation
completeness. A separate policy canary consumes the exact engine-issued drop
plan and records the lost instantiation as incomplete.

The general experiment activates proposed equality edges as indexed,
replayable search contractors: improving either endpoint wakes transport in
the other direction, and admission of a new edge considers both current
endpoint facts atomically. The edge payload remains untrusted, so an equality-
derived contradiction is only a search signal until companion replay validates
that payload. The first FIFO worklist still runs all compiled applications at
their registered effort. A separate policy experiment makes escalation,
retry, instantiation selection, and subdivision explicit state transitions
over the same generic application protocol. Neither limitation is a reason to
specialize the scheduler to rational operations or to bake function semantics
into it.

The raw `Propagator.drive` helper is only a bounded request/reply and equality
worklist harness. Its `RunStop.saturated` constructor means that this queue is
empty; the helper neither selects retained suggestions nor carries the policy
incomplete bit. Only `Policy.State` and its driver may turn an empty frontier
into proof-search saturation, and they return `unknown` when any
closure-affecting suggestion was dropped or dismissed.

### Equality activation

The initial production candidate treats each search-active equality as one
engine-owned, undirected contractor. It neither merges equal nodes nor presents
transport as a fake function rule to the external registry. The scheduler's
dependency item is therefore a sum:

```lean
structure EqualityId where
  index : Nat

inductive WorkItem
  | rule     (application : ApplicationId)
  | equality (edge : EqualityId)
```

Both endpoints watch the equality item. When selected, the item reads the two
facts and versions from one pre-step snapshot, rechecks that both nodes exist
in the same domain, and asks the domain intersection operation to narrow left
by right and right by left. It preflights the complete fact-history and wakeup
cost, installs zero, one, or two improvements atomically, and then wakes the
deduplicated union of rule and equality consumers. A single equality item,
rather than two independently queued directions, is important when two
incomparable partial facts can improve both endpoints to their meet.

Adding an equality is also atomic. Instantiation constructs prospective new
nodes, equality identifiers, evidence origins, rule applications, both kinds
of watcher, queued bits, and initial work items before committing any of them.
Every new equality receives one initial queue item, so propagation need not be
hidden inside structural admission. Whether new equality items precede new
function applications is policy data; equality-first is a useful first
experiment because an alternate expression receives the known bound before
its function rules run.

Equality work is visible resource usage: each run charges one work-item pop,
two domain intersections, dependency visits, zero to two accepted facts, and
all resulting queue insertions. The global step budget counts equality items
as well as registry invocations. Equality closure is never an unbounded
recursive side effect of waking a node.

Fact provenance distinguishes an external rule from transport:

```lean
structure FactRef where
  node    : NodeId
  version : Nat

inductive FactCause (Fact : Type)
  | rule      (action : Action) (proposed : Fact) (payload : PayloadId)
  | transport (equality : EqualityId) (source : FactRef)
```

The surrounding fact event retains the preceding target fact and the installed
result. A rule cause additionally retains the candidate exactly as proposed:
the installed result may be the intersection of that candidate with the
preceding fact, and neither value determines the other in a general partial
fact domain.
For transport, replay resolves the source fact, checks equality direction and
scope, reconstructs the equality proof, transports the exact source fact, and
then validates its intersection with the preceding target fact.

An equality's evidence cannot be only an untyped payload index. The preferred
shape makes it an output of a particular theorem instance, so one frozen
instance payload can justify several products and equalities:

```lean
structure InstanceId where
  index : Nat

inductive EqualityOrigin
  | source   (source : SourceId)
  | instance (instance : InstanceId) (output : Nat)
```

The retained instantiation origin includes the complete triggering action,
including its input fact versions, not only its rule and anchor. We leave two
evidence questions open for experiment. First, shape equalities might be
restricted to facts unconditional in their scope, or they might depend on the
interval facts observed by the trigger; the latter is more expressive but
adds those facts to replay dependencies. Second, several recipes may prove
the same endpoint pair with different scopes or proof costs. A production
table may separate one canonical transport link from several evidence records;
the first experiment may retain the first deterministic evidence.

Structural instance identity includes canonical unordered equality endpoint
pairs as well as the originating rule, engine-derived substitution, and
resolved products. An untrusted family label remains replay metadata but does
not manufacture a new network extension. Equality resolution
returns the identifiers of reused links as well as newly appended links, so a
pure-equality instance is replayable and cannot collide with an empty
extension. If every proposed node CSE-hits and every equality already exists,
admission reports a duplicate without advancing the program snapshot or
consuming an instance slot. Scope becomes part of this identity when branches are introduced.
Structurally admitted equality evidence is search-active but not trusted:
failure to reconstruct it rejects the eventual proof, just as a malformed
function-rule payload does.

The first structural scaling experiment deliberately keeps that same fixed
one-generation witness while varying dead nodes, relevant and irrelevant
facts, and adjacent versus far derivation references. Its evidence is recorded
in [the structural scaling report](../../reports/hex-interval-scale.md). At 500
facts, adjacent and far traces have identical dimensions but require 1,544 and
121,839 charged original-order list lookups and take median 51.4 and 164.2
microseconds in compiled replay. Fact cardinality is therefore not a sufficient
resource proxy, and original-order `List` lookup remains a transparent
reference checker rather than a production storage decision.

The next general trace representation exposes an endpoint-erased structural
skeleton. It records operation tags and operand references, literal slots,
trigger provenance and recomputed generations, proposal/deduplication keys,
equality edges, derivation references, caller-bound source/target slots, and
structural budgets, but not endpoint values. Endpoint backends may be compared
only when their accepted certificates erase to the identical skeleton. This
prevents Core rational normalization or dyadic projection cost from being
misreported as scheduler or storage cost.

Production experiments compare exact-index array, arena, and chunked layouts
against the list reference in both compiled and ordinary-kernel replay. Every
layout retains separate node, fact, edge, source, byte, and lookup/work caps;
the checker recomputes representation-level cost from validated references.
Whether scheduler fuel should count abstract logical references or concrete
storage steps remains empirical, but a certificate-supplied cost is never
trusted.

Instantiation is explicitly budgeted by new nodes, new equality edges, rule
applications, theorem-generation, structural node depth, and retained payload
bytes. A canonical key consisting of the rule, substitution, scope, and
generated expression prevents duplicate instances. Candidate traversal and
insertion order are deterministic. If a branch-local fact triggers a
semantically branch-independent expression, the node may be shared globally
while the resulting fact and conditional equality remain branch-scoped.
Whether the first implementation uses that scheme or branch-local extensions
is an experiment; identifiers and replay must make the choice explicit.

The initial feasibility comparison has three arms:

1. eagerly materialize every alternate admitted by the node/form budgets;
2. run bounded instantiation between propagation epochs, then validate and
   freeze a new program snapshot;
3. append nodes lazily during search with incremental dependency updates.

The corpus measures program size, duplicate instances, useful-instance ratio,
search time, and replay size. Safe budget exhaustion leaves the already
validated program and facts usable.

#### Instantiation certificate boundary

The proof-facing checker treats the proposed program extension, recipe
witnesses, equality edges, propagation facts, and selected result index as
untrusted certificate data. The caller separately supplies the immutable base
snapshot boundary, initial source rows, requested target row, and every
resource limit. Successful replay proves exactly that caller-selected target
from exactly those caller-supplied sources; certificate fields cannot replace
either side of this implication. In the tactic, the caller obligations are
discharged from reification and local hypotheses, rather than accepted as
external axioms.

Validation proceeds in a fail-closed order:

1. bounded-length checks stop after one constructor beyond each trusted node,
   source, equality, and fact cap;
2. every program literal is endpoint-preflighted, including a dead literal
   not reached by the selected trace;
3. SSA topology and the trigger's exact source and generated instruction
   shapes are checked against the caller's base boundary;
4. the selected witness must contribute its exact equality edge, and every
   retained edge is independently checked against the same base boundary and
   generation cap;
5. each propagation fact uses exact optional lookups of existing program,
   source, equality, and prior-fact entries; and
6. an in-bounds selected fact must equal the caller's target row exactly.

The generic soundness API exposes introduction and elimination lemmas for
source-table invariants and row membership, so a downstream frontend can use
the checker without unfolding implementation-private definitions. Source rows
may soundly describe any existing node, including a composite expression,
because each is an explicit theorem hypothesis. Whether the first frontend
offers only variable-domain bindings by default, while reserving composite
source facts for hypotheses and imported solvers, remains a policy question;
the generic checker does not impose that restriction.

A small proof-facing implementation may use original-order `List` facts with a
newest-first accumulator, provided it rejects forward references. In the D2
canary, `maxLookupSteps` charges indexed derivation lookups—including traversal
to prior facts—and the final-result lookup. It is not a unified counter for
every constructor visited by the checker: whole program, source, equality,
and fact scans are separately bounded by `maxNodes`, `maxSources`, `maxEdges`,
and `maxFacts`. In particular, the reference centered checker does not add the
equality-recipe checker's program-list traversal to `maxLookupSteps`; it only
bounds that work indirectly. The current `centerV1` checker performs nine
program lookups for the selected center and nine for every equality edge, for
a list-constructor bound of `9 * (maxEdges + 1) * maxNodes`. An edge-padding
workload must measure this dimension independently. Production replay either
charges every such traversal or uses validated random access—the product bound
is not the desired final accounting model. This representation and accounting
split is experimental, not the production storage decision. Array, chunked,
and arena-backed traces remain candidates; they must implement the same
exact-index, caller-bound, and explicit work-accounting contract. A
correspondence theorem between stored original indices and the chosen replay
layout is required when that layout is selected.

## Rule protocol

Rules are explicit registrations, not typeclass instances. Typeclass search
must not recursively decide which algorithm computes an expression's bound.
The registry may contain several rules for one head symbol, and the policy may
try or combine all of them.

A registry snapshot is assembled from independently upgradeable function
packages. The current canary chooses an ordered `Array (Package Fact)`. Each
package existentially owns one private `Cache` shared by its handlers and
contributes owned operation signatures, exact external signatures required by
its matchers, `(Registration, callback)` pairs, and a package-owned limit
preflight over both the engine and proof-arena envelopes. A handler head must
be declared as owned or required.
`Registry.buildWithin` bounds package and metadata counts plus arities before
flattening, builds a `Route` from each compact `RuleId` back to its package and
handler, and rejects undeclared heads and duplicate `OpKey`s or `RuleKey`s.
The registry constructor is private: callers can inspect a checked snapshot
but cannot forge inconsistent flattened routes. Executable operations,
aggregate registry metadata, and replay-format declarations have independent
limits; adding a proof recipe cannot buy space by relaxing the frontend's
operation cap.
Program size and arity are bounded before exact signature lookup. The checked
session start validates every owned and required signature against the final
frontend program, runs each package's configuration preflight, and starts the
engine with the registry's exact flattened registration array. Registry-owned
dispatch diagnostics impose their own `maxDiagnosticValue` floor even when
every callback package would accept a smaller value. The concrete reciprocal
package additionally checks both endpoints of its configured effort-to-
precision ladder against its arithmetic endpoint-height limit; otherwise a
configuration known in advance to exceed the backend limit is rejected at
start rather than advertised as compatible.

Each scoped handler also owns a fail-closed semantic validator for concrete
bindings of its registration. The registry first repeats the generic
structural checks, then routes the binding to that exact handler. A checked
session installs the same routed validator in the engine, so retained matcher
proposals, dynamic admission, and later scoped dispatch cannot disagree about
package acceptance. The proof replay layer must still justify the resulting
contractor theorem; this validator controls which package contract may be
invoked, not whether that contract is sound.
The registry exposes a whole-table check for direct-engine callers which
supply start-time bindings; the current checked session starts with an empty
binding table and exercises dynamically proposed scopes.

`Registry.invokePlanned` cross-checks the flattened registration, routed handler
metadata, and structural projection of an engine-produced request before
entering the callback, then replaces only the selected package's cache. It
returns a plan containing the outcome and all reply-local payload drafts,
paired with the exact selected handler's immutable replay snapshot. The
planned route is proof-producing, but neither it nor
`Registry.invokeDroppingDrafts` is an authentication boundary: the engine
still authenticates the pending serial, application, fact values, and
versions. The explicitly named dropping-drafts adapter discards drafts and
replay metadata only for search experiments. Registry, replay-snapshot, and
invocation constructors are private; the checked builder and routed invocation
are their only producers.

Each handler now carries cache-independent replay-format declarations beside
its registration and callback. A declaration consists of a payload role, a
rule-local numeric schema variant, and a body-shape validator. The immutable
dispatch key is `(RuleKey, role, schema)`: two unrelated function packages may
reuse the same role and local schema number without sharing a validator.
Registry assembly rejects duplicate `(role, schema)` declarations within a
handler, and counts declarations against a dedicated replay-format bound as
well as the aggregate metadata bound.

There are two independent version axes. `RuleKey.schema` is the compatibility
epoch for the complete handler and companion theorem contract. The payload
`schema` in a draft or arena entry is a recipe variant within that exact rule
epoch and semantic role. Replay requires an exact match on the whole
`(RuleKey, role, payload schema)` address. It never selects the newest
`RuleKey.schema`, and it never dispatches from a payload schema alone.

`PayloadSession.Session` has a private constructor and its checked start owns
the matching engine, registry, arena, and arena limits; the bounded `Run`
result also has a private constructor, so its stop classification can only
come from session execution. During an invocation, generic arena preflight
first bounds the number of drafts, body cells, atoms, schemas, and payload
uses. Only then does the session run the selected package's body validators.
The selected immutable `ReplaySnapshot` supplies its rule owner and validator
to one paired freeze operation, so the proof-producing path cannot mix an
owner from one package with a validator from another. It rejects an undeclared
role/schema pair or malformed body without committing the prospective arena or
engine outcome.
Package caches may record the failed attempt because they remain non-semantic.

The format API validates representation shape only; it does not itself attest
that a body proves the proposed interval fact, instance, or equality. The
cache-free semantic replay protocol separately assembles theorem schemas
package-for-package against one sealed executable registry. Its constructor is
private, and its checked builder requires exact bidirectional coverage between
package-owned theorem schemas and executable formats for all three roles on
the complete `(RuleKey, role, schema)` key. Thus a checker from another
package cannot be selected merely because two rules reuse a numeric schema,
and a registry with an unchecked fact, instance, or equality format cannot be
used for proof replay.

The three semantic claims are deliberately different. A fact schema proves
its proposed fact from the exact already-checked input facts. An instance
schema proves that every model of the program before the extension has a model
of the extended program which agrees on every old node; this conservativity
obligation prevents a partial or inconsistent package-defined operation from
manufacturing a proof by adding an uninhabited expression. An equality schema
proves the exact retained endpoints equal, optionally under an exact list of
already-checked facts for conditional identities. Instance replay additionally
requires an unchanged operation table: search-time instantiation may append
nodes but may not redefine a registered function.

Public replay follows the `PayloadId` retained by a rule cause, instance
event, or equality edge into the immutable arena, checks its semantic role,
and compares the complete originating `Action` before typed dispatch. Matching
only a serial, rule key, or body schema is insufficient. The chronological
checker remains responsible for reconstructing the exact program step,
fact-prefix assumptions, instance event, and equality edge before invoking
these package-owned theorem builders.

The first chronological transition composes a retained rule theorem into a
theorem about the fact actually installed by the engine. Given a previous fact
and ordered action-input facts resolved from the already-checked prefix, it
checks the event/action program version, previous-node pointer, and declared
input-node order; replays the package-owned proposed fact; independently asks
the fact-domain schema to prove `installed ↔ previous ∧ proposed`; and returns
that the installed fact follows from the caller's base assumptions. Supplying
the resolution evidence explicitly is intentional at this stage: this
transition cannot inspect a future event or the engine's final mutable fact
slots. The arbitrary-function contractor event exercises this composition
against the actual policy-session history.

The prefix resolver returns an exact fact together with its theorem for a
requested `(node, version)`, and builds the rule's ordered input list by
traversing the immutable `Action.inputs`. The rule transition consumes this
resolver directly. A request for a positive version absent from the checked
prefix therefore fails before recipe dispatch; the conformance test mutates
the previous pointer to the event's own version and observes this rejection.
The fixed-program prefix has a private constructor. Its checked start exposes
the seed resolver only at version zero, and a successful rule event appends
exactly its proved positive version. Replaying the same `(node, version)` is
rejected as a duplicate. The stable-step transition described below lifts this
prefix across an instance transition. `TraceReplay` drives these transitions
over the complete interleaved event history and checks exact exhaustion of
every detailed history array.

The executable engine retains one compact authoritative `chronology` array
whose entries select either an exact fact-history index or an exact
instance-history index. The role-specific arrays retain the detailed records;
the compact array fixes their cross-order without copying them. Equalities
become available at their owning instance event. Each `InstanceEvent` records
both its proposal-order equality outputs and the exact fresh equality suffix,
so replay can distinguish a reused identity from a newly introduced edge and
reject a reference to a future edge. A complete fold consumes every chronology
entry and every role-specific record exactly once.

The corresponding equality-transport transition checks that the retained
source is the opposite endpoint of the exact edge, replays the package-owned
equality theorem under its resolved conditional assumptions, transports the
source fact through a fact-domain law saying equal semantic values satisfy the
same fact, and validates the target meet before returning the installed-fact
theorem. Before using that law, replay checks that both endpoints exist in the
current program and have the same domain. A canary drives this route with the
equality produced by the arbitrary-function matcher; the generic engine still
has no sine case.

The instance transition checks that the retained event advances exactly one
program version from its originating action, replays the package-owned
conservative-extension theorem, and composes it with the already-checked
extension from the caller's base program. This composition admits reflexive
semantic steps because a pure-equality or pure-scope instance may change
scheduler structure without appending a node.

Chronological replay also needs the opposite, prefix-facing semantic
direction. For each append-only program step, the semantics adapter supplies
that a model of the enlarged program is a model of the old prefix and that a
fact on an old node has the same meaning in old and new models whenever those
models assign that node the same value. This is separate from, and
complementary to, the package theorem that every old model can be extended.
The checker uses these laws to lift all previously proved fact versions into
the enlarged program. It then seeds every genuinely new node at version zero
with the fact-domain top theorem. The old resolver is consulted first, so an
initial fact supplied by the caller is never silently replaced with top. A
conformance fold starts from the original graph, replays the actual
arbitrary-function instantiator, lifts the fact prefix, seeds its two new
expressions, and only then replays the dynamically installed propagator. This
path depends on no rational representation and contains no generic function
case.

The runtime `TraceReplay` experiment currently receives an `InstanceBuilder`
which reconstructs the next concrete program and its `StableStep`. This is not
yet the intended production ownership boundary: a single callback could hide a
central case split over function keys. The transparent
`GenericInstanceReconstruction` comparison arm reconstructs the next program as
the exact prefix of the retained final node array selected by
`event.newNodes`, keeps the operation table fixed, and obtains stability from
one semantics-wide prefix-locality law. It covers both ordinary node appends and
zero-node version-only instances. The direct proof emitter now uses this arm
at every quoted instantiation event: it replays the owning package's
conservative-extension theorem, lifts every retained fact proof through the
semantics-wide stability law, and seeds exactly the event's fresh nodes with
top. Integrating the same arm into runtime `TraceReplay` and comparing it with
package-dispatched reconstruction remains experimental. Neither arm may
introduce a central enumeration of functions.

The private chronological cursor is indexed by its exact program version and
program value. Its instance transition requires the originating action to
name the cursor's current version, the event to advance it by exactly one, and
`newNodes` to be exactly the appended node-index range—not merely a
self-consistent list supplied by the event. It then composes the structural
prefix, package-owned conservative-extension theorem, and stable fact prefix
into the next cursor. Its rule transition similarly requires the event's
program version to equal the cursor's. The arbitrary-function canary verifies
that a future generated node has no version-zero fact before instantiation,
that it receives top afterwards, that an old base fact remains available, and
that the dynamically installed contractor's positive fact version appears
only after its rule event. Mutually consistent but cursor-stale versions and a
mutated `newNodes` list fail closed.

The complete checker starts through its canonical `TraceReplay.startInput`,
which constructs one node-indexed assumption from every
`CheckerInput.initialFacts` entry and checks that the array has the base-program
node count. It does not accept an arbitrary version-zero resolver. Final
closure first asks the fact-domain schema to prove that the resolved result is
contained in the caller-selected target. It then uses the accumulated
conservative extension and semantic stability evidence to transport that
theorem back from the final extended graph to the caller's original graph.
Both the target node and every base assumption must belong to the original
program.

Compiled search, package caches, and the private execution cursor may remain
opaque, but a compiled `.isSome` or `#guard` result is not a Lean proof. Proof
production therefore has two viable architectures which remain open to
measurement: quote the plain trace into a transparent proof-only fold, or have
the tactic emit direct applications of the generic rule, meet, equality,
extension, and closure lemmas selected by that trace. In either design the
kernel sees only ordinary theorem applications and transparent certificate
checks; `native_decide` is not a bridge across opaque execution. The
chronological conformance includes an ordinary theorem term following the
second route through a sine-shaped contractor, an independent negation step,
equality transport, and caller-target closure. Runtime `#guard`s remain useful
mutation tests, but never satisfy the theorem-production gate by themselves.
The transparent `ProofEmitter` implements the direct-emission route for
quoted instance, rule-fact, and equality-transport events. It checks each full
replay address plus its frozen origin and payload link. Instance replay checks
the version step and exact appended-node suffix; rule replay checks ordered
fact inputs and write authority; transport checks ordered equality assumptions
and endpoint orientation. The transitions then compose package theorems with
the generic extension, meet, transport, and closure lemmas. The real-sine
conformance quotes all four live events and proves each successful replay by
ordinary `rfl`; the resulting dependent proof chain yields the caller's
ordinary `Real.sin` theorem. The opaque engine supplies plain event data to
the elaborator but is absent from the emitted theorem.
The first elaborator canary runs the opaque real-sine planner, searches the
returned state for the instance, two rule facts, equality edge, payload
entries, and versioned input facts, and reifies all four proof steps as
ordinary Lean expressions. From each payload's full replay address it selects
the package-contributed schema declaration, then emits the instance, sine,
negation, equality-transport, and caller-closure applications in dependency
order. Every accepted `Option` result carries an ordinary `rfl` success proof;
if the quote or schema is wrong, elaboration fails. The assigned term consumes
the actual returned quote and reified final program. Its checked literal event
chain is a separate field-for-field regression and cheap goal-shape probe.

`Frontend` now performs function-independent quotation of any engine history
into instance, rule, and transport records, with exact role-local ordering and
history exhaustion. `ProofFrontend` is the reusable direct proof assembler.
It walks an arbitrary quoted event list and maintains an exact
`(node, version)` evidence table. Rule and transport steps obtain their
previous facts and ordered dependencies from this table, select their package
schemas solely by replay address, and insert their proved result versions.
The same fold accepts instantiation events at arbitrary chronology positions.
It reconstructs each intermediate graph as the exact prefix of the reified
final program, carries the independently established program version,
transports the complete evidence table across stability, and then seeds the
new-node suffix. A second zero-node instance can therefore advance the version
after the sine and negation rules while preserving the negation evidence needed
by a later equality transport. Reordering negation before the sine result it
consumes, or claiming a wrong rule or transport program version, fails before
replay.

The fold is polymorphic in the fact type and contains no sine, negation, or
other function case. Its `Context` receives the semantics/domain laws,
prefix-stability theorem, caller program and facts, and a plain-data encoder;
packages remain responsible for their replay schemas. The real-sine tactic is
now a client of this module rather than the owner of the fold. Its semantic
bridge and final proof closure still name the canary's fixed base graph and
target; the goal reifier below begins removing that specialization.

A second live vertical validates this separation with `Real.exp`. Its
Mathlib-free package uses a distinct three-element fact lattice, contributes
one unconditional nonnegativity propagator, and has neither instantiation nor
equality transport. Its Mathlib companion contributes only real semantics and
one replay schema. The same policy session, joint package registry,
fact-polymorphic quotation, shared structural encoder, and generic evidence
fold produce the ordinary theorem `0 ≤ Real.exp x`. Thus both a multi-package
graph-growing sine proof and a single-rule exponential proof pass through the
same frontend API without a function switch.

The first goal-reification experiment now derives the exponential canary's
base program, version-zero fact array, and target fact from the actual Lean
goal before running its compiled fixture. Expression packages contribute an
opaque operation signature and a Lean-expression recognizer; the reifier has
no switch for exponential, sine, or any other mathematical function. It tries
all packages with the required output domain, requires a unique match and
exact arity, and runs each recognizer without retaining changes to elaborator
state. It recursively reifies arguments in signature order, performs exact
expression/domain CSE, validates the resulting SSA program, and enforces
package, node, and depth limits. A separate fact parser maps propositions to a
term, domain, and fact, so interval endpoint and open/closed semantics do not
enter graph construction. Parser calls likewise retain no elaborator-state
changes. The target is reified first and is strict: an unsupported or
over-budget target fails. A parsed hypothesis is optional information; if its
term or a recursive dependency has no package or exceeds the remaining graph
budget, that whole immutable attempt is discarded. Malformed arity and
ambiguous package matches remain hard registry errors. All accepted hypotheses
narrowing the same version-zero node remain in an ordered seed recipe; later
hypotheses cannot overwrite an earlier proof dependency, while facts about
other recognized expressions may append a suffix after the target graph. The
exponential tactic currently requires only the target-reachable operation and
node prefixes, and the target fact, to match its fixed semantic/proof fixture.
Extra supported, duplicate, unsupported-real, and non-real hypotheses therefore
do not disable an otherwise applicable proof; later operation packages may
also extend the registry after the target prefix. Removing that last prefix
comparison requires package-compositional construction of the program
semantics and generic proof emission for the recorded top/assumption seed
recipes. `GoalClosure` supplies those two proof bridges, and the dynamic
exponential vertical below now starts compiled search on the resulting checker
input. A general policy-driven target-closure loop remains future work rather
than an assumed capability.

The first package-composed semantics experiment removes a second fixed-graph
assumption. An operation-meaning package supplies an opaque operation signature
and a relation from its ordered input values to its result value. The assembled
model requires the program's operation array to equal the aligned package
array and requires a successful meaning lookup for every node; an absent or
mismatched package therefore cannot make an expression unconstrained. This
makes full package alignment a proof-production obligation, not merely a
registry convenience: until the frontend supplies that equality and a meaning
proof for every node, `Models` may be uninhabited and an `Entails` theorem by
itself may be vacuous. Appending or reordering syntax packages therefore also
requires assembling the correspondingly aligned meaning array. This
node-local semantics supplies one generic append-only stability law. The
exponential companion now assembles independent source and exponential
meanings, and its positivity schema checks an arbitrary proposed node's
instruction, the exponential package's current operation slot, and unary
argument before proving the result. Key-resolved lookup replaces that
canary-specific numeric slot before packages may be reordered. A
three-node `exp (exp x)` canary obtains an ordinary theorem through that schema,
while applying it to the source node fails closed. The `GoalClosure` experiment
below supplies the kernel-checked link from syntax packages to their operation
relations and generically discharges the reifier's top and ordered-assumption
seed recipes. A recognizer match alone is never treated as semantic evidence.
This first adapter uses one semantic value type for all domains. A later
multi-domain adapter must choose and validate a tagged universal value or a
domain-indexed valuation rather than pretending heterogeneous values have one
untyped representation.

The first kernel link from the goal graph to this semantics is also generic in
the mathematical operations. Each goal-closure package carries its opaque
operation, the corresponding semantic model term, a kernel proof that the two
operations agree, and a callback which constructs the model's relation proof
for concrete argument and result expressions. The assembler first requires
the complete package operation array to equal the reified program's array. It
then checks that the term table covers every node in exact SSA order, builds a
total valuation from those terms, and emits one package-owned relation theorem
per instruction. A recursive `Meanings` proof turns those node theorems and
the package-by-package alignment proofs into `semantics.models` for the exact
reified graph. Missing packages and a callback returning an unrelated proof
both fail during elaboration. Recognizer success is not used as evidence.

The same bridge constructs the caller-fact premise without arithmetic or
function cases. Canonical version-zero facts begin at the domain schema's top
theorem. Each recorded hypothesis must typecheck as its parsed semantic fact;
the bridge reruns the runtime narrowing operation and the independent
`proveMeet` schema in the recorded order until it reaches the exact installed
base fact. It then supplies all base facts to the emitted replay theorem. The
exponential canary now has an ordinary `interval_exp_model` theorem whose
value assignment, complete operation model, and caller facts come from the
actual reified goal. One variant closes from the live exponential replay; a
second consumes a caller hypothesis through the ordered seed path. Neither
uses `native_decide`.

The next experiment removes the exponential canary's fixed compiled trace.
It starts `PolicySession` from the reifier's actual `CheckerInput`, selects an
offer anchored at the actual target node, quotes that resulting session, and
feeds it to `ProofFrontend` with the dynamic base program, facts, and reflexive
extension proofs. The ordinary tactic theorem now accepts an unrelated
supported exponential hypothesis which appends two nodes after the target,
and it proves `0 ≤ exp (exp x)` from a three-node target graph. Neither case
adds a nested-exponential or extra-hypothesis branch to goal closure, semantic
model construction, dependency assembly, or proof replay.

The target-run experiment removes that one-rule scheduling restriction.
`TargetRun.Controller` is polymorphic in the fact type and in arbitrary
policy-private state. It sees only bounded engine-owned views, chooses or
dismisses checked offers, and receives every recoverable observation in order.
The driver retains the single proof-producing `PolicySession` and stops
distinctly on target subsumption, saturation, contradiction, explicit policy
stop, a prepared split, incompleteness, fuel, malformed state, or each resource
class. It derives selections from the chosen offer and the exact view identity;
packages and function names do not occur in the driver.

Target subsumption is a runtime stopping test: narrowing the current fact by
the requested fact must report no change. The result records the exact current
fact and version, but neither that test nor the controller is proof evidence.
`ProofFrontend.closeTarget` resolves that exact retained proof and applies the
transparent `ProofEmitter.closeFact` combinator. The combinator independently
asks `FactDomainSchema.proveMeet` to prove that intersecting the established
fact with the requested fact leaves the established fact unchanged; only that
kernel theorem supplies the requested conclusion. A conformance theorem closes
`.all` from a strictly stronger `.nonnegative` fact through the transparent
`closeFact` combinator. The live frontend canaries exercise `closeTarget` with
an exact retained target fact; an end-to-end strict-subsumption frontend
canary remains useful coverage rather than a delivered claim.

The exponential conformance policy simply selects the first offer. On
`exp (exp x)` it therefore improves the inner and outer nodes in two separate
steps, stops at the requested outer bound, and feeds both chronological events
to the unchanged generic proof frontend. The driver returns split plans but
does not yet create or join proof branches. The operation registry also remains
the fixed source/exponential pair. Key-resolved semantic model selection must
land before operation packages may be reordered; array position is not a
permanent package identity.

### Solver-split proof boundary

A prepared `SplitPlan` is not a case split theorem. It proves only that an
engine-owned offer was selected against the exact scope, program version,
node version, current fact, and resource envelope. Three independently checked
objects must remain distinct:

1. the untrusted policy plan, which chooses where and when to split;
2. a domain-owned coverage theorem for the exact parent fact, cut, and child
   facts;
3. one kernel proof of the requested target under each child assumption.

The proof-side interface is polymorphic in both `Fact` and `Cut`. Its essential
field has the following shape:

```lean
proveCover :
  (program : Program) -> (node : NodeId) -> (parent : Fact) -> Cut ->
    (left right : Fact) ->
    Option (Evidence (
      forall valuation, semantics.models program valuation ->
        semantics.holds program valuation { node, fact := parent } ->
          semantics.holds program valuation { node, fact := left } \/
          semantics.holds program valuation { node, fact := right }))
```

Thus executable child construction is checked a second time by the semantic
domain package. The current transparent `ProofEmitter.replaySplit` implements
the generic join. Given a proof of `parent` from the caller's `base`, a proof
of the target from `{node,left} :: base`, and a proof of the target from
`{node,right} :: base`, it applies `proveCover` and returns a proof of the
target from `base`. No policy callback, compiled session, branch score, or
runtime comparison enters that proof. A Mathlib-free Boolean canary consumes
both distinct child assumptions and obtains an ordinary theorem through this
join; swapping the quoted children is rejected.

Coverage is the logical requirement. Disjointness, nonempty children, and a
strictly interior cut are search-progress requirements: omitting them cannot
prove a false theorem, but can duplicate work or cause a split loop. The real
interval adapter should enforce the stronger v1 convention that a dyadic cut
produces `parent ∩ (-∞,m]` and `parent ∩ (m,+∞)`, preserving a closed boundary
on exactly one side. Open/closed and unbounded endpoint information therefore
lives in `Fact`; the generic join does not erase strictness or assume a closed
interval representation. A future non-real domain may use another `Cut` type
without changing function packages or the join theorem.

Branch execution needs a provenance-aware root rather than a fresh list of
unconditional assumptions. At a split point, facts already proved in the
parent remain parent proofs. Exactly one new child fact is conditional on the
corresponding case. If a child engine is restarted from the parent's complete
fact array with the split node narrowed, its version-zero proof table must
classify every entry as either:

- an inherited parent `FactProof`, lifted into the child context; or
- the single left or right split assumption.

It must not feed all inherited derived facts to `ProofEmitter.assumed`: that
would silently promote consequences of the caller's context into new caller
hypotheses. The existing caller `InitialContext` is consequently not the
branch-root API. The transparent `ProofEmitter.BranchSeed` now binds the exact
child `initialFacts` array and its length to this mixed proof table. Its checked
builder obtains the split-node entry only from the new child assumption and
requires an inherited parent theorem for every other array entry; the
Mathlib-free canary checks both routes. The Meta frontend still needs to turn
such a `BranchSeed` into version-zero `FactProof` records before chronological
child replay.

Branches may instantiate different auxiliary expressions. Each child replay
therefore closes its target back to the program snapshot at the split before
the two results are joined. The package-owned `Extends` theorem and semantic
stability law already provide the required direction: extend a split-snapshot
model into the child program, use the child theorem there, and transport the
old target back. Nodes, equality edges, payloads, and positive fact versions
created below one child are scoped to that child and cannot be resolved by its
sibling. Parent program nodes and proof terms may be shared structurally.

A runtime contradiction flag is also not a closed child. The proof layer needs
a domain-owned refutation schema which turns an exact established bottom or
inconsistent-bound fact into `False`; generic elimination can then produce the
branch target. Until that schema exists, a contradictory child is useful for
search diagnostics but cannot participate in a completed join. An unexplored,
fuel-limited, resource-limited, incomplete, or merely saturated child likewise
does not close the parent target.

The first branch manager should retain a tree whose internal node records the
validated plan and checked child facts, and whose leaves retain either a target
proof, a checked contradiction, or an explicit unfinished result. It may emit
a theorem only when every coverage child is closed. For best-bound mode,
unfinished leaves contribute their inherited parent fact to the global hull;
they never inherit a tighter sibling fact. Split depth, total created scopes,
live leaves, and total branch decisions receive separate limits in addition to
the per-session engine and payload limits.

Several operational choices deliberately remain experimental:

- restart a child session from a checked snapshot, or add a sealed session-fork
  operation which preserves reusable work and immutable payload sharing;
- depth-first execution for small proof memory, best-first execution for early
  target closure, or a bounded hybrid frontier;
- store branch-local program suffixes directly, or hash-cons identical
  instantiations above the scope layer;
- retain `Dyadic` in real-domain executable plans while keeping the proof
  schema generic, or replace it with a registry-resolved opaque landmark.

These choices may change performance and certificate size, but not the
coverage-and-two-proofs contract. Acceptance tests for the branch layer must
include a useful two-sided closure, one contradiction leaf plus one target
leaf, a nested split, a child-local instantiation, a sibling-reference attack,
a non-interior repeated split, and fuel exhaustion with no theorem emitted.

The fixed canary also requires a live session with an exact proof history of one
instance, one equality, three fact events, and the expected interleaving before
it reads historical values through `Engine.factAt?`. Those values are quoted
as data, while their proofs come from caller assumptions, top soundness, or an
earlier emitted replay result. A future arbitrary-trace emitter must likewise
obtain evidence from its chronological proof table; a successful full-history
lookup is never evidence that the dependency was available at the required
earlier step.
The quotation walker consumes arbitrary `HistoryEvent` lists, requires
sequential role-local indices, and rejects omitted or duplicated fact or
instance records through final exhaustion. Proof emission then folds the
resulting fact and instance events through its dependent program/evidence
state. Repeated and zero-node instantiations update the checked program,
version, prefix, extension theorem, fact bounds, and fact proofs at the exact
chronology position.

A general direct emitter maintains a table from each already-established fact
version to its `Evidence` term; the real-sine assembler now exercises this
table directly. Caller assumptions seed that table through the generic
`ProofEmitter.assumedAt` lemma and an exact list lookup; generated nodes at
version zero use `ProofEmitter.topFact`, tied to an exact checked node lookup
and the fact-domain schema's top theorem. For a rule or conditional equality,
`ProofEmitter.EntailsList` is constructed in the action's declared input order
and combines the selected terms into `InputsSound`; replay separately checks
that its node list matches the action order, while `InputsSound` itself is a
membership proposition. These helpers contain no operation or function cases:
adding a propagator contributes schemas, not a new dependency assembler.
Merely resolving the same fact values from compiled search history is a
quotation check and cannot substitute for these proof terms.

Each package also contributes an `EmitPackage Handle`: a finite map from its
exact replay addresses to frontend-defined schema handles. The Mathlib tactic
instantiates `Handle` with Lean declaration names, while the Mathlib-free core
does not depend on that representation.
`SchemaTable.build` concatenates those contributions and rejects every
duplicate full address, including duplicates which happen to name the same
declaration. The tactic selects by the payload entry's `(rule, role, schema)`;
it never dispatches on an expression's mathematical function. A declaration
name is elaboration data, not trusted evidence: a missing name, wrong type, or
schema whose own replay key does not match the entry makes emitted application
construction fail. Only the resulting well-typed theorem application enters
the kernel.
`ProofRegistry.Package` now joins each package's semantic schemas and emitter
fragment. Joint assembly first uses the semantic registry check to establish
exact package-for-package ownership and bidirectional coverage against the
executable formats. It then requires package-local equality of semantic and
emitter replay-key sets and global emitter uniqueness. Consequently a handle
cannot be omitted, added under an undeclared key, or borrowed from another
package even if the final flattened key set would happen to match. The live
real-sine semantic replay and direct-emission table are both projections of
this one checked registry. This governance relation is still defense in depth
rather than part of theorem soundness: every selected schema must produce the
required kernel-checked claim.

A Mathlib companion must instantiate those abstract schemas, decode each
frozen entry independently of package cache state, and recheck the
corresponding rule theorem. It remains an explicit compatibility
obligation—not a property enforced by the representation validator—that a
different callback implementation under an existing versioned rule schema
leave every retained payload semantically replayable. Whether production
retains these existential snapshots, compiles a dispatch table, adds typed
decoders, supports hot replacement, or uses another lookup structure remains
experimental. The older direct registry and engine interfaces remain
available for search experiments, but proof-producing execution goes through
the session.

`PolicySession.Session` is the corresponding proof-producing policy canary.
Its checked start stores one bundle containing the engine, policy, and arena
limits and owns the resulting `Policy.State`, exact registry, and arena.
`Session.view` returns the same owned session with traversal accounting
committed, while `Session.choose` accepts only a checked selection or
dismissal and returns the next coherent session. No public transition accepts
separately assembled engine, registry, policy state, or arena values.

The explicit registration and validation boundary is fixed. Discovery and
scheduling above it remain empirical: one arm uses an incremental registry
worklist to share facts and retain state, while a second traverses the same
registered rules in a structural, form-directed loop similar to `apply_rules`.
Neither arm uses recursive typeclass search or bypasses rule validation. The
benchmark compares these discovery styles rather than preselecting one for
every structural goal; a hybrid may use the structural loop as one action.

Rule-private caches can have arbitrary Lean types. The engine stores none of
them. In the current canary, heterogeneous caches are existentially hidden
inside the registry's `Array (Package Fact)`, and the resulting
`Registry Fact : Type 1` is threaded as the single external cache through
either the FIFO or policy driver. Handlers in one package share that package's
cache; handlers in different packages may use unrelated types. Each package
currently has one cache for the whole run. Dynamically scoped contractor
bindings are already installed and validated; what remains open is whether
package cache state is branch-owned or explicitly keyed by
`ScopeId`/semantic cache keys once proof branching is implemented.

Cache contents are a performance optimization, not a hidden mathematical
dependency. For the same request and logical budget, a memoization hit and
miss must produce the same observable outcome. If package state can change
applicability or a candidate fact, that state needs an explicit versioned
dependency and wakeup rule; silently sharing it between handlers would make
fixed points depend on schedule.

Binding still expands relative ports into concrete applications, and every
registry request exposes exactly the declared read facts and write targets. It
provides no unrestricted fact getter: a hidden fact read would be absent from
the dependency index and could miss a required wakeup.

A registration whose matcher depends on the whole `ProgramView` uses the
`global` binding, the `network` structural watch, and `watchesProgram`. Every
append-only extension then stales its old action and requeues that
registration's single global application. This coarse trigger is the first
grind-like instantiation mechanism: a matcher that was previously inapplicable
can observe expressions introduced by another package without compiling one
whole-network scan per matching expression. Ordinary anchor-local and scoped
registrations remain append-stable; they do not acquire a global dependency
merely because engine-owned admission may CSE one of their outputs. Compiled
structural patterns or more selective operation-key triggers remain
alternatives to compare against the same reference stream.

1. The solver produces an `Action` naming a program snapshot, concrete rule
   application, anchor, declared input fact versions, exact write authority,
   effort, and action kind. Fact history retains that write list, so semantic
   replay rejects a proposed fact outside the frozen action authority without
   consulting mutable final state. In the current quoted-data canary this is an
   internal-consistency and defense-in-depth check: authenticating that list
   against the compiled application/registration tables requires either quoting
   and reconstructing those tables or re-running application compilation. That
   production choice remains open; package theorem replay is the soundness
   boundary in either design.
2. The external function-package registry executes the routed callback and
   owns its private cache; the Mathlib companion is responsible for semantic
   replay, not hot-loop dispatch.
3. The registry returns a `Plan` containing an `Outcome` plus exactly the
   reply-local recipe drafts referenced by its fact, instantiation, and
   equality payload identifiers.
4. A reply echoes the request serial, snapshot, and application. A delayed or
   transplanted reply is rejected without clearing the current request.
5. The solver validates every candidate target against the application's
   declared writes and computes all intersections against the pre-outcome
   state. It then commits the whole improving batch and wakes the deduplicated
   union of affected applications once. A malformed later candidate or a
   one-step-short fact or queue budget commits none of the batch. Interval
   intersection enforces representation consistency and monotone narrowing;
   it does not establish the semantic soundness of an untrusted candidate.
   Only companion replay of the retained payload can do that.
6. In the production replay protocol, every value needed to justify an
   accepted fact is frozen into an immutable per-run payload arena, and the
   retained `PayloadId` points there rather than into a mutable cache. Session
   execution validates and relocates the complete reply prospectively before
   engine admission.
7. The solver records the snapshot, concrete application, anchor, action kind,
   effort, input versions, target's preceding fact version, proposed fact,
   installed fact, and frozen payload in provenance. The preceding target fact
   is an explicit dependency of intersection even when the rule did not
   declare that target as an input. The engine also retains the immutable base
   program and caller-supplied version-zero fact array rather than attempting
   to recover either from the extended program or narrowed current slots.

The executable `Engine.factAt?` is the replay lookup invariant. Version zero
of a base-program node resolves from the caller's immutable `initialFacts`;
version zero of an appended node resolves to `FactDomain.top` at that node's
domain; every positive version resolves only through the exact `(node,
version)` event in `history`. It never substitutes the mutable current fact
slot. For every valid engine state, each event's `previous`, every
action-input version used by a rule event, and every equality-transport source
must resolve this way; the event's own identifier resolves to its installed
fact. The current `(node, versions[node])` lookup likewise agrees with
`facts[node]`. The initial-fact array has exactly the base-program node count,
and every later program retains the complete base program as an unchanged
prefix. These properties become checker invariants when engine fields are
made opaque.

`Engine.factAt?` is an observation over an already-valid engine, not the
checker for an untrusted trace: it searches the complete retained history.
Certificate replay must instead fold events in chronological order and
resolve every positive-version dependency only from the already-validated
prefix. This rejects future references and cyclic provenance even if a forged
final history contains an entry with the requested `(node, version)`.
The checked rule, equality-transport, and instance transitions above are the
semantic bodies of that fold. The private prefix resolver supplies their exact
historical inputs and lifts them across checked program extensions.
`TraceReplay` now consumes the authoritative cross-history order, validates
equality availability, and requires exact fact, instance, equality, program,
and version exhaustion. The tactic frontend now extracts and reifies the
accepted plain data for the complete sine trace, selects package schemas, and
emits the direct replay applications through final closure. Generalization now
concerns arbitrary trace length, program reconstruction, and construction of
the complete version-to-evidence table rather than the soundness of an
individual emitted transition. A transparent generic fold remains an
alternative architecture to measure, but is not required by direct emission.

Because `Semantics.holds` may inspect the complete program as well as the
valuation, conservative model extension alone cannot transport old facts or
the caller's target across a program extension. The checked `StableStep`
boundary therefore requires both model restriction and fact stability on old
nodes. A production semantics adapter may derive this once from a global
prefix-locality theorem; keeping it as evidence for the exact step leaves that
choice open during experimentation. Conditional equality assumptions resolve
from the same already-checked fact prefix at the owning instance's position in
the authoritative chronology. They may not consult the final fact table or a
later event. These are proof obligations, not policy choices.

Whether freezing is an explicit second request after the solver identifies
the improving subset, or eager allocation before the `Outcome`, remains an
experiment. Eager freezing has a simpler protocol but may retain payloads for
weaker candidates; two-phase freezing adds a failure transition which must
remain atomic. In an eager design, a successfully submitted reply can leave
an unused entry when a candidate does not improve the current intersection,
when a suggestion is dropped or later dismissed, stale, invalid, or
structurally duplicate, or when an instantiation's proposed equality reuses an
older edge whose payload remains authoritative. These are permitted arena
waste, not proof dependencies. They must be measured and bounded; compacting
only the backwards proof slice, freezing only the improving/admitted subset,
and accepting this monotone waste are all still viable designs.
The first protocol also freezes a fresh entry whenever a later reply uses the
same recipe again: reply-local exact coverage does not yet provide an explicit
way to cite an older global entry. Interning immutable entries, adding a
checked global-reference draft, and accepting bounded cross-reply duplication
are alternatives to measure rather than assumptions of the final format.

The first executable arena uses an eager but prospective transaction:
it preflights total-proposal work and the per-reply draft, draft-cell, atom,
and schema limits, then matches package-local labels exactly against
package-local drafts and checks duplicate, missing, extra, and wrong-role
entries. The package-owned path next checks body representation with the
immutable replay snapshot selected by the exact invocation. Only a locally
bounded, exactly covered, format-valid reply is compared with remaining
whole-arena entry and body-cell capacity, relocated to fresh global
identifiers, and appended to a new arena value. Thus malformed local evidence
cannot be classified as cumulative exhaustion merely because earlier valid
replies filled part of the arena. Local preflight returns an opaque
bounded-draft transaction whose constructor is private; it carries the exact
draft list together with its derived cell count, and both cumulative preflight
and append consume that same value. No public caller can supply a separate
cell count for unrelated drafts. The total-proposal budget charges every
candidate, every suggestion constructor (including retry and split), and
every equality nested under an instantiation. Repeated references count as
work even when they share one draft. Before any quadratic label/coverage scan,
`maxDrafts` bounds the draft list independently of proposal traversal. Every
atom reached by the bounded body traversal is range-checked before its cell is
charged. The traversal stops at the first in-range cell beyond
`maxDraftCells`; later atoms are deliberately not inspected. Entry
construction and identifier assignment are one traversal, so a relocated
identifier denotes exactly the entry appended for its local draft.
Candidate, instantiation, and equality roles are distinct, and ordinary replay
lookup checks the expected role. Reconstructing an instantiation during this
traversal preserves its complete node, equality, and arbitrary-scope proposal;
default-valued fields are not permission to discard nonempty structure.
Each entry also retains the complete engine-issued action, including the exact
matcher structural-input batch and epoch which caused the reply. The
engine-private matcher cursor is deliberately absent from `Action`, is neither
stored nor reconstructed by payload freezing, and remains scheduler state
only. This verbatim action copy is sound only while `Action` contains no
package-produced reply-local payload labels; any future payload-bearing action
field must join the checked relocation traversal rather than being copied as
though it were already a frozen arena identifier. Failure returns the old
arena.

Both private FIFO and policy sessions commit that returned arena only if
submission of the relocated outcome also succeeds. For a structural matcher,
this makes proof payloads and engine-owned cursor progress one transaction: an
accepted reply
commits both, while semantic rejection, engine or fact-domain resource
refusal, and cumulative arena exhaustion commit neither. Before freezing, the
sessions check the candidate and suggestion list lengths against the engine's
own trusted limits. Let
`requiredUses = maxOutcomeCandidates + maxOutcomeSuggestions *
(maxProposalItems + 1)`: every candidate and suggestion costs one payload use,
and every suggestion may be an instantiation with at most
`maxProposalItems` nested equalities. Session start requires
`requiredUses ≤ maxDrafts`, `maxDrafts ≤ maxUses`,
`maxDrafts ≤ maxEntries`, and `maxDraftCells ≤ maxBodyCells`. The first
inequality permits one distinct draft for every engine-valid payload use.
The second both implies that the use traversal can inspect every such position
and bounds even malformed pre-coverage draft lists by the same envelope.
The remaining inequalities ensure that any reply inside the local draft/cell
envelope fits a fresh arena. `maxEntries` and `maxBodyCells` remain cumulative
whole-run bounds: only capacity spent by an earlier committed reply can make a
later locally valid reply exhaust them.
Packages see the complete engine and arena envelopes and may impose stronger
method-specific requirements.
Before any package-specific program check traverses nodes, session start runs
the generic engine preflight and compilation, so the engine's operation, node,
rule, arity, application, and queue bounds already hold.

The eager protocol's `maxEntries` and `maxBodyCells` are separate whole-run
waste bounds. They must cover drafts frozen for every invoked action up to the
action limit, including entries later unused because a candidate was not
improving or a suggestion was dropped, dismissed, stale, invalid, or
duplicate. Sizing either from `maxAcceptedFacts` is therefore unsound. A coarse
safe envelope multiplies the corresponding per-reply cap by the action limit;
tighter package-declared envelopes and two-phase freezing remain experiments
to compare.

Engine rejection, fact-domain or engine resource refusal, and exhaustion of
the remaining whole-run arena entry or body-cell capacity retain the preceding
arena, facts, program, and proof history and make the returned session
non-live. Start-time coherence means these arena stops occur only after an
earlier commit has consumed capacity. A caller cannot resume that snapshot and
later relabel the partial run saturated. Treating cumulative arena exhaustion
as fatal is an intentional conservative liveness policy, aligned with global
engine-resource exhaustion: the selected reply is otherwise valid, but its
required proof data cannot be retained. Proof soundness could also permit a
recoverable session which permanently records dropped work and remains
incomplete, but that would broaden scheduling behavior; the eager prototype
does not do so. The fatal policy-session path clears the pending latch without
submitting a synthetic rule outcome, so a prepared matcher cursor and its visit
charge remain at the last committed batch. The already selected policy
decision and non-semantic package invocation telemetry remain charged.
Malformed package evidence and
package-local payload-use, draft-count, draft-cell, atom, or schema excess are
different: the prospective arena is discarded, but the session submits a
bounded synthetic `failed` outcome through the ordinary engine reply path.
This clears the request latch, retains non-semantic cache telemetry, leaves
facts and history unchanged, keeps the session live, and records that required
work was dropped. For a matcher, that synthetic failed reply deliberately
consumes the issued structural batch without retaining its malformed payload;
otherwise repeatedly presenting the same broken reply could prevent all other
work from running. The FIFO driver may therefore continue other independent
rules, including later successful arena and fact commits, but the monotone
`droppedWork` flag survives and the run must eventually report incomplete.
The selected package's cache may record either kind of attempt because caches
and invocation telemetry are explicitly non-semantic.
This executable eager protocol does not foreclose measuring a two-phase
production protocol.

An invalid rule outcome may mislead search, but it cannot produce a theorem.
The companion reconstructs every retained fact from the rule's soundness
theorem. A failed reconstruction identifies a broken registration rather than
closing the user's goal.

Cost observations used by a deterministic policy are specified logical counts
such as declared arithmetic work, visited certificate entries, generated
nodes, or estimated proof nodes. Actual runtime reductions, allocations, and
wall time are telemetry only: compiler and backend changes can alter them, so
they cannot influence a reproducible action choice.

A `resourceLimit` diagnostic reports work refused and is not itself a claim
that this work was performed. The executable protocol therefore checks
successful and fixed-point `CostObservation` fields against
`maxObservationValue`, while `resourceLimit` and `failed` identifiers use the
separate `maxDiagnosticValue`. Negative outcomes contribute no logical cost.
Fact-domain malformed and resource identifiers cross the same diagnostic cap
before they can enter reply or equality events.
The dyadic canary maps its typed preflight failures to small fixed category
codes rather than copying an arbitrary work magnitude into policy history.
Whether negative outcomes should also carry a bounded logical cost remains
open: omitting that cost simplifies the protocol, while including it lets
policy learning account for unsuccessful probes. Until measured, a registry
must label its successful cost model as a versioned declared estimate rather
than present placeholder weights as exact operation counts.

The standalone arena experiment gives fact, instantiation, and equality
`PayloadId`s checked array-index meaning and bounds entry count, opaque
recipe-body cells, schemas, atoms, draft count, and total proposal work before
allocation. Reply-local draft and cell caps are distinguished from cumulative
entry and cell capacity.
Each frozen entry stores its originating action, semantic role, numeric
payload schema, and uninterpreted `List Nat` body. It derives the rule owner
only from `origin.key`, avoiding two stored identities which could disagree.
The session now performs package-owned format lookup and bounded body-shape
validation under the full `(RuleKey, role, schema)` key. Typed decoding, typed
atom encodings, byte limits, and semantic replay are still missing.
The first real dyadic packages declare payload schema `0` separately for each
fact, instance, or equality handler. Each body validator accepts exactly the
empty list and rejects every trailing cell; the rule key still distinguishes
the theorem epoch and owner.
Instantiation family labels and custom split-reason numbers also remain
untyped representation gaps. The FIFO session turns any positive
compatibility callback whose local identifier lacks a draft, or whose draft
fails format validation, into a failed rule transition, so no unvalidated
package-local identifier reaches its retained provenance. Its monotone
`droppedWork` flag means exactly that required work was lost; it is not itself
a terminal-state claim. The exported `Session.complete` predicate additionally
requires a live session and no retained retry or instantiation. At a FIFO
fixed point this predicate is the sole gate between saturated and incomplete.
Package `failed`/`resourceLimit` results, malformed evidence, dropped narrowing
suggestions, and unprocessed retained narrowing therefore cannot be laundered
into saturation.

The policy session now preserves the same transaction while allowing an
external policy to select invocations and retries, instantiations, equality
contractors, and splits, or to dismiss any live offer. A selected invocation
or retry routes through `Registry.invokePlanned`, which returns the plan paired
with the exact selected handler's replay snapshot. The session calls that
sealed snapshot's paired freeze operation, submits the relocated reply through
`Policy.State`, and commits the new arena only for an accepted reply. A missing
or malformed format and package-local payload-use, draft-count, draft-cell,
atom, or schema excess consume a bounded synthetic failed reply: the cache may
record the attempt, the arena, facts, and history do not commit, and the
private session remains live but permanently incomplete. Exhausting remaining
whole-run entry or body-cell capacity after an earlier commit instead returns
a non-live session after clearing the selected request while preserving the
preceding arena and history.
The policy can observe a bounded view and echo a semantic selection, but
cannot extract and later recombine the engine, registry, arena, or policy
bookkeeping. Its `Session.complete` predicate additionally scans for live
invocation and equality work and treats retries and instantiations, but not
optional splits, as closure obligations. The policy state's monotone
incompleteness bit covers failed replies, rejected or stale narrowing
suggestions, and required dismissals; the session bit covers evidence lost
outside those policy transitions. Engine-resource or structurally invalid
snapshots also become non-live.

The representation-free policy-session canary is an architectural gate, not a
dyadic or rational example. It uses an opaque `Nat` fact domain and imports no
interval representation or rational arithmetic. An opaque sine package
recognizes `sin (-x)` from an engine-issued structural batch, introduces
`sin x` and `-(sin x)`, proposes their equality, and installs a dynamically
scoped sine contractor. Policy then selects both the theorem instance and that
new contractor; the contractor improves an otherwise opaque fact while the
session freezes the instance, equality, and fact recipes under their
respective handlers. A companion proposal changes the contractor's semantic
watch while remaining generically well-formed; package veto must roll back its
prospective arena, retained proposal, and matcher cursor together. This canary
is also passed through the generic semantic registry: package-local schemas
prove conservative addition of the two expressions, equality of the retained
endpoints, and the contractor's proposed fact from the actual session history
and arena. The compact canary gives the sine-shaped operation a private integer
model solely to test that generic route; it is not a theorem about `Real.sin`
and by itself does not close the non-polynomial completion gate.

The first non-polynomial vertical keeps this graph shape but replaces the
integer model with actual `Real.sin` semantics and a tiny fact lattice
containing whole, `[0,1]`, nonnegative, and nonpositive ranges. From caller
facts `x ∈ [0,1]`, a scoped sine propagator proves `sin x ≥ 0`; an independently
registered negation propagator proves `-(sin x) ≤ 0`; and the retained
`Real.sin_neg` equality transports that fact to the original base expression
`sin (-x)`. Successful replay must yield the ordinary theorem
`0 ≤ x → x ≤ 1 → Real.sin (-x) ≤ 0`. This exercises a real transcendental,
multiple arbitrary packages, instantiation, a one-sided unbounded interval,
equality transport, and final target closure before any Taylor or rational
endpoint backend is optimized.

That vertical is now executable. The live policy session performs matcher,
instantiation, sine propagation, independent negation propagation, and
equality transport in that order; complete chronological replay reaches the
original `sin (-x)` target. The tactic quotes the actual instance, two fact
events, equality edge, and payload entries as plain data, selects schemas from
the contributing packages, and constructs the transparent replay and generic
closure term. It yields the ordinary theorem above without `native_decide` or
rational normalization. This is the acceptance shape for further arbitrary
functions: executable search and quotation may fail, but only kernel-checked
package lemmas and generic composition enter the proof.

### Action kinds

The protocol distinguishes the following actions.

- `forward`: compute an enclosure of a node from current argument intervals.
- `backward`: use the node's current interval and all but one argument to
  contract an argument interval.
- `improve`: rerun a rule at greater effort, use a tighter enclosure method, or
  subdivide only the rule's input range and take the hull of the pieces.
- `shave`: temporarily slice one input, run a bounded contractor on each slice,
  discard slices proved inconsistent, and return the hull of survivors with a
  local branch certificate.
- `instantiate`: propose validated new expression nodes and their proof
  recipes from a matched shape.
- `rewrite`: activate a proved alternate expression and equality edge already
  present in the current validated program snapshot.
- `regularize`: create bounded-height working views without deleting stronger
  facts.
- `split`: create proof branches by adding complementary cuts for one node.

`improve` and `split` are intentionally distinct. Local subdivision inside one
propagator can tighten the range of a function without duplicating the whole
proof state. A solver split is needed when a dependency between several nodes
requires different assumptions in different cases.

`shave` is also distinct from a solver split. It is the proof-producing analogue
of RealPaver's 3B/CID strong-consistency step: its temporary cases live inside
one rule payload, and replay proves that every removed edge slice is
inconsistent before hulling the survivors. A policy may compare cheap HC4-style
forward/backward contraction, BC-style searches for repeated occurrences,
targeted shaving, interval Newton, and a global split. Which strength to apply
is empirical and may depend on occurrence counts, derivative influence,
observed contraction, and proof cost.

Whether `ActionKind` is only a policy/provenance label or also constrains the
constructors a callback may return remains open. The current experiment allows,
for example, an instantiation suggestion from any successfully routed handler;
a binding design would instead reject a mismatch at reply admission. This must
be settled together with multi-purpose handlers rather than inferred from the
first registration names.

An `Outcome` may be `noChange`, `inapplicable`, `resourceLimit`, or `failed`
without affecting soundness. `resourceLimit` names the exhausted budget and is
not cached as mathematical inapplicability; a `failed` code is an opaque
diagnostic identifier rather than a cost magnitude. Rules do not promise that
greater effort always gives a tighter answer. The solver intersects every
result with existing facts, measures the actual improvement, and learns from
that observation. Retained suggestions are advisory: the engine computes one
bounded kept/drop-reason classification and still commits independently valid
candidate facts. Metrics record the total omitted suggestions and separate
capacity and structural-depth counts; the two category counts sum to the
total. Capacity overflow drops the remaining suffix; an individually
depth-limited instantiation is filtered without consuming capacity, allowing
later affordable advice to survive. The exact plan accompanies the accepted
reply into the policy observation. Dropping a retry or instantiation marks
propagation incomplete, while dropping only split advice preserves
fixed-point completeness.

The base `Program` is static after validation. Generic cheap alternates may be
present before search, and `rewrite` only changes which form in the current
validated snapshot is scheduled. Adaptive range reduction or a Taylor
polynomial may instead remain inside a rule-specific payload and return a fact
about an existing node. Dynamic instantiation is never unchecked mutation: it
uses the validation, dependency-update, scope, generation, and replay contract
above.

### Stateful rules

A cache is either owned by one branch or explicitly keyed by `ScopeId`. Its
key also includes the immutable program-snapshot identifier (or equivalent
canonical expression key), versioned rule, node, exact input `FactId`s and
slot versions, and effort. A node number and scope-local version counters are
not a global key: siblings may reuse those numbers for different cuts or
extensions. Cross-branch reuse is permitted only when all semantic inputs and
the validated snapshot key agree. A rule may retain:

- Taylor coefficients and remainder data;
- values at subdivision points;
- argument-reduction integers;
- automatic-differentiation intervals;
- a previous local partition that can be refined;
- proof payload fragments that remain valid after an input interval shrinks.

Shrinking an input does not require a rule to discard all earlier work. Cache
reuse is a performance feature only. Every returned fact still receives a new
or reused sound justification.

### Lessons from RealPaver

RealPaver is the closest concrete reference architecture for the intended
combination of arbitrary nonlinear contractors, adaptive consistency, and
branching. Both the classic 0.4 manual and the current 1.1 C++ implementation
are relevant. The current system separates a generic `Contractor` interface,
contractor composition, dependency-driven propagation, strong-consistency
contractors, variable selection, and search-space order. This validates the
SPEC's separation between package rules, engine transitions, policy, and the
branch layer, but its proof boundary must be strengthened substantially for
Lean.

The current RealPaver propagation loop initially queues every contractor. After
one contractor mutates its box, it examines only variables in that contractor's
scope; a sufficiently large relative width reduction wakes inactive dependent
contractors. HC4 builds one `HC4Revise` contractor per constraint over a shared
expression DAG. BC4 similarly combines an HC4 pass with variable-occurrence
search. The solver can compose a base HC4, BC4, or affine propagator with ACID,
polytope relaxation, and interval Newton. This is directly translatable as:

- one checked application per package contractor and an explicit watch/write
  scope;
- a dependency worklist rather than whole-network rescans;
- optional stronger actions represented as additional offers, not hard-coded
  phases in the engine;
- policy features for relative reduction, repeated occurrences, derivative
  influence, and recent contractor productivity.

RealPaver's propagation tolerance is not a theorem. It may treat a small width
reduction as unchanged and therefore decline to wake dependents. HexInterval
may use the same heuristic only in policy and completion accounting: every
accepted fact is intersected exactly, while suppressing a logically possible
wake either belongs to an explicitly approximate profile or marks the branch
incomplete. The tolerance can never justify `noChange`, contradiction, or
target subsumption in emitted proof.

ACID is especially useful for the upgradeable policy design. It ranks variables
by a derivative-based smear score, alternates learning and exploitation phases,
measures contraction gains, and learns how many variable-level 3BCID
contractors are worth applying. The transferable idea is not its particular
average-gain formula. A policy-private state may learn an effort frontier from
bounded observations and choose fewer expensive offers on later boxes. The
engine must still own action identities, exact inputs, budgets, and proof
payloads. Learned scores are untrusted scheduling data, and mutable ACID state
must be branch-owned or keyed by the complete semantic snapshot before it is
reused across siblings.

RealPaver's variable 3BCID implementation first slices one variable, removes
inconsistent outer slices using a nested contractor, and then applies CID to
the remaining middle slices, returning the hull of surviving reductions. This
maps to the `shave` action rather than a global solver split. Its Lean replay
payload must enumerate a finite covering partition, give a checked
contradiction for every discarded slice, give the retained contraction for
every surviving slice, and prove the returned hull covers all survivors. A
coarse `Empty` status from a nested run is insufficient. The number of slices,
nested propagation work, and retained proofs are all charged to the one action.

RealPaver keeps solver branching separate. Its variable selectors include
round-robin, largest/smallest domain, mixed discrete/continuous selection,
derivative-smear selection, and hybrids. Its pending-node containers include
DFS, BFS, distant-most DFS, and hybrids which search depth-first until a
solution and then resume from a best pending node by depth or perimeter. These
are useful initial policies to reproduce behind `Controller`; none belongs in
the proof-producing core. For proof goals, additional useful scores are
distance to a closing fact, predicted proof size, and whether both children are
likely to close rather than average contraction alone.

The principal non-transferable part is RealPaver's `Proof` enum. Its
`Empty`, `Maybe`, `Feasible`, and `Inner` values are operational certificates
returned by C++ methods, not kernel proof terms with replayable provenance. In
HexInterval each successful analogue needs a package theorem or checked
certificate tied to the exact box, constraint, and program snapshot.
`Maybe` maps naturally to an unproved search result. `Empty` needs the
refutation schema described in the split section. Feasible/existence results
from interval Newton need separate existence and uniqueness theorem schemas;
they must not be conflated with universal interval bounds.

The RealPaver examples give small, discriminating acceptance cases:

- `y = x^2` and `y = 2 - x^2` on `[0,2]^2`, where independent local
  contraction stalls but facet shaving isolates the intersection near `(1,1)`;
- `x*x + y^2 = 2` on `x ∈ [-2,4]`, `y ∈ [-1,1]`, where repeated occurrence
  defeats simple hull propagation and motivates box search;
- `x₁*x₂*x₃ = 1`, `x₁+x₂+x₃ = 0`, and
  `max (x₁+x₂) (x₂-x₃) ≤ 0` on `[-10,10]^3`, which distinguishes one-pass
  weak 3B, iterated 3B, and a large paving;
- the square-system examples where interval Newton dramatically strengthens
  local propagation, including certification of isolated roots.

These should be translated into exact rational/dyadic starting boxes and
package-owned operations. Tests compare accepted facts, branch trees, and
proof size across policies; they do not freeze RealPaver's floating-point
endpoints or take its output as an oracle.

## Propagation state

Each live branch contains:

- the strongest and selected cheap lower and upper facts for every node;
- monotonically increasing fact versions;
- a dependency worklist;
- rule effort, cache keys, and the result of the last invocation;
- policy observations and action ages;
- the branch assumptions introduced by splits;
- step, endpoint-height, trace-size, depth, and leaf counters.

A stronger fact enqueues only consumers and reverse rules that depend on the
changed side. The default implementation does not run repeated whole-program
passes. A pass remains a useful diagnostic grouping, but the algorithm is an
incremental worklist.

The reference propagation queue coalesces a concrete application while it is
already dirty. Several changed inputs therefore produce one registry call on
the newest declared-input snapshot, while telemetry counts suppressed wakeups.
A versioned priority policy may instead retain stale candidates and discard
them lazily at pop time. Both implement the same request/reply contract; the
benchmark compares rule calls, dependency visits, insertions, pops, stale or
suppressed work, and peak live queue before selecting a default. Multi-output
outcomes install every accepted fact before waking this union, so they do not
manufacture stale work against their own half-installed state.

The initial `balancedV1` candidate runs all cheap forward rules once in program
order and then drains the dependency worklist. It also runs zero-cost
contradiction checks after every accepted fact. More expensive improvement and
split actions start only after this cheap fixed point, unless a rule marks a
singularity that requires an immediate split. This staging is policy behavior,
not an engine soundness condition.

Backward propagation uses the same worklist. A contractor is valid only when
its soundness theorem says that it preserves every assignment satisfying the
current constraints. When proving a goal by contradiction, the frontend may
seed the negation of the goal and contract the possible counterexamples. It
must never assume the desired conclusion itself.

The negated goal lives in an explicit counterexample scope below the original
context. Facts derived there are conditional on that assumption. If the scope
does not close by contradiction, its intervals are reported only as
counterexample-box diagnostics. A public best-bound theorem is replayed from
pre-assumption facts or from a separate bound search, never by leaking a
conditional fact into the parent scope.

## Search policy

The policy affects success and performance, never validity. In particular it
does not construct an `Action`: action serials, program snapshots, concrete
applications, and input versions are engine-owned authority. The engine owns a
bounded frontier of offers and the policy returns only the stable identity and
canonical key of one offer it observed. In the sketch below,
`InstantiationSemanticKey` is the payload-erased canonical family,
engine-computed generation, proposed-operation/reference graph, and unordered
equality-pair key. Replay-facing trigger metadata is deliberately absent;
`PolicyFeature` is a bounded exact integer key/value; and frontier events are
engine-issued additions, refreshes, tombstones, and observations:

```lean
structure PolicyKey where
  name    : String
  version : Nat

structure OfferId where
  index : Nat

structure InvocationKey where
  scope          : ScopeId
  programVersion : Nat
  application    : ApplicationId
  rule           : RuleKey
  anchor         : NodeId
  kind           : ActionKind
  effort         : Nat
  inputs         : List SeenVersion

structure EqualityWorkKey where
  scope          : ScopeId
  programVersion : Nat
  equality       : EqualityId
  left right     : SeenVersion

inductive OfferClass
  | invoke
  | equality
  | retry
  | instantiate
  | split

inductive OfferKey
  | invoke (invocation : InvocationKey)
  | equality (contractor : EqualityWorkKey)
  | retry (source : InvocationKey) (effort : Nat)
  | instantiate (source : InvocationKey) (request : InstantiationSemanticKey)
  | split (source : InvocationKey) (node : NodeId) (point : Dyadic)
      (reason : SplitReason)

structure PolicyFeature where
  key   : Nat
  value : Int

structure ObservationSummary where
  outcome      : Nat
  changedFacts : Nat
  logicalWork  : Nat

structure PolicyBudget where
  decisions : Nat
  traversal : Nat
  noteBytes : Nat

structure EngineBudgetView where
  actions       : Nat
  acceptedFacts : Nat
  nodes         : Nat
  equalities    : Nat
  branches      : Nat

structure FactDelta (Fact : Type) where
  node          : NodeId
  before after  : Fact
  beforeVersion : Nat
  afterVersion  : Nat

inductive OutcomeTag
  | success
  | noChange
  | inapplicable
  | resourceLimit (budget : Nat)
  | failed (code : Nat)

structure RuleObservation (Fact : Type) where
  invocation    : InvocationKey
  outcome       : OutcomeTag
  changes       : Array (FactDelta Fact)
  contradiction : Bool
  cost          : CostObservation
  suggestionPlan      : SuggestionPlan
  emittedSuggestions : Array OfferId

inductive EqualityOutcome
  | noChange
  | improved
  | contradiction
  | engineResource (resource : Resource)
  | factResource (budget : Nat)
  | invalid (code : Nat)

structure EqualityObservation (Fact : Type) where
  key         : EqualityWorkKey
  outcome     : EqualityOutcome
  changes     : Array (FactDelta Fact)
  narrowCalls : Nat

structure OfferView where
  id       : OfferId
  key      : OfferKey
  class    : OfferClass
  age      : Nat
  summary  : Option ObservationSummary
  features : Array PolicyFeature

structure PolicyView (Fact : Type) where
  scope          : ScopeId
  serial         : Nat
  programVersion : Nat
  offers         : Array OfferView
  facts          : Snapshot Fact
  goalFeatures   : Array PolicyFeature
  remaining      : EngineBudgetView

structure Selection where
  scope          : ScopeId
  serial         : Nat
  programVersion : Nat
  id             : OfferId
  expected       : OfferKey

inductive PolicyEvent (Fact : Type)
  | frontier (added : Array OfferView) (removed : Array OfferId)
  | rule (observation : RuleObservation Fact)
  | equality (observation : EqualityObservation Fact)
  | instanceAdmitted (programVersion : Nat) (added : Array OfferView)
  | splitPrepared (scope : ScopeId) (node : NodeId) (point : Dyadic)
  | choiceRejected (choice : Selection) (reason : Nat)
  | engineResource (resource : Resource)

structure DecisionNote where
  stage  : Nat
  reason : Nat
  score  : Nat

inductive PolicyStep (State : Type)
  | select  (choice : Selection) (note : DecisionNote) (next : State)
  | dismiss (choice : Selection) (note : DecisionNote) (next : State)
  | stop    (reason : Nat) (next : State)

structure Policy (Fact : Type) where
  key    : PolicyKey
  State  : Type
  init   : PolicyView Fact → State
  update : State → PolicyView Fact → PolicyEvent Fact → State
  choose : PolicyBudget → State → PolicyStep State
```

The policy state, like rule-private caches, may have an arbitrary Lean type and
is owned by the external driver. `Policy.State.select` rechecks the decision
serial, scope, program version, offer identifier, complete canonical key,
eligibility, and budgets. It alone freezes current input versions and creates
a registry `Action`, runs an engine equality contractor, admits a selected
instance, or emits an endpoint-resource-checked `SplitPlan`. The current driver
stops and returns that plan; it does not create branches or establish that the
point is interior. A future scope/branch layer must validate domain-specific
interiority and construct complementary child assumptions. A stale,
fabricated, or transplanted selection changes no facts, program, frontier
membership, or pending action; it may consume one bounded decision step and
append an audit disposition.

Dirty concrete applications create or refresh invocation offers. Any
structurally accepted bounded rule report may create engine-indexed retry,
instantiation, and split offers; the policy cannot supply their structural
payloads. Removing an offer emits a tombstone event, so stable identifiers do
not require an ever-growing live frontier. Program extension invalidates
exact-snapshot instantiation offers, refreshes dirty invocation offers, rechecks
retry and split offers under their variant-specific guards, and inserts offers
for new applications and equality jobs atomically with the extension.
A selected retry prepares a fresh action carrying the bounded effort override;
it does not mutate the compiled application's registration baseline, so later
append-only program validation still compares an immutable application prefix.
When its source was a structural matcher, the retry replays the source batch
and epoch but carries the current engine-owned cursor unchanged. Admission
therefore authenticates the epoch while charging only new cursor movement,
which is normally zero for a replay.

Each completed rule selection produces an engine-owned observation containing
the outcome class, actual admitted fact deltas, contradiction status, emitted
offer identifiers, and the bounded declared `CostObservation` for successful
or fixed-point reports. Rule-declared refusal and failure identifiers remain
separately bounded diagnostics, while engine-owned `Resource` stops and
fact-domain resource identifiers use distinct typed events. The current
experiment retains exact `FactDelta Fact` values in its event array and has no
observation-byte budget; that is useful conformance evidence, not a settled
production storage choice. A later experiment must compare ephemeral exact
deltas with retained bounded features and explicitly charge any exact values
kept for policy history. Width reduction and other domain-specific benefits
are not inferred by the generic scheduler.

The concrete `RuleObservation` shown above records actual admitted deltas
rather than a rule's claimed gain. Other `PolicyEvent` constructors distinguish
structural admission, equality contraction, split preparation, rejected
choices, and engine resource exhaustion from a rule-declared outcome. Equality
has its own typed observation because it is selectable engine work, not a fake
registry invocation. A fixed-point equality run with no delta is still an
observation; the generic fact interface supplies no idempotence law that would
justify silently omitting it.

`PolicyEvent` is the single ordered transition stream. It wraps rule
observations, instance admission, split preparation, offer additions and
tombstones, rejected choices, and engine resource stops. `OfferView.summary`
is merely the current bounded aggregate derived from earlier events, not a
second observation channel. Successful and fixed-point cost components are
checked against `maxObservationValue`; candidate, suggestion, and proposal
counts have separate structural caps, and negative identifiers have their own
diagnostic cap. The current event protocol has no general encoded-byte cap.

It may be cleaner to normalize the registry result as one bounded `RuleReport`
containing an outcome tag, candidate list, suggestion list, and cost. That
allows `noChange` to recommend a stronger effort or landmark split without
encoding itself as `success` with no candidates. This is an open protocol
experiment; negative mathematical information is never inferred from a
resource limit or failed rule. An accepted `resourceLimit` or `failed` report
clears the request/reply latch and remains an exact policy observation, but it
also marks propagation incomplete: consuming that application did not
establish either successful contraction or mathematical inapplicability.
Reply rejection, engine-resource exhaustion, or fact-domain-resource
exhaustion has the same status when it clears the pending latch. A mismatched
reply which preserves that exact pending action remains resubmittable and does
not by itself lose completeness.

One `balancedV1` candidate uses a versioned priority queue over these offers.
Changed facts insert or invalidate only affected offers; stale entries are
discarded lazily when popped. Policies intended for diagnostics may use a
simpler complete scan, but their complexity is reported honestly. An empty
frontier means saturation only when no narrowing-capable work was dismissed,
dropped by the engine's bounded retention plan, or tombstoned by a failed
freshness guard. `Suggestion.affectsClosure` is the single classification used
for all three paths, while `Engine.suggestionPlan` and its
`SuggestionPlan.kept` and `SuggestionPlan.dropped` results define the exact
shared retention boundary.
Declining an invocation, equality contractor, retry, or instantiation makes
the run incomplete; declining a split does not, because it changes proof
search rather than the propagation closure of the current scope. An empty
frontier after an incomplete dismissal is reported as `unknown`. A
`PolicyStep.stop` for a nonempty frontier is likewise reported as `unknown`,
not saturation. The dismissal event records these as two separate facts:
whether the driver halts immediately, and whether the dismissed offer makes
fixed-point completeness unavailable.

The shown first interface supplies the authoritative bounded scan frontier in
each `PolicyView`; transition events let the policy update historical state
without reconstructing it. Its traversal budget is cumulative across views,
not merely a per-view size check, and counts inactive backing slots honestly.
The decision budget does not suppress a read-only view: after the last allowed
decision the driver may still use its separately charged traversal budget to
distinguish a genuinely empty frontier from live work that must be reported as
`unknown`.
`maxLiveOffers` is initially a policy-view/output budget: making it an atomic
frontier-mutation budget would require preflighting replies and instantiations
before their already-atomic commits. An event-only priority implementation may
later remove the repeated scan behind a different adapter while preserving
`Selection` and `Policy.State.select`. We must also compare coalesced live offers
with append-only stale entries and decide how much of a generic fact, as
opposed to exact bounded policy features, a reusable policy should see. These
choices change cost and convenience, not the admission or replay boundary.

The corrected logical frontier experiment does **not** yet select a production
representation. Its indexed arm maintains a binary maximum-priority heap from
one seed view and newly appended work and suggestion events; it is not a FIFO
queue cursor. Both arms execute the same maximum policy through
`Policy.State.select`, start from a fixed point reached through the public
request/reply API, and must agree on the complete choice trace, facts,
decisions, calls, improvements, queue coalescing, dismissals, and checksum.

The experiment reports a vector rather than the earlier incomplete
`288`-versus-`8` scalar. It counts complete-view backing slots and emitted
offers, clock slots rebuilt by each wrapper state advance, suggestion-pruning visits,
dependency watcher visits including suppressed insertions, appended events,
semantic rechecks, variable-length semantic-key items, priority comparisons,
and heap moves. These logical units are shown separately: their machine costs
are not assumed equal. On the small merge-gated fixtures:

- one root fanning out to six sinks gives scan/index aggregate touch counts
  `294/260`, while both arms already share `112` clock synchronizations and
  `14` suggestion-pruning visits;
- four roots densely waking five sinks records all `20` watcher visits—five
  insertions and fifteen suppressed duplicates—and gives `297/265`;
- five sinks each emitting three disposable split suggestions gives
  `1287/769`; the scan inspects `424` historical backing slots, while the
  index consumes five work plus fifteen suggestion events from a single
  seven-slot seed view.

The aggregate is only a convenient checksum over the reported columns, not a
wall-time prediction. In particular, the current wrapper still rebuilds every
application, equality, and retained-suggestion clock array on each
request/reply transition. That shared work is often dominant and must itself
be made incremental before an event-indexed production frontier can realize
its intended asymptotics. The bounded complete scan remains the executable
reference and differential oracle. Coalesced mutable entries, a versioned
stale heap, and other incremental layouts remain open candidates until they
are implemented at the clock-synchronization boundary and compared with
scientific timing and larger traces.

The first policy wrapper treats age as continuous eligibility age. A dirty
application or equality keeps its birth time while its versioned semantic key
refreshes, becomes inactive when selected, and receives a new birth time if a
later dependency change wakes it again. Retained suggestions never refresh
into different proposals: selection, dismissal, or failure of their
variant-specific freshness guard tombstones them permanently. A rejected
instantiation, or automatic tombstoning of a retry or instantiation, marks the
scope incomplete; a discarded stale split remains optional. This accounting
also applies when policy control adopts an engine snapshot containing an
already-invalid retained suggestion. Adopting a snapshot with an open reply
latch also marks the scope incomplete: the selected application is not exposed
as a second offer, so an empty visible frontier is not a fixed point. The
prototype conservatively treats
every automatically tombstoned retry as completeness-relevant, including a
weak or stale retry. Whether some failure reasons can be proved redundant and
discarded without that penalty remains an open policy question.

Freshness is offer-specific. An invocation or retry compares the concrete
application and relevant current input versions. An anchor-local rule remains
fresh across an unrelated append-only extension. A `watchesProgram` rule also
requires the exact program version: extension stales its old offer and requeues
the application against the new snapshot. Instantiation shape is validated
before retention; offer construction rechecks freshness and authoritative
generation without resolving the draft again, and selection repeats full
admission against the current append-only program. A split compares its scope,
target fact version, and endpoint resource bound; an unrelated append-only
program extension need not stale it. Domain-specific interiority belongs to
the later scope/branch validator which constructs the complementary children.
Proactive invalidation is an optimization, so selection always rechecks the
conditions it owns.

Policy decisions, retained decision notes, effort, and live frontier size have
independent deterministic limits. Even a rejected stale selection consumes a
decision step, preventing a faulty policy from looping for free. A rule defines
the meaning of its own bounded effort ladder: pieces, Taylor degree, reduction
precision, or another function-specific choice. Different incomparable
methods remain separate registrations rather than pretending their effort
numbers share a scale. The engine bounds action and retry effort, every
structural suggestion, each `CostObservation` component, and negative
diagnostic identifiers before they can enter policy state. These independent
bounds limit representation size; they do not assign cross-rule semantic
meaning to an effort, diagnostic, or cost number. Payload-arena identifiers
remain the explicit unfinished exception described above.

The engine bounds every choice attempt and the structural, cost, effort, and
diagnostic values enumerated above, but it cannot force an arbitrary external
callback to terminate. Shipped policies are structurally fuelled and audited;
nontermination of a malicious policy or rule registry is outside theorem
soundness and produces no proof.

Every attempted choice has a bounded audit entry containing the decision
serial, versioned policy key, expected semantic offer key, bounded note, and
disposition (`selected`, `dismissed`, `stale`, `invalid`, or `resourceLimit`).
Offer identifiers are never deterministic tie-breakers because allocation
history can change them. The `replay` policy selects recorded semantic keys and
reports divergence without state mutation when the expected offer is absent.
Proof replay ignores this policy log and checks only fact, equality, instance,
and split derivations.

Canonical instantiation keys remain an experiment. Version `v0` preserves
proposed SSA dependency order, preserves the proposal equality order, and
never deduplicates the ordered input-slot list; this makes the initial
implementation exact and easy to test but not yet canonical under reordered
equality reports. A later candidate sorts/deduplicates unordered equality
pairs. Payload erasure can leave two semantic duplicates with different proof
recipes. The engine must either retain the first by bounded response ordinal,
include that ordinal in the offer key, or require a stable registry-defined
recipe key; freshly allocated payload identifiers are never canonical
tie-breakers.

The policy experiment proceeds in replaceable increments:

1. retain the complete source invocation for every suggestion;
2. split FIFO `poll` into engine operations which prepare one selected
   concrete application or equality contractor;
3. expose a bounded scan frontier and reproduce FIFO as a reference policy;
4. return exact fact deltas, logical costs, and frontier changes from reply
   admission;
5. add the external policy driver and compare scan, staged, replay, and
   versioned-priority implementations on identical semantic offers;
6. run that unchanged driver over concrete function packages, including a
   retryable enclosure, a structure-triggered alternate form, equality
   contraction, and a function-owned split landmark.

The centered-product/reciprocal package canary reaches step 6 in both
search-only and proof-producing modes. One deterministic schedule selects
subtraction and multiplication propagation, the structure matcher,
instantiation admission, the centered function's split handler and forward
propagator, equality contraction, reciprocal propagation, a precision retry,
and finally the centered function's split suggestion. It adds the centered
node at generation one, narrows both representations to `[0,1/4]`, improves
the enclosure of `1/3` at effort one, and returns a prepared plan at
`x = 1/2`. The
proof-producing schedule also dismisses the effort-two retry and therefore
retains an honest incomplete marker. Its arena contains the exact sequence of
fact, instance, and equality roles; the admitted instance event, equality
edge, and centered fact provenance resolve to entries owned by their
originating package actions. No branch is executed, so this is evidence for
policy routing, ownership, evidence freezing, and freshness, not for scope
creation or split interiority.

Once policy control begins, the wrapper is the sole scheduling authority for
that state: callers use its `view`, `select`, `submit`, equality, and admission
transitions. Mixing those calls with the reference FIFO `poll` would leave
tombstoned append-log entries and conflicting action serial authority. The FIFO
path remains a separate reference run for trace comparison, not an interleaved
API.

Only after those transition traces agree do we choose the production frontier
representation. This keeps scheduling experiments independent of any rational
or elementary-function implementation.

The initial prototype policies are:

- `balancedV1`: the first deterministic default candidate described below;
- `propagateV1`: propagation and effort increases, with solver splits disabled;
- `bisectV1`: a diagnostic midpoint policy after cheap saturation;
- `replay`: follows an explicitly supplied action plan for regression tests.

Versioned names let a downstream proof script pin search behavior while the
default alias can improve. A pinned policy is not a soundness requirement. It
is only a reproducibility aid.

### Default-policy contract

The normative requirements on any release default are smaller than one
particular scoring formula.

- For a fixed validated program, registry contents, configuration, and Lean
  environment, offer choice under a step budget is deterministic.
- Candidate maps are traversed in canonical sorted order. The final tie-break
  includes action kind, `NodeId`, versioned `RuleKey`, input fact versions,
  equality endpoints and endpoint versions, effort, generation, and split
  point; hash-table order and freshly allocated identifiers are not
  tie-breakers.
- Scores use bounded integer or exact arithmetic with specified saturation,
  never `Float` or host timing.
- A fairness mechanism eventually samples every continuously eligible action
  when the budget is unbounded and only finitely many new actions are added.
- The policy reports enough observations to replay and compare its decisions;
  changing it cannot change proof validity.

`balancedV1` is the initial empirical default candidate. Its first prototype
uses four stages.

1. Drain cheap equality, forward, and backward work whose inputs changed.
2. Run untried applicable enclosure methods with their initial effort.
3. Compare targeted effort increases, rewrites, local range refinement, and
   contractor probes.
4. If no candidate has adequate predicted gain, choose a solver split and
   repeat in both children.

The prototype computes a goal-directed potential rather than summing raw widths.
Nodes on the backwards dependency slice from the desired comparison or current
contradiction receive greater weight. A node's uncertainty records:

- how many ends remain unbounded;
- a capped base-2 width for a bounded interval;
- whether a strict cut would close the goal where a non-strict cut does not;
- endpoint bit length;
- estimated proof cost;
- distance in the program from a fact that can close the branch.

The coefficients, stage boundaries, uncertainty components, and score formula
are policy-tuning benchmark data, not public contracts. They live in
`PolicyConfig` and are reported by tracing.

The first scoring experiment gives an action that has run before its observed reduction in
weighted potential divided by declared work plus estimated proof cost. An
untried action receives an optimism bonus. Repeated `noChange` results decay
the score unless an input version or effort changes. A fixed quota selects the
oldest still-valid action in the highest nonempty fairness tier instead of the
best score. A competing implementation uses a bandit-style score, and a third
uses a simpler staged queue. Benchmarks compare solved corpus, proof nodes,
deterministic work, and robustness under irrelevant actions. A finite
configured budget makes no completeness promise.

The original sensitivity proposal is recovered as a simple special case: if
`m` is the global uncertainty measure and an action changes it to `m'`, the
action's measured sensitivity is a monotone function of `m - m'` or `m / m'`.
The first implementation tests a difference on capped logarithmic widths so
unbounded values and zero width do not require exceptional arithmetic. This is
replaceable policy data.

### Precision, propagation, or splitting

The policy records why a range is wide.

- If doubling effort materially moves an endpoint, another `improve` action is
  promising.
- If endpoint movement is much smaller than the interval width, the loss is
  probably input uncertainty or dependency. The policy favors a centered
  form, contractor, rewrite, or split.
- If a propagation sweep contracts a relevant variable, another sweep is
  cheap and receives priority.
- If a virtual split probe predicts two substantially better worst-case
  children, a solver split is preferred.
- If a singularity, kink, or certified critical point lies inside an interval,
  the associated rule suggestion outranks an arbitrary midpoint.

Universal proof search must close every child. Split scoring therefore uses
the worst predicted child, with total predicted proof size as a tie-breaker.
An average-only score can repeatedly create one easy branch and one hopeless
branch.

### Split candidates

Rules may suggest a node other than one of their direct arguments. Each
suggestion names a dyadic point and a reason. The first `balancedV1` prototype
orders otherwise comparable suggestions as follows:

1. a pole, total-function boundary, or other semantic landmark;
2. an `abs`, `min`, or `max` kink;
3. a certified derivative zero or trigonometric extremum;
4. a point proposed by a productive backward contractor;
5. zero, one, or another small dyadic inside an unbounded interval;
6. the midpoint of a bounded interval.

A symbolic or irrational landmark cannot be a global cut in this first
format. Its rule instead proposes a nearby dyadic guard backed by a certified
enclosure, or handles a symbolic partition entirely inside its local proof
payload.

The concrete `Dyadic` split point and `EndpointLimit` in the current generic
experiment are a deliberate real-domain-v1 seam, not a claim that every future
domain or branch policy must use dyadic cuts. Keeping that seam concrete lets
the arbitrary real-function vertical proceed without prematurely choosing
between a cut-type parameter, a domain-owned split interface, and an opaque
landmark decoded by the branch layer. That choice remains open and must be
revisited before stabilizing a multi-domain API; it does not require changing
the function-package, instantiation, or replay protocols now.

A split on term `t` adds `t ≤ m` to the left child and `m < t` to the right
child. This complementary form preserves strictness, avoids a duplicate
boundary case, and is justified by linear order. A split need not target a
free variable. Splitting a derived node is useful when several occurrences
share that node, though contractors are needed to transfer the cut to its
arguments.

### Budgets and termination

Every search is finite because the configuration bounds:

- reified base nodes, dynamically generated nodes and equality edges,
  instantiation actions and generation depth, and alternate forms per original
  node;
- accepted actions;
- rule invocations and maximum effort;
- solver split depth and number of leaves;
- local range pieces made by one rule;
- effective endpoint height, alignment shift, and regularized working
  precision;
- retained trace nodes, frozen payload entries and bytes, kernel-checker work,
  and estimated proof nodes;
- optional wall-clock time.

`maxEndpointHeight` is measured after canonical dyadic normalization as the bit
length of the absolute numerator plus the magnitude of the signed binary
exponent. This deliberately charges dynamic range linearly: a fact near
`2^-333` costs at least 333 even when its numerator is tiny. Regularization can
reduce numerator growth and working precision, but cannot shrink that dynamic
range; defaults must therefore cover the several-hundred-bit exponents in the
PNT+ tail corpus. A separate alignment-shift limit caps the exponent difference
used by comparison and arithmetic. This reflects the actual shifted-integer
work; an exponent of magnitude `2^30` is not treated as a 31-bit endpoint.
This is the conservative first accounting policy. Telemetry separately records
numerator bits, encoded exponent bits, exponent magnitude, and actual shifted
integer work so experiments can replace the aggregate metric without weakening
the preflight resource guard.

Every backend in the D2 comparison implements a common exact endpoint-cost and
preflight interface. The rational candidate at minimum charges normalized
numerator and denominator bit lengths, predicts cross-multiplication and
regularization work before allocating the enlarged integers, and returns the
same distinct `resourceLimit` outcome when its configured bound is exceeded.
Backend-specific numbers need not be numerically identical to dyadic height,
but each must prevent an ostensibly small encoded exponent or denominator from
bypassing the actual arithmetic-work budget and must expose its components in
telemetry.

For serialized rational certificates, entry counts and encoded integer byte
lengths are checked before arbitrary-precision decoding. After decoding,
numerator and denominator size checks precede the nonzero-denominator and
coprimality checks; no gcd, shift, or cross-product is attempted before its
input-size preflight. Per-operation temporary arithmetic and aggregate checker
work are budgeted separately from retained endpoint size.

For the dyadic candidate, before an exact comparison or arithmetic action the
engine computes the required alignment shift without performing it. If it
exceeds the budget, the action returns `resourceLimit` and records the
exhausted limit; it is never interpreted as “not contradictory” or as a failed
mathematical comparison. An oversized new candidate is not installed. The rule
may instead return a separately justified outward-regularized candidate within
budget when regularization actually helps. Existing stronger facts are never
deleted to satisfy the limit, and an oversized result is reported distinctly
from `noChange`. The rational candidate applies the common exact-cost preflight
above to cross-multiplication and denominator growth instead.

Retained endpoint height and temporary arithmetic work are distinct limits.
For subtraction, every endpoint-alignment pair needed by an interval rule is
preflighted before the first subtraction runs; temporary aligned work is
bounded from `H + S`, while each canonical result must separately return within
retained height `H`. For multiplication, the checker predicts the sum of input
mantissa bit lengths and the signed sum of exponents before constructing the
product, then checks the canonical result. Using the signed exponent sum is
important: it admits cheap cancellation such as a tiny power of two times its
inverse while still rejecting a genuinely oversized product. Comparable
preflight-before-allocation obligations apply to rational cross-products.

Payload limits are enforced when an accepted recipe is frozen. Deduplicated
tables are counted once in the immutable arena. A one-node derivation cannot
bypass certificate-byte, entry, or checker-work limits by pointing to an
unbounded payload.

Reaching a budget returns `unknown` with the best state and diagnostics. It
does not silently lower a target, discard a branch, or turn a failed strict
bound into a weak one.

After any solver split, a reported bound is global. For each requested node,
the result takes the hull of its proved interval over every live, completed,
and pending leaf. An unexplored child contributes at least its inherited
ancestor facts, never the tighter state of its sibling. The result retains a
partial `BranchTree` whose leaves close membership in this hull, even if they
do not close the original goal. `interval_bound` can therefore replay a real
theorem from an `unknown` search; diagnostics never present a branch-local cut
as a context-wide fact.

## Derivation trace

The search log may be large, but the returned derivation is a backwards slice
from the closing facts. Parent identifiers make that slice linear in the
facts actually used. The constructor set below is a design sketch, not a frozen
serialization format; the vertical kernel-replay prototype may separate
validation, evaluation, program-extension, and output lookup differently.

```lean
structure FactId where
  scope : ScopeId
  index : Nat

inductive EqualityRef
  | edge   (edge : EqEdgeId)
  | source (source : SourceId)

inductive Derivation
  | source     (source : SourceId)
  | rule       (rule : RuleKey) (inputs : Array FactId) (payload : PayloadId)
  | transportEq (equality : EqualityRef) (input : FactId) (target : NodeId)
  | weaken     (input : FactId) (cut : Cut)
  | splitAssumption (parent : ScopeId) (side : SplitSide)
      (node : NodeId) (cut : Dyadic)

inductive Close
  | goal          (facts : Array FactId)
  | contradiction (lower upper : FactId)

inductive BranchTree
  | leaf  (scope : ScopeId) (close : Close)
  | split (scope : ScopeId) (node : NodeId) (cut : Dyadic)
      (leftScope rightScope : ScopeId) (left right : BranchTree)

inductive ProofPlan
  | direct (tree : BranchTree)
  | byContradiction (counterScope : ScopeId) (negatedGoal : SourceId)
      (tree : BranchTree)
```

Every fact identifier is scope-qualified. A fact may depend only on facts in
its own scope or an ancestor scope. The two child scopes of a split are fresh,
and neither may refer to the other's facts. The left child receives the closed
upper cut `node <= cut`; the right child receives the strict lower cut
`cut < node`. The branch-tree validator checks these relationships, unique
parentage, acyclicity, and that every leaf has a closing witness.

`transportEq` preserves side, value, and strictness while moving a fact across
a proved equality. Validation checks that the equality is visible in the
fact's scope, that its endpoints match the input and target nodes in one of the
two permitted directions, and that a source equality names an original or
ancestor hypothesis rather than a sibling fact. The trace is paired with the
validated equality-edge table and its immutable proof recipes, including edges
introduced by bounded instantiation. Thus alternate-form intersection and
contextual equality transfer have an explicit replay step.

The branch tree refers to shared derivations. Facts established before a split
are stored once in the ancestor scope. Within a branch, repeated uses of one
fact refer to one identifier. Backwards slicing starts from every leaf's
`Close`, retains the necessary ancestor facts and split assumptions, and
discards all other probes. The Mathlib companion turns this representation
into nested `let`, `have`, and case bindings so Lean's elaborator and kernel
also see the sharing.

`ProofPlan.byContradiction` tells replay to introduce the negated target in a
fresh counterexample scope before replaying its tree. Its `SourceId` cannot be
resolved as an original local hypothesis, and every leaf in that plan must
close by contradiction. A direct plan may close the target or use a
contradiction already derivable from the original context. A partial
best-bound certificate always uses `direct`, so a failed contradiction attempt
cannot leak its temporary assumption.

The trace never contains a proof of its own validity. It is untrusted data.
The companion registration for each `RuleKey` reconstructs the corresponding
theorem application or checks a rule-specific certificate. A trace is paired
with its immutable payload arena and operation table. Replay rejects an
unknown rule version, wrong payload schema, dangling payload identifier, or
scope violation.

## Diagnostics and observability

On `unknown`, the engine returns enough information for a user or future policy
to act:

- the best interval for each requested term;
- the node with the greatest goal-directed uncertainty;
- the rule and action that last improved each endpoint;
- which rules were inapplicable and which exhausted effort;
- whether loss appears dominated by endpoint rounding, dependency, an
  unbounded input, or branch count;
- the best split suggestion not taken;
- all exhausted budgets.

Trace levels are `off`, `summary`, `actions`, and `bounds`. The default failure
message uses `summary`. Machine-readable observations can be exported for
offline policy tuning, but reading such telemetry is never required to check
a proof.

## Applications

The tactic is the first client, not the only one. Two downstream applications
constrain the framework without requiring either application to be implemented
in the first release.

### Verified raster graphs

Given a real function, an exact dyadic viewport, and raster dimensions, a plot
client can ask the engine for range enclosures over pixel columns or adaptive
subcolumns. The primary certified-image contract is conservative coverage:

- every point of the graph inside the viewport lies in a marked pixel; and
- every unmarked pixel carries a checked proof that its rectangle is disjoint
  from the graph.

This makes every binary pixel claim correct: blank means proved absent, while
marked means the graph may occur there. It does not falsely claim that every
marked pixel is hit. A richer three-state raster may additionally mark a pixel
`present` only when it carries an existence proof, for example from exact
endpoint values and continuity plus an intermediate-value argument; remaining
marked pixels are explicitly `unknown`. No finite algorithm can always decide
intersection with every pixel boundary, so unresolved pixels are part of the
honest interface rather than rendered as proved occupancy.

Pixel rectangles use an exact, documented boundary convention, preferably
half-open cells with a separately closed outer viewport. Open cuts matter:
they decide whether a graph lying exactly on a pixel boundary belongs to one
cell, its neighbour, both in a conservative mask, or neither outside the
viewport. Raster indexing, clipping, integer dimensions, and the dyadic map
between coordinates and pixels are checked data, not assumptions made by an
image library.

A certificate need not contain one independent proof per pixel. One interval
fact over a column or adaptive tile usually proves a contiguous band of
possibly occupied rows and simultaneously excludes the rows above and below.
Run-length, tile, and derivation sharing are therefore certificate
representations to benchmark. The untrusted renderer emits ordinary raster
bytes plus a certified mask or classification table; a small checker validates
that the bytes encode that table. Kernel replay proves the coverage/disjointness
theorem from shared interval derivations, not from the PNG decoder.

The ordinary framework supplies all required search mechanisms: arbitrary
function propagators bound the range; instantiation introduces centered forms,
range reductions, derivatives, or continuity witnesses when useful; local
subdivision sharpens one column; and solver subdivision refines the spatial
partition. Discontinuities and partial domains are never joined by a cosmetic
line. A singular or out-of-domain subcolumn is split, clipped, classified
unknown, or proved absent according to explicit facts.

An initial conformance fixture should plot an opaque continuous function whose
registry supplies only generic enclosures, then compare a coarse raster with
an adaptively refined one. Both must satisfy the same coverage theorem; the
refined mask may have fewer unknown pixels. Later challenge fixtures include a
tangent asymptote, a narrow extremum requiring an instantiated derivative or
centered form, and a curve exactly on pixel boundaries.

### Certified differential-equation solvers

A future validated ODE solver can use this engine as its expression,
propagation, and policy component without making ODE algorithms part of the
initial interval library. Over a time slab it may register arbitrary
propagators for the right-hand side, Jacobian, Picard operator, Taylor
coefficients and remainder, invariants, and event functions. Instantiation can
introduce derivative and Taylor expressions only when a step method needs
them; function-local refinement can subdivide a remainder calculation, while a
solver split represents genuinely alternative state boxes or event cases.

The eventual ODE companion remains responsible for the mathematical theorems:
existence, uniqueness when claimed, enclosure of the solution tube, and
composition of consecutive steps. The interval engine contributes checked
facts and replayable dependencies to those theorems; successful numerical
search alone never asserts that a solution exists.

This downstream use argues for keeping the present abstractions:

- domains and facts must extend beyond one scalar endpoint representation,
  either through vector/box facts or coordinated scalar nodes;
- operation keys and propagator caches must remain opaque to the scheduler;
- expression instantiation, equality transport, scoped facts, and exact
  resource limits must work over many consecutive program extensions; and
- policy observations must distinguish local refinement from global branching
  and proof cost from numerical gain.

We do not choose Taylor models, affine arithmetic, zonotopes, a time-stepping
scheme, or grind integration in this SPEC. Small mock ODE dependency graphs are
useful scheduler and cache tests, but a certified integrator is a downstream
design with its own SPEC.

## Complexity contract

Let `n` be the number of program nodes, `e` the number of argument-to-consumer
edges, `q` the number of queued candidates, and `b` the number of live branch
states.

- Program validation and initial dependency construction are `O(n + e)`.
- One worklist update is proportional to the number of rules attached to the
  changed node and its consumers. The scheduler does not scan all `n` nodes
  after every fact.
- Fact comparison and contradiction checks use exact endpoint comparison. For
  the dyadic candidate, integer cost is proportional to effective endpoint
  height and the permitted exponent-alignment shift; a rational candidate must
  declare and benchmark its corresponding exact-arithmetic cost.
- Branch storage must make child creation and isolated updates cheap at the
  program sizes and leaf counts in the corpus; it must not silently copy all
  `n` fact slots at every split once that cost dominates. Candidate
  implementations include Lean `Array` copy-on-write, a persistent paged trie,
  a chunked vector, and a depth-first mutable trail with rollback. Their actual
  complexities and constant factors are reported. No one representation is
  selected before the crossover benchmark.
- The priority-queue candidate targets `O(log q)` amortized candidate
  insertion, invalidation, and selection, excluding the declared cost of
  rescoring a stale candidate. A diagnostic policy that scans candidates
  reports `O(q)`; other policy data structures state and measure their own
  model.
- Total search is bounded by the configured action, leaf, endpoint-height, and
  payload budgets.

Individual Mathlib-free propagator packages declare their logical cost model
and cache behavior at the external registry boundary. The Mathlib companion
supplies the soundness theorems and replay interpretation for retained
payloads. The generic scheduler neither interprets those semantics nor hides
their declared cost inside a scheduler bound.

## File organization

- `HexInterval/Bound.lean`: lower and upper cuts, comparison, normalization.
- `HexInterval/Interval.lean`: intersection, hull, arithmetic, splitting, and
  regularization.
- `HexInterval/Program.lean`: node identifiers, SSA program, dependencies.
- `HexInterval/Fact.lean`: facts, versions, provenance, contradiction checks.
- `HexInterval/Action.lean`: requests, outcomes, suggestions, observations.
- `HexInterval/State.lean`: branch state and incremental worklists.
- `HexInterval/Policy.lean`: policy interface and `balancedV1`.
- `HexInterval/Search.lean`: budgeted branch search and derivation slicing.
- `HexInterval/Trace.lean`: diagnostics and machine-readable telemetry.
- `conformance/HexInterval/{Conformance,EmitFixtures}.lean`: Lean-only checks
  and oracle fixtures.
- `bench/HexInterval/Bench.lean`: Mathlib-free interval and scheduler
  benchmarks.

## Conformance

The required Lean-only profile covers every interval shape and operation with
typical, boundary, and adversarial inputs. In particular it includes:

- all four finite endpoint closure combinations;
- equal endpoints in all closure combinations;
- empty, singleton, one-sided unbounded, and whole intervals;
- table-driven empty laws: every unary operation and `regularize` preserve
  empty; binary image operations and intersection absorb it; hull has it as an
  identity; splitting it returns two empty pieces; `pow empty n = empty` even
  at zero, while `pow I 0 = {1}` for every nonempty `I`;
- intersection and hull at equal open and closed cuts;
- split coverage at an endpoint and an interior point;
- negation and addition closure propagation;
- multiplication by singleton zero, by a nonsingleton interval containing
  zero, and by unbounded intervals, with exact endpoint-attainment flags;
- the distinct cases `mul empty whole = empty`, `mul {0} whole = {0}`, and
  `mul whole {0} = {0}`;
- `abs`, `min`, and `max` with tied open and closed extrema;
- precision-indexed reciprocal and division for `{3}`, positive, negative,
  singleton-zero, one-sided-zero, and sign-crossing inputs;
- powers on negative, mixed-sign, open-zero, and singleton inputs;
- rational-to-dyadic projection at exact and inexact values, including the
  strict cut gained by moving a closed source outward;
- canonical raw rational tables, including negative numerators and canonical
  `0 / 1`, and rejection of zero denominators, noncoprime equivalent
  encodings, unused oversized entries, excessive projection shifts, and
  one-step-over-budget cross-products before allocation;
- regularization idempotence, outward containment, moved closed cuts, and
  exact-grid open cuts;
- a dependency worklist in which one fact wakes only the affected consumers;
- opaque unary chains, fan-out with a ternary join, and forward/backward rule
  cycles in which the expression DAG remains acyclic;
- multiple rules for one node, including a later effort result that does not
  improve the interval;
- an atomic multi-output outcome, repeated-operand watcher deduplication,
  projected-input enforcement, and rejection of an undeclared write or a
  mismatched delayed reply without state mutation;
- package-major registry assembly with two handlers sharing a `Nat` cache,
  independently appended packages using `List Nat` and `Bool` caches, exact
  route and final-program signature checks, external required signatures,
  duplicate operation/rule-key and undeclared-head rejection, cache-preserving
  rejection of wrong routes, duplicate replay-format rejection, and a `Type 1`
  registry threaded through both drivers;
- a private package session which freezes and relocates reply-local evidence,
  continues independent work after malformed or locally oversized drafts,
  retains incompleteness across a later successful reply, charges nested
  equality payload uses, keeps derived draft-cell accounting tied to the exact
  bounded transaction, and intentionally reserves fatal entry/body-cell stops
  for genuine remaining-capacity exhaustion after an earlier arena commit;
- two unrelated opaque function packages which both use local fact schema `7`
  but retain distinct `(RuleKey, role, schema)` addresses and validate
  incompatible bounded body shapes; undeclared formats, malformed bodies, and
  format failure after a previously committed invocation leave no partial
  current transaction, while recoverable reply-local draft-cell refusal
  precedes package validation;
- real dyadic fact and instantiation packages running through the private
  proof session with exact empty-body schema `0` declarations, including
  rejection of a trailing body cell and distinct rule-epoch ownership;
- an anchor-local opaque shape rule which distinguishes `x * (one - x)` from
  products with a reversed difference or a different repeated input, proposes
  the exact existing node identifiers while receiving no fact inputs, repeats
  the match on a newly appended DAG suffix, and admits both the append-stable
  pre-extension proposal and the new proposal after revalidation with their
  exact assigned node identifiers and generations;
- two append-stable rules which propose the same absent product and distinct
  equality outputs in either selection order: the first materializes a
  depth-three tower, the second CSE-hits the entire prefix, both remain
  theorem-generation one under an exact generation-one cap, and the stored
  structural depths are identical in either order;
- a genuine `watchesProgram` matcher which proposes an increasingly long
  generation-one tower: two extensions CSE-hit their old prefixes, while the
  depth-four proposal is dropped under an exact `maxNodeDepth = 3` cap without
  aborting unrelated rule processing; the raw driver reports queue saturation,
  not policy completeness;
- one mixed reply in which a candidate fact, an affordable instantiation, and
  a later retry survive an over-depth instantiation between them; the loss is
  counted and policy completeness becomes false;
- exact-capacity replies showing that an over-depth proposal does not consume
  the sole retained slot, while a malformed instantiation already in the
  capacity suffix is intentionally dropped without validation and marks
  policy incomplete rather than invalidating the useful prefix;
- reply-boundary rejection of malformed structural/equality proposals, with no
  retained offer that can later be silently tombstoned;
- an end-to-end concrete registry run in which `x * (1 - x)` first receives
  the dependency-losing hull `[0,1]`, structural instantiation adds the
  centered node and an opaque-payload equality, the alternate callback returns
  `[0,1/4]`, and equality transport narrows the original expression to the same
  fact; its anchor-local proposal remains append-stable and does not consume
  closure budget by rerunning after its own extension, while `z = 2*y` shows a
  backward contraction waking an initially inapplicable forward rule;
- the same concrete registry under the external policy driver, selecting
  propagation, structural matching, instantiation, equality, reciprocal retry,
  and a function-owned split in a checked event order; it returns an
  endpoint-resource-checked plan at `1/2`, leaves the next retry offer live,
  and performs no branch/interiority step;
- the proof-producing policy session over those same packages, selecting every
  offer class through one private owner, retaining exact fact, instance, and
  equality replay formats, rolling back a prospectively frozen rejected write
  and both malformed and undeclared formats, keeping package-local payload
  use, draft-count, draft-cell, atom, and schema bounds live but incomplete,
  making genuine mid-run whole-arena exhaustion fatal, and exposing an empty
  failed frontier as incomplete rather than saturated;
- an interval-representation-free sine package whose matcher recognizes
  `sin (-x)`, atomically introduces `sin x`, `-(sin x)`, their equality, and a
  dynamically scoped contractor, then runs that contractor through policy and
  freezes its fact recipe; changing only the scope's semantic watch must
  trigger package veto with no arena, proposal, or matcher-cursor commit;
- undirected equality transport, including incomparable endpoint facts that
  improve both sides atomically, equality chains, reactivation after a later
  function improvement, and an original expression transferring its bound to
  an instantiated alternate before the alternate's arbitrary propagator runs;
- exact equality provenance and reversed-edge deduplication, plus one-step-short
  equality, queue, action, and accepted-fact limits with no partial update;
- deterministic action choice for a fixed `balancedV1` configuration;
- two policies over the same opaque `f` and dynamically introduced `g`: one
  retries `f` before instantiation and one instantiates first. They must reach
  the same final facts and endpoint-resource-checked prepared split plan (with
  branch creation and interiority left to the scope layer) while recording
  different exact rule-call counts; replay of either semantic offer log is
  exact, and a stale effort or exhausted decision budget stops without state
  mutation;
- derivation slicing that removes failed probes and unused facts;
- branch validation that rejects sibling fact references and mutable or
  dangling payloads;
- program-extension validation that rejects bad topology, duplicate canonical
  keys, invisible branch-local nodes, invalid equality endpoints, and an
  instantiation beyond each generation budget;
- deterministic deduplication of two rules proposing the same expression and
  equality edge in different orders;
- two successive opaque instantiations which add absent expressions, activate
  their registered propagators, recompute generations one and two, and leave
  the previous snapshot intact at each one-step-short limit;
- budget exhaustion returning `unknown` with a nonempty diagnostic record.

The `ci` profile cross-checks finite arithmetic against an independent Python
implementation using exact `Fraction` corner calculations and explicit
endpoint-attainment flags. `python-flint` Arb is reserved for the companion's
elementary-function fixtures. The oracle result is testing evidence only. It
is never imported by the tactic. Open-cut and unbounded semantics also receive
direct Lean property checks because ordinary ball types do not represent them
faithfully.

No conformance assertion uses `native_decide`. Small closed computations may
use ordinary `#guard` or `by decide`. Larger deterministic campaigns run as
compiled fixture emitters and compare their serialized results outside Lean.

## Benchmarks

The Mathlib-free benchmark target measures:

- `intersect`, `mul`, and `regularize` over effective endpoint height and
  exponent-alignment distance;
- worklist saturation over synthetic chain, fan-out, and shared-diamond
  programs;
- bounded-instantiation saturation over useful, duplicate, and deliberately
  explosive trigger families, recording generated nodes, equality edges,
  suppressed instances, and proof-slice retention;
- HC4-style propagation and local-shaving traces over translated small
  RealPaver-shaped dependency graphs, without importing their floating-point
  semantics;
- branch creation and isolated updates for `Array` copy-on-write, persistent
  paged-trie, chunked-vector, and trail/rollback candidates, crossing program
  sizes 20, 50, and 500 with 8, 100, and 1,000 leaves;
- policy selection over the number of available actions;
- derivation slicing over total log size and retained proof size;
- the same centered-product DAG under compiled Core `Rat` planning and
  transparent canonical-table replay, separating planning, endpoint
  interning, serialization, bounded decoding, table validation, and compiled
  replay; an external build-only probe measures ordinary-kernel replay of the
  same certificate, with dyadic-valued sources, `1 / 3`-valued sources, and a
  denominator-height ladder.

The opaque-forest logical-count canary starts from a saturated set of
disconnected unary chains and tightens one root. With four depth-eight chains,
the dependency worklist makes 8 rule calls while whole-network fixed-point
rescanning makes 64; both accept 8 improvements and produce the same
position-sensitive fact checksum. For `t > 0` chains of depth `d`, the current
fixture records `d` incremental calls versus `2*t*d` structural calls. These
counts motivate the incremental baseline without freezing queue coalescing,
priority policy, or state storage.

The separate policy-frontier canary compares complete scans with a genuinely
maintained maximum-priority heap on fan-out, dense multi-output wake, and
retained-suggestion churn workloads. Its executable prints the full logical
work vector described in the policy section, and small instances are
merge-gated twice: ordinary `#guard` equivalence checks build with
`HexConformance`, while the compiled spike's `canary` mode builds and runs in
the existing single CI job. This is deterministic representation evidence,
not scientific timing; it neither uses a custom timing loop nor freezes the
current touch-count aggregates as performance contracts.

The declared models follow the complexity section above. Scientific runs also
record accepted actions, endpoint heights, live leaves, retained derivations,
and cache hits so a faster time cannot conceal a weaker search.

Tactic elaboration and Mathlib theorem replay are measured in the companion's
local test profile. They do not enter this Mathlib-free benchmark target.

## References

- Kim Morrison, [Interval arithmetic research note](https://hackmd.io/ZagrUv95RFSU-7WP9TNxUQ).
- IEEE 1788 working group, [IEEE Standard for Interval Arithmetic](https://grouper.ieee.org/groups/1788/).
- Nathalie Revol and Fabrice Rouillier,
  [Motivations for an arbitrary precision interval arithmetic library and the MPFI library](https://perso.ens-lyon.fr/nathalie.revol/publis/RR05.pdf).
- Fredrik Johansson,
  [Arb: efficient arbitrary-precision midpoint-radius interval arithmetic](https://arxiv.org/abs/1611.02831).
- Oliver Flatt and Pavel Panchekha,
  [An interval arithmetic for robust error estimation](https://arxiv.org/abs/2107.05784).
- [IBEX contractor documentation](https://ibex-team.github.io/ibex-lib/contractor.html)
  and [strategy documentation](https://ibex-team.github.io/ibex-lib/strategy.html).
- Laurent Granvilliers and Frédéric Benhamou,
  [Algorithm 852: RealPaver, an interval solver using constraint satisfaction techniques](https://doi.org/10.1145/1132973.1132980),
  and the [RealPaver 0.4 user manual](https://manualzilla.com/doc/6912445/realpaver-user-s-manual).
- Raphaël Chenouard and Laurent Granvilliers,
  [RealPaver 1.1](https://doi.org/10.21105/joss.09331), with the
  [current implementation](https://github.com/realpaver/realpaver).
- [IntervalArithmetic.jl construction and exact input guidance](https://juliaintervals.github.io/IntervalArithmetic.jl/stable/manual/construction/).
- [Boost.Interval policies and representation](https://www.boost.org/doc/libs/latest/libs/numeric/interval/doc/interval.htm).
