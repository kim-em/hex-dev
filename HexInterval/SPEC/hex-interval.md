# hex-interval (exact interval data and budgeted propagation search, Mathlib-free)

`hex-interval` is the Mathlib-free computational library for interval
arithmetic. It represents exact dyadic bounds, maintains the bounds of a
shared expression program, schedules propagation and refinement actions, and
records the successful search as a compact derivation trace. It does not
interpret a program as a real-valued function and it does not construct Lean
proof terms. Those tasks belong to
[hex-interval-mathlib](../../SPEC/Libraries/hex-interval-mathlib.md).

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

### Exact rational source facts

Lean goals often contain rational constants such as `1 / 3`, which are not
dyadic. The frontend retains each such hypothesis as an exact source fact. At
working precision `p`, it asks this library for an outward dyadic projection:

- a rational lower bound is rounded down;
- a rational upper bound is rounded up;
- an exactly dyadic rational is preserved;
- strictness is preserved when transitivity proves the projected strict cut.

Increasing effort may request a finer projection from the original rational.
It never rounds an already rounded endpoint again. This prevents accumulated
rounding drift and keeps arbitrary rational arithmetic out of the hot
propagation path.

The Mathlib-free library does not depend on `norm_num` to certify these source
facts. Lean core's ordinary `Rat` operation instances are deliberately opaque,
but core also supplies the reducible `Rat.normalize` computation and
characterization lemmas such as `Rat.add_def`, `Rat.sub_def`, `Rat.mul_def`,
and `Rat.inv_def`. A proof-facing rational backend may therefore use small
exposed wrappers around those computations, or validate canonical
numerator/denominator data by cross multiplication. D2 measures both styles
under ordinary kernel reduction before choosing a rational trace encoding.
The Mathlib companion may use `norm_num` when it is the cheapest way to close
a frontend rational leaf; that convenience is not part of the shared
library's trust or dependency story.

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

An instantiation proposal contains a versioned rule key, a canonical
substitution, new SSA instructions, equality or derived-fact recipes, and an
untrusted claimed generation. Acceptance validates operation arities and
domains, topological order, scope visibility, and every referenced input;
recomputes each node's generation from the trigger provenance and generated
dependencies, rejecting a mismatch or over-budget descendant; deduplicates
expressions by the same canonical CSE key as the base program; updates consumer
and rule indexes; and freezes the proof recipe for replay. Base nodes have
generation zero, and a generated node is one plus the maximum relevant
generation in the instance that caused it. The new expression is not trusted
merely because a trigger matched or labeled itself generation zero.

Generation is explicitly budgeted by new nodes, new equality edges, rule
applications, depth, and retained payload bytes. A canonical key consisting
of the rule, substitution, scope, and generated expression prevents duplicate
instances. Candidate traversal and insertion order are deterministic. If a
branch-local fact triggers a semantically branch-independent expression, the
node may be shared globally while the resulting fact and conditional equality
remain branch-scoped. Whether the first implementation uses that scheme or
branch-local extensions is an experiment; identifiers and replay must make
the choice explicit.

The initial feasibility comparison has three arms:

1. eagerly materialize every alternate admitted by the node/form budgets;
2. run bounded instantiation between propagation epochs, then validate and
   freeze a new program snapshot;
3. append nodes lazily during search with incremental dependency updates.

The corpus measures program size, duplicate instances, useful-instance ratio,
search time, and replay size. Safe budget exhaustion leaves the already
validated program and facts usable.

## Rule protocol

Rules are explicit registrations, not typeclass instances. Typeclass search
must not recursively decide which algorithm computes an expression's bound.
The registry may contain several rules for one head symbol, and the policy may
try or combine all of them.

The explicit registration and validation boundary is fixed. Discovery and
scheduling above it remain empirical: one arm uses an incremental registry
worklist to share facts and retain state, while a second traverses the same
registered rules in a structural, form-directed loop similar to `apply_rules`.
Neither arm uses recursive typeclass search or bypasses rule validation. The
benchmark compares these discovery styles rather than preselecting one for
every structural goal; a hybrid may use the structural loop as one action.

Rule-private caches can have arbitrary Lean types. For that reason the
Mathlib-free library does not store them in a heterogeneous array. It exposes
a request-and-reply state machine:

1. The solver produces an `Action` naming a rule, node, input fact versions,
   effort, and action kind.
2. The companion registry executes the rule and owns its cache.
3. The registry returns an `Outcome` containing candidate facts, alternatives,
   suggestions, cost observations, and an opaque proof recipe identifier.
4. When a fact is accepted, the registry freezes every value needed for replay
   into an immutable per-run payload arena. The `PayloadId` in the trace points
   into this arena, never into a mutable or evictable rule cache.
5. The solver intersects accepted facts into the state and records their
   provenance.

An invalid rule outcome may mislead search, but it cannot produce a theorem.
The companion reconstructs every retained fact from the rule's soundness
theorem. A failed reconstruction identifies a broken registration rather than
closing the user's goal.

Cost observations used by a deterministic policy are specified logical counts
such as declared arithmetic work, visited certificate entries, generated
nodes, or estimated proof nodes. Actual runtime reductions, allocations, and
wall time are telemetry only: compiler and backend changes can alter them, so
they cannot influence a reproducible action choice.

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

An `Outcome` may be `noChange`, `inapplicable`, `resourceLimit`, or `failed`
without affecting soundness. `resourceLimit` names the exhausted budget and is
not cached as mathematical inapplicability. Rules do not promise that greater
effort always gives a tighter answer. The solver intersects every result with
existing facts, measures the actual improvement, and learns from that
observation.

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

The initial saturation runs all cheap forward rules once in program order and
then drains the dependency worklist. It also runs zero-cost contradiction
checks after every accepted fact. More expensive improvement and split actions
start only after this cheap fixed point, unless a rule marks a singularity that
requires an immediate split.

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

The policy affects success and performance, never validity. The library
exposes a pure interface with private state and incremental candidate events:

```lean
structure Policy where
  State      : Type
  init       : Snapshot → State
  insert     : State → Action → State
  invalidate : State → ActionKey → State
  choose     : State → Snapshot → Option (Action × State)
  observe    : State → Action → Observation → State
```

The first `balancedV1` prototype uses a versioned priority queue. Changed facts insert or
invalidate only affected candidates; stale entries are discarded lazily when
popped. Policies intended for diagnostics may use a simpler complete scan,
but their complexity is reported honestly.

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
  environment, action choice under a step budget is deterministic.
- Candidate maps are traversed in canonical sorted order. The final tie-break
  includes action kind, `NodeId`, versioned `RuleKey`, input fact versions,
  effort, generation, and split point; hash-table order and freshly allocated
  identifiers are not tie-breakers.
- Scores use bounded integer or exact arithmetic with specified saturation,
  never `Float` or host timing.
- A fairness mechanism eventually samples every continuously eligible action
  when the budget is unbounded and only finitely many new actions are added.
- The policy reports enough observations to replay and compare its decisions;
  changing it cannot change proof validity.

`balancedV1` is the initial empirical default candidate. Its first prototype
uses four stages.

1. Drain cheap forward and backward actions whose inputs changed.
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
- The first priority-queue prototype targets `O(log q)` amortized candidate
  insertion, invalidation, and selection, excluding the declared cost of
  rescoring a stale candidate. A diagnostic policy that scans candidates
  reports `O(q)`; other policy data structures state and measure their own
  model.
- Total search is bounded by the configured action, leaf, endpoint-height, and
  payload budgets.

Individual propagators declare their own arithmetic complexity and cache
behavior in the Mathlib companion. The solver does not hide that cost inside
a scheduler bound.

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
- regularization idempotence, outward containment, moved closed cuts, and
  exact-grid open cuts;
- a dependency worklist in which one fact wakes only the affected consumers;
- multiple rules for one node, including a later effort result that does not
  improve the interval;
- deterministic action choice for a fixed `balancedV1` configuration;
- derivation slicing that removes failed probes and unused facts;
- branch validation that rejects sibling fact references and mutable or
  dangling payloads;
- program-extension validation that rejects bad topology, duplicate canonical
  keys, invisible branch-local nodes, invalid equality endpoints, and an
  instantiation beyond each generation budget;
- deterministic deduplication of two triggers proposing the same expression
  and equality edge in different orders;
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
- derivation slicing over total log size and retained proof size.

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
- [IntervalArithmetic.jl construction and exact input guidance](https://juliaintervals.github.io/IntervalArithmetic.jl/stable/manual/construction/).
- [Boost.Interval policies and representation](https://www.boost.org/doc/libs/latest/libs/numeric/interval/doc/interval.htm).
