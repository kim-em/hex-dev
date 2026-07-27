# hex-interval (exact interval data and budgeted propagation search, Mathlib-free)

`hex-interval` is the Mathlib-free computational library for interval
arithmetic. It represents exact dyadic bounds, maintains the bounds of a
shared expression program, schedules propagation and refinement actions, and
records the successful search as a compact derivation trace. It does not
interpret a program as a real-valued function and it does not construct Lean
proof terms. Those tasks belong to
[hex-interval-mathlib](hex-interval-mathlib.md).

The library is intended to support a standalone `interval` tactic. Integration
with `grind` is not part of this development. The scheduler and rule protocol
should nevertheless be reusable by another frontend later.

The procedure is deliberately incomplete. It tries to prove a requested bound
or to make a collection of hypotheses inconsistent within explicit budgets.
Failure means that the selected rules and search policy did not find a proof.
It does not mean the goal is false.

## Requirements

The design must satisfy all of the following.

1. A finite bound is an arbitrary-exponent `Dyadic`. No floating-point value is
   used as a proved endpoint.
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
must remain the default and fallback.

## Interval representation

The public shape is intentionally small. The exact constructor names may
change while the implementation is scaffolded, but the distinctions below are
part of the contract.

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

inductive Repr
  | empty
  | bounds (lower : Lower) (upper : Upper)

end Interval

/-- A canonical interval representation. -/
structure Interval where
  repr  : Interval.Repr
  valid : repr.CutConsistent

end Hex
```

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

`Repr.CutConsistent` says that `empty` is the unique inconsistent cut pair and
that a `bounds` value has ordered cuts. Over a dense ordered domain containing
the dyadics, such a pair is nonempty. `normalize` returns `empty` when the
lower value exceeds the upper value, or when equal finite values have at least
one open cut. It is idempotent. Public smart constructors and operations
return `Interval` values with this invariant. Infinite ends do not carry
meaningless closure flags. This invariant deliberately does not claim that,
for example, `(0,1)` contains an integer.

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

This avoids manufacturing an intersection proof after every update. When a
new lower fact is stronger, the state changes one pointer. The corresponding
upper fact is unchanged. If two facts state the same cut, the state retains
the one with the cheaper estimated proof. Weaker facts may remain available
when they have much smaller endpoints or lead to a cheaper downstream proof.

Two finite facts are contradictory precisely when the lower value is greater
than the upper value, or when the values are equal and either fact is strict.
That check is exact dyadic arithmetic.

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
```

The Mathlib companion proves their set-enclosure theorems. The computational
tests also check the following exactness rules.

- `intersect` chooses the larger lower cut and the smaller upper cut. At equal
  endpoints it chooses open if either input is open.
- `hull` chooses the smaller lower cut and the larger upper cut. At equal
  endpoints it chooses closed if either input contains the endpoint.
- Negation swaps the ends and preserves their openness.
- A finite endpoint of a sum is closed exactly when both contributing
  endpoints are closed.
- Multiplication partitions both inputs by sign, enumerates finite corner and
  zero candidates, and tracks whether each extremum is attained. Zero is an
  attained extremum whenever either factor contains zero, not only when a
  factor is the singleton zero. For example,
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

These named arithmetic operations return tight cuts in their representable
dyadic result class, including exact endpoint attainment. Conservatively
closing a cut is permitted for an approximate registered propagator, not for
these primitives.

The image of reciprocal or division may be disconnected, and even `{3}⁻¹`
has a nondyadic endpoint. `invAt p` and `divAt p` return the tightest
single-interval enclosure on the `2^-p` dyadic grid for the complete image
under Lean's total inverse, including `0⁻¹ = 0`. Moved grid endpoints use the
strictness rule above. Thus a positive interval bounded away from zero has the
usual reversed reciprocal cuts rounded outward, `[0,1]⁻¹` has hull
`[0,+∞)`, and an interval containing both negative and positive values has
whole-interval hull. A rule can request a split at zero before using a tighter
sign-specific result. A later `IntervalSet` with at most two components is an
isolated extension, not a reason to complicate every initial operation.

Lean defines functions such as inverse and logarithm on inputs where a
numerical interval library might call them undefined. The computational
operation does not choose the mathematical convention. Each companion rule
must enclose Lean's actual function or require a proved domain cut before
using a tighter theorem.

### Outward regularization

`regularize p I` widens finite endpoints onto a grid with denominator at most
`2^p`. It rounds a lower endpoint down and an upper endpoint up. It never
replaces the strongest fact in the solver. Instead, it creates a cheaper view
that a later rule may use.

If an endpoint moves, the regularized cut is strict: a moved lower endpoint
is strictly below the old lower endpoint, and a moved upper endpoint is
strictly above the old upper endpoint. An unchanged endpoint inherits its old
strictness. This is the strongest sound outward view and makes regularization
idempotent without throwing away useful strict inequalities.

This distinction matters. Exact dyadic numerators can still grow rapidly.
Discarding a strong fact to shorten it would make the state order-dependent.
Keeping both the strong fact and a regularized working view lets the policy
trade precision against arithmetic cost without losing information.

The backend-comparison milestone also builds a separate exact-rational search
prototype. Its regularizer uses continued-fraction convergents or
semiconvergents to find low-height outward bounds under a denominator budget.
It is not silently substituted for `Fact.value : Dyadic`: retained proof
traces are projected to dyadic cuts, and adopting rational working facts would
require an explicit representation revision. The dyadic backend remains the
specified default because its bit-height contract and kernel certificates are
simpler. The comparison records total search, proof construction, and replay
cost. A small arithmetic microbenchmark alone is not enough to settle the
public representation.

## Shared expression program

The frontend reifies terms into a typed static single-assignment program. Each
instruction refers only to earlier instruction identifiers. Common
subexpression elimination occurs before search, so the array is also a compact
encoding of an expression DAG.

Conceptually:

```lean
structure Node where
  domain : DomainId
  op     : OpId
  args   : Array NodeId

structure Program where
  operations : Array OpKey
  nodes     : Array Node
  consumers : Array (Array NodeId)
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

## Rule protocol

Rules are explicit registrations, not typeclass instances. Typeclass search
must not recursively decide which algorithm computes an expression's bound.
The registry may contain several rules for one head symbol, and the policy may
try or combine all of them.

A structural, form-directed rule search similar to `apply_rules` remains a
benchmark alternative because it has worked well in other proof assistants
and may compose local order lemmas cheaply. The specified implementation keeps
an explicit registry and incremental scheduler so it can share facts, retain
state, and compare multiple methods. The benchmark compares these search
styles rather than assuming the registry wins every structural goal.

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

### Action kinds

The protocol distinguishes the following actions.

- `forward`: compute an enclosure of a node from current argument intervals.
- `backward`: use the node's current interval and all but one argument to
  contract an argument interval.
- `improve`: rerun a rule at greater effort, use a tighter enclosure method, or
  subdivide only the rule's input range and take the hull of the pieces.
- `rewrite`: activate a proved alternate expression and equality edge that the
  frontend materialized before search.
- `regularize`: create bounded-height working views without deleting stronger
  facts.
- `split`: create proof branches by adding complementary cuts for one node.

`improve` and `split` are intentionally distinct. Local subdivision inside one
propagator can tighten the range of a function without duplicating the whole
proof state. A solver split is needed when a dependency between several nodes
requires different assumptions in different cases.

An `Outcome` may be `noChange`, `inapplicable`, or `failed` without affecting
soundness. Rules do not promise that greater effort always gives a tighter
answer. The solver intersects every result with existing facts, measures the
actual improvement, and learns from that observation.

The initial `Program` is static after validation. Generic alternate forms are
present before search, and `rewrite` only changes which existing form is
scheduled. Adaptive range reduction or a Taylor polynomial may remain inside
a rule-specific payload and return a fact about the existing node. It does not
append unchecked instructions. A later append-only program extension would
need its own validation, dependency-update, and branch-storage design.

### Stateful rules

A cache key includes the rule, node, input fact versions, and effort. A rule
may retain:

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

The default state uses a versioned priority queue. Changed facts insert or
invalidate only affected candidates; stale entries are discarded lazily when
popped. Policies intended for diagnostics may use a simpler complete scan,
but their complexity is reported honestly.

The initial named policies are:

- `balancedV1`: the deterministic default described below;
- `propagateV1`: propagation and effort increases, with solver splits disabled;
- `bisectV1`: a diagnostic midpoint policy after cheap saturation;
- `replay`: follows an explicitly supplied action plan for regression tests.

Versioned names let a downstream proof script pin search behavior while the
default alias can improve. A pinned policy is not a soundness requirement. It
is only a reproducibility aid.

### The default policy

`balancedV1` uses four stages.

1. Drain cheap forward and backward actions whose inputs changed.
2. Run untried applicable enclosure methods with their initial effort.
3. Compare targeted effort increases, rewrites, local range refinement, and
   contractor probes.
4. If no candidate has adequate predicted gain, choose a solver split and
   repeat in both children.

The policy computes a goal-directed potential rather than summing raw widths.
Nodes on the backwards dependency slice from the desired comparison or current
contradiction receive greater weight. A node's uncertainty records:

- how many ends remain unbounded;
- a capped base-2 width for a bounded interval;
- whether a strict cut would close the goal where a non-strict cut does not;
- endpoint bit length;
- estimated proof cost;
- distance in the program from a fact that can close the branch.

The exact coefficients are policy-tuning benchmark data, not mathematical
constants. They live in `PolicyConfig` and are reported by tracing. Scores use
bounded integer fixed-point arithmetic with specified saturation, never
`Float`. `balancedV1` has a
total tie-break over action stage and kind, `NodeId`, versioned `RuleKey`,
input fact versions, effort, and dyadic split point. Candidate maps are
traversed in sorted order, so hash-table iteration and fresh environment
identifiers cannot affect a step-budgeted result.

For an action that has run before, its score is the observed reduction in
weighted potential divided by declared work plus estimated proof cost. An
untried action receives an optimism bonus. Repeated `noChange` results decay
the score unless an input version or effort changes. A fixed quota selects the
oldest still-valid action in the highest nonempty fairness tier instead of the
best score. Consequently, with an unbounded step budget and only finitely many
new insertions, every continuously eligible action is eventually sampled. A
finite configured budget makes no such promise.

The original sensitivity proposal is recovered as a simple special case: if
`m` is the global uncertainty measure and an action changes it to `m'`, the
action's measured sensitivity is a monotone function of `m - m'` or `m / m'`.
The implementation uses a difference on capped logarithmic widths so
unbounded values and zero width do not require exceptional arithmetic.

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
suggestion names a dyadic point and a reason. The default order is:

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

- reified program nodes and alternate forms per original node;
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
exponent. A separate alignment-shift limit caps the exponent difference used
by comparison and arithmetic. This reflects the actual shifted-integer work;
an exponent of magnitude `2^30` is not treated as a 31-bit endpoint. An
oversized new candidate is not installed. The rule may instead
return a separately justified outward-regularized candidate within budget.
Existing stronger facts are never deleted to satisfy the limit, and an
oversized result is reported distinctly from `noChange`.

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
facts actually used.

```lean
structure FactId where
  scope : ScopeId
  index : Nat

inductive Derivation
  | source     (source : SourceId)
  | rule       (rule : RuleKey) (inputs : Array FactId) (payload : PayloadId)
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
- Fact comparison and contradiction checks use exact dyadic comparison. Their
  integer cost is proportional to effective endpoint height and the permitted
  exponent-alignment shift.
- Branch facts use an explicitly persistent paged trie, not Lean `Array`
  copy-on-write. Creating a child shares the root in `O(1)`; updating a fact
  copies one trie path and one fixed-size page in `O(log n)` time.
- Default-policy candidate insertion, invalidation, and heap selection are
  `O(log q)` amortized, excluding the declared cost of rescoring a stale
  candidate. A diagnostic policy that scans candidates reports `O(q)`.
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
- intersection and hull at equal open and closed cuts;
- split coverage at an endpoint and an interior point;
- negation and addition closure propagation;
- multiplication by singleton zero, by a nonsingleton interval containing
  zero, and by unbounded intervals, with exact endpoint-attainment flags;
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
- persistent paged-trie branch creation and updates over program size;
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
