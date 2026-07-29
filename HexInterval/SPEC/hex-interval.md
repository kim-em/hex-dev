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

The authoritative references are the action substitution and old nodes named
explicitly as existing inputs by proposed drafts or equalities. A proposed node
remains an output of the theorem instance when it CSE-hits an already
materialized node: storage reuse cannot manufacture a proof dependency. Thus
the same append-stable proposal has the same logical generation before and
after an unrelated CSE-producing extension.

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

One atomic theorem instantiation initially assigns a single instantiation
generation to all helper nodes it introduces: one plus the maximum generation
of every node in the authoritative action substitution or explicitly named as
an existing input by a draft or equality. Proposed products are outputs, even
when CSE reuses their storage, so selection order cannot raise their logical
generation or change success at an exact generation cap. This measures
theorem-instantiation depth rather than expression-tree depth. Per-product or
multiple-provenance generation remains a possible refinement.

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

This first format API validates representation shape only. It does not attest
that a body proves the proposed interval fact, instance, or equality. The
Mathlib companion must dispatch on the same immutable key, decode the frozen
entry independently of package cache state, and recheck the corresponding
rule theorem during semantic replay. Until that companion layer exists, it is
an explicit compatibility obligation—not a property enforced by this format
API—that a different callback implementation under an existing versioned rule
schema leave every retained payload semantically replayable. Whether production
retains these existential snapshots, compiles a dispatch table, adds typed
decoders, supports hot replacement, or uses another lookup structure remains
experimental. The older direct registry and engine interfaces remain available
for search experiments, but proof-producing execution goes through the
session.

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
cache; handlers in different packages may use unrelated types. This first
scope-free run has one registry cache for the whole run. Before branching is
implemented, production must choose branch ownership or explicit
`ScopeId`/semantic cache keys and test cross-branch reuse separately.

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

A registration whose matcher depends on the whole `ProgramView` sets
`watchesProgram`. Every append-only extension then stales its old action and
requeues all existing applications of that registration. This coarse trigger
is the first grind-like instantiation mechanism: a matcher that was previously
inapplicable can observe expressions introduced by another package. Ordinary
anchor-local registrations remain append-stable; they do not acquire a global
dependency merely because engine-owned admission may CSE one of their outputs.
Compiled structural patterns or more selective operation-key triggers remain
alternatives to compare once the behavior is established.

1. The solver produces an `Action` naming a program snapshot, concrete rule
   application, anchor, declared input fact versions, effort, and action kind.
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
lookup checks the expected role. Failure returns the old arena.
Both private sessions commit that returned arena only if submission of the
relocated outcome also succeeds. Before freezing, they check the candidate and
suggestion list lengths against the engine's own trusted limits. Let
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
does not do so. Malformed package evidence and
package-local payload-use, draft-count, draft-cell, atom, or schema excess are
different: the prospective arena is discarded, but the session submits a
bounded synthetic `failed` outcome through the ordinary engine reply path.
This clears the request latch, retains non-semantic cache telemetry, leaves
facts and history unchanged, keeps the session live, and records that required
work was dropped. The FIFO driver may therefore continue other independent
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
dropped from the engine's bounded retained prefix, or tombstoned by a failed
freshness guard. `Suggestion.affectsClosure` is the single classification used
for all three paths, while `Engine.keptSuggestions` and
`Engine.droppedSuggestions` define the exact shared retention boundary.
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
  `267/242`, while both arms already share `112` clock synchronizations and
  `14` suggestion-pruning visits;
- four roots densely waking five sinks records all `20` watcher visits—five
  insertions and fifteen suppressed duplicates—and gives `277/250`;
- five sinks each emitting three disposable split suggestions gives
  `1267/754`; the scan inspects `424` historical backing slots, while the
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

The concrete package canary reaches step 6 in both search-only and
proof-producing modes. One deterministic schedule selects subtraction and
multiplication propagation, the structure matcher, instantiation admission,
the centered function's split handler and forward propagator, equality
contraction, reciprocal propagation, a precision retry, and finally the
centered function's split suggestion. It adds the centered node at generation
one, narrows both representations to `[0,1/4]`, improves the enclosure of
`1/3` at effort one, and returns a prepared plan at `x = 1/2`. The
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
- [IntervalArithmetic.jl construction and exact input guidance](https://juliaintervals.github.io/IntervalArithmetic.jl/stable/manual/construction/).
- [Boost.Interval policies and representation](https://www.boost.org/doc/libs/latest/libs/numeric/interval/doc/interval.htm).
