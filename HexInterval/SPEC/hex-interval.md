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

The current supported Mathlib-free boundary includes checked typed SSA
`Program`s; versioned fact snapshots and projected views; stable
operation/rule keys; registrations and explicit scope bindings; immutable
actions and package requests; and checked immutable branch, dependency,
work-queue, chronology, and bounded diagnostic snapshots. These records
deliberately contain neither function callbacks nor proof evidence. The state
records are a stable decoded interchange and validation contract; they do not
select the eventual mutable, persistent, paged, or trail-backed implementation
used inside a high-performance branch search. The supported boundary also
includes generic bounded policy offers/views, exact echoed decisions, a
replaceable choice interface, package-measured byte/pair/work caps, and
transactional revalidation against exact program, fact snapshot, scope,
serial, program version, remaining budget, and complete offer fields. It does
not choose a semantic offer-key encoding or a default policy. The supported
Mathlib companion now also owns the function-agnostic program interpretation,
package theorem registry, chronological proof fold, exact caller closure, and
checked expression boundary. Its first programmatic frontend recursively
reifies a bounded arithmetic term language by stable operation key, rechecks
the transparent result's exact node/term correspondence, places exact caller
facts at source rows and `whole` at computed version-zero rows, derives all
initial containments from only the source obligations, and replays a
caller-supplied authenticated flat
chronology, and projects
the result to lower, upper, conjunction, or closed-singleton equality theorems.
Its depth cap rejects over-deep descent but does not bound construction or a
full traversal of an already-built branching term. The supported direct
forward tactic client below parses its bounded Lean-expression and integer-cut
subset, authenticates the exact flat runtime chronology as untrusted data, and
independently synthesizes caller proofs. Its fixed public-tactic precision `16`
uses the dyadic grid `2⁻¹⁶`; programmatic clients may choose another precision
within the explicit envelope. Because each computed arithmetic layer is
followed by an internal regularization layer, its term-depth cap `32` admits
about 16 nested arithmetic operations along one expression spine. Generic
search-selected recipes and broader local-context parsing remain experimental.
The supported proof companion can separately consume a checked retained
`Search.Result.Tree` plus caller-supplied proof chronology: its registry
authenticates package-owned binary cover and refutation schemas, its checked
state rebases inherited child facts without promoting them to assumptions, and
its bounded recursive fold closes target/refutation leaves, rejects unknown
leaves, and joins siblings only through the exact cover. Producing that proof
recipe from generic search callbacks and invoking the fold from the public
tactic remain later controller work. The first
concrete supported registry is the Mathlib arithmetic package for one
configured constant and natural exponent plus public negation, addition,
subtraction, multiplication, power, absolute-value, min/max, reciprocal,
division, and regularization operations. Arbitrary-function package assembly,
callback outcomes and proposals, concrete policy algorithms and default
scheduling, the branch-search controller, callback-to-recipe orchestration,
payload storage, and the optimized backing store remain experimental.
Supported authenticated sessions and the narrow direct-forward tactic do not
yet supply that missing controller bridge.
In particular, the current instantiation proposal's package-supplied numeric
policy family is not part of the supported action contract.

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

The semantic shape is intentionally small. The D2 measurement selected a
sealed public value carrying canonical raw cuts and their consistency proof;
the observable distinctions below are part of the contract. `Dyadic` means
Lean core's `Init.Data.Dyadic` type. The rounding precision used by the initial
dyadic backend is signed `Int`, as in core; negative values are needed for
coarse grids at large magnitudes.

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

`Raw` avoids shadowing Lean's `Repr` typeclass. The public `Hex.Interval` is a
sealed API with a canonical `view`, smart constructors, and normalization. Its
constructor and consistency proof are private. Two internal candidates were
compared during the vertical feasibility prototype:

1. a structure bundling `raw : Raw` with a proof of `raw.CutConsistent`;
2. plain data whose `Bool`-valued consistency and normalization are checked at
   construction or replay boundaries, without carrying a proof in every hot
   value.

The refreshed five-sample comparison at repository commit `9c87f7cf2` and Lean
`v4.33.0-rc1` records both 433-value and 4096-value workloads in
`reports/bench-results/hex-interval-d2-representation.json`. The checked hot
loop is within two percent of the bundled loop, while revalidating the checked
arena at the boundary costs about twelve percent relative to using the bundled
invariant. Generated C and object sizes are identical because the proof field
erases. Kernel replay and WHNF timings favor different candidates and are noisy
after import-baseline subtraction; they do not justify moving validation into
every trust boundary. The public value therefore uses the bundled invariant.
Internal planners and certificates may still use plain data when their own
checked boundary authenticates it; proof traces do not inherit the public
value's proof field.

The initial supported slice exposes `view`, `empty`, `whole`, and endpoint-cost
preflighted raw, singleton, one-sided, and finite constructors. The first
supported operations are resource-checked intersection, hull, negation,
addition, subtraction, multiplication, minimum, maximum, absolute value,
natural power, outward regularization, and transactional splitting at a dyadic
point.
Their Mathlib companion proves exact computed-cut semantics and image theorems;
the remaining arithmetic is promoted separately rather than being declared
public merely because narrower experiment implementations exist. All public
examples use the fully qualified `Hex.Interval`, because Mathlib also has a
root `Interval` type; the public namespace is itself revisitable before release
if qualification proves awkward. Unless a block explicitly says otherwise,
unqualified API sketches below are declarations inside `Hex.Interval`.

The public Mathlib companion interprets every canonical interval as a subset
of `ℝ`. It proves that a successful executable `intersectWithin` denotes
logical conjunction for the complete cut language: strict and closed ends,
tied endpoints, empty results, and either end unbounded. It also proves that a
successful `hullWithin` has the exact selected-cut/interval-convex-closure
meaning and contains both inputs; this is deliberately not set union. A
successful `negWithin` contains `x` exactly when the input contains `-x`.
Successful `addWithin` exposes the exact independently summed lower and upper
Minkowski cuts, and its image theorem maps any two input members to their sum.
Successful `subWithin` similarly exposes the crossed left-lower-minus-right-upper
and left-upper-minus-right-lower cuts, and maps two input members to their
difference. Successful `minWithin` and `maxWithin` expose their exact selected
cut predicates and enclose the pointwise real minimum and maximum of any two
input members. They do not claim the converse characterization of every result
member as a pointwise image. Successful `absWithin` exposes its exact normalized
selected-cut predicate and maps every input member `x` to `|x|`; it likewise
does not claim a converse characterization of every result member as an
absolute-value image. Successful `powWithin` exposes its exact normalized
direct cuts for exponent zero, positive odd powers, and positive even powers,
and maps every input member to its real natural power. It likewise makes no
set-image converse claim. Successful `regularizeWithin` exposes the exact
normalized Core-rounded cuts and contains every member of its source. Repeating
the raw cut transform at the same precision is idempotent; no global
grid-tightest claim is made. Neither addition nor subtraction currently claims the
separate representation-independent tightness converse for the real Minkowski
image.
Separately, the experiment form of the intersection theorem is installed as the
generic `FactDomainSchema.proveMeet` boundary, and the transparent proof
frontend uses it to close a weaker requested interval from a stronger
established one. The supported theorem is independent of that experiment
package.

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

The supported first operation slice is:

```lean
def intersectWithin : EndpointLimit → Interval → Interval → BuildResult
def hullWithin      : EndpointLimit → Interval → Interval → BuildResult
def negWithin       : EndpointLimit → Interval → BuildResult
def addWithin       : EndpointLimit → Interval → Interval → BuildResult
def subWithin       : EndpointLimit → Interval → Interval → BuildResult
def minWithin       : EndpointLimit → Interval → Interval → BuildResult
def maxWithin       : EndpointLimit → Interval → Interval → BuildResult
def absWithin       : EndpointLimit → Interval → BuildResult
def mulWithin       : EndpointLimit → Interval → Interval → Arithmetic.Result
def powWithin       : EndpointLimit → Arithmetic.PowLimits → Interval → Nat →
  Arithmetic.Result
def regularizeWithin : Arithmetic.PrecisionLimits → Precision → Interval →
  Arithmetic.Result
def splitWithin     : EndpointLimit → Interval → Dyadic → SplitResult
```

`SplitResult.ready left right` carries both children together;
`SplitResult.resourceLimit cost` carries neither. This dedicated result keeps
refusal distinct from both canonical empty children and makes a partial pair
unrepresentable.

These names retain the budget because a public interval does not store the
limit under which it was constructed. Comparing endpoints admitted under two
different caller limits can otherwise allocate an exponent-alignment shift far
larger than either stored mantissa. A refused comparison returns
`BuildResult.resourceLimit`; it is never interpreted as an empty interval.
Negation still takes a limit because its finite output endpoints and final
canonical comparison cross the same public boundary. Addition cannot be the
previously sketched total `Interval → Interval → Interval`: core
`Dyadic.add` aligns finite mantissas by their exponent gap, so inputs admitted
under unrelated limits can request an arbitrarily large shift. `addWithin`
preflights both finite endpoint pairs before either addition. When endpoint
height is bounded by `H` and alignment by `S`, the temporary numerator is
bounded by the larger input numerator plus `S` and one carry bit. The summed
raw cuts then cross `ofRawWithin`, which separately checks retained endpoint
height and their final crossed comparison.

`subWithin` uses the same allocation argument on the crossed pairs: left lower
with right upper, then left upper with right lower. It is deliberately direct,
not `addWithin left` after `negWithin right`. The composed form would first
normalize an intermediate negated interval and could refuse its unrelated
right-endpoint comparison even when both crossed subtraction pairs fit. Direct
preflight therefore admits strictly more valid operations and performs no
dyadic negation or aligned subtraction until both crossed pairs are admitted;
the resulting raw cuts then cross `ofRawWithin` exactly once. The theorem
`Raw.sub_eq_add_neg` pins that the direct raw result still agrees with addition
after raw negation.

`minWithin` and `maxWithin` are also direct checked primitives, not compositions
through unchecked total interval APIs. Empty is absorbing. Both same-side
finite endpoint comparisons are preflighted before either selector executes.
Minimum selects the hull lower cut and intersection upper cut; maximum selects
the intersection lower cut and hull upper cut. The selected candidate then
crosses `ofRawWithin`, whose independent endpoint/final-comparison check may
still refuse even when both selector comparisons fit.

`absWithin` preserves empty and sign-separated endpoint strictness. An input
crossing zero has a closed zero lower cut and chooses the larger endpoint
magnitude for its upper cut; equal magnitudes are strict only when both source
endpoints are strict. The opposite-magnitude comparison is preflighted before
the selector aligns finite dyadics, and the selected raw cuts then cross
`ofRawWithin`. Thus an interval admitted under a larger earlier budget cannot
force an unchecked alignment or silently turn refusal into empty.

`splitWithin` is likewise direct and transactional. Empty short-circuits to
two empty children without inspecting the point. For a nonempty source it
first checks the retained point endpoint, then every finite source/point
selector comparison, before running an unchecked selector. It next preflights
the normalization cost of both raw candidates before constructing either
sealed child. Success returns the canonical intersections with `(-∞, point]`
and `(point, +∞)` together; any failed check returns one resource refusal and
no child.

Multiplication uses the separate checked-arithmetic result because growth
refusal is distinct from both empty output and endpoint/comparison refusal.
`Arithmetic.Growth`
records admitted source endpoint costs and a conservative predicted result.
Multiplication records the sum of input numerator-bit lengths and the exact
magnitude of the signed exponent sum. `Arithmetic.preflightMul` checks both
inputs before forming that small signed exponent sum and never multiplies their
mantissas. For example, under endpoint height `8`, the endpoints `255` and
`255` and their comparison are admitted, while their predicted sixteen-bit
product numerator is refused before multiplication.

`Arithmetic.preflightPowGrowth` applies the same boundary to a direct natural
power with one source. It predicts the exact magnitude of the dyadic exponent
and a conservative mantissa-bit count without raising the mantissa. Numerators
of
absolute value one retain their exact one-bit cost, so large powers of `1`,
`-1`, and unit-mantissa powers of two do not incur fictitious mantissa growth;
powers of two are still charged their exact signed exponent magnitude. The
metadata uses arbitrary-precision `Nat` arithmetic rather than fixed-width
counters. Under endpoint height `8`, `3^4` is admitted by its eight-bit bound,
while `3^5` is refused from its ten-bit bound before `Dyadic.pow` allocates the
result. A quarter cubed is admitted with exponent magnitude six, while its
fourth power is refused because one numerator bit plus exponent magnitude
eight exceeds the retained-height budget.

On its own, this preflight bounds retained endpoint growth only. It does not bound the
execution work of `Nat.pow` or the conversion of the natural exponent used in
Core's signed dyadic-exponent multiplication, and therefore is not the complete
resource gate used by public interval power. In particular, when the dyadic
exponent is zero and the mantissa has absolute value one, arbitrarily large
natural exponents pass the endpoint-growth check. `powWithin` therefore adds
and enforces a separate exponent/work cap before invoking `Dyadic.pow`.

`Arithmetic.PowLimits` supplies that smallest execution-work prerequisite.
Its `maxExponent` bounds the actual arbitrary-precision `Nat` value, not the
number of bits used to encode it. `Arithmetic.preflightPow` checks this cap
for every nonzero dyadic before composing transactionally with
`preflightPowGrowth`; a work refusal is `Arithmetic.Cost.power`, never a
fabricated endpoint or growth diagnostic. A successful composite check
guarantees that `powWithin` reaches Core's nonzero power only with a bounded
source, bounded retained-result growth, and `exponent ≤ maxExponent`.

Zero alone bypasses the work cap. Core's zero branch only distinguishes `0^0`
from a positive power and returns `1` or `0`; it does not invoke `Nat.pow`,
convert the exponent to `Int`, or form the signed dyadic-exponent product.
This exemption does not extend to `1` or `-1`, whose Core path still processes
the natural exponent. The scalar cap is sufficient to bound that Core path
when combined with the existing endpoint/growth limits, but it is not a
wall-clock estimate and does not charge work already spent constructing,
parsing, or reifying the input `Nat`.

`powWithin` is the direct checked hull, rather than repeated interval
multiplication. Empty is absorbing at every exponent. A nonempty input at
exponent zero becomes the closed singleton `{1}` without evaluating an
endpoint power. A positive odd exponent maps the two source cuts directly. A
positive even exponent first computes the exact absolute-value hull, so a
negative interval reverses magnitude order and a mixed interval gets a closed
zero exactly when zero belongs to the source; it then maps the nonnegative
cuts with their selected attainment flags.

Before any Core power evaluation, every selected finite endpoint passes
`preflightPow`. The even mixed-sign magnitude comparison passes the same
exact comparison preflight used by `absWithin` before selection. Both selected
endpoint prerequisites are checked before either power is evaluated, and the
resulting raw cuts finally cross `ofRawWithin` for endpoint retention and
canonical-order comparison. A refusal at any stage is an
`Arithmetic.Result.resourceLimit`, not empty. The public view theorem exposes
exactly the normalized `Raw.powUnchecked` cuts; the Mathlib companion proves
that every input member maps to its real natural power. It does not claim the
set-image converse.

`Arithmetic.Cost.growth` keeps these refusals distinct from endpoint and exact
comparison costs, and `Arithmetic.Result` is a separate checked-arithmetic
result so the existing `BuildResult` APIs above do not acquire a misleading or
breaking cost variant.

`mulWithin` first admits every finite source endpoint before sign inspection.
It then
admits all four finite corner products through `Arithmetic.preflightMul`
before multiplying any mantissas, admits every evaluated finite candidate as
an endpoint, and only then admits all candidate alignment comparisons before
extremum selection. Source height refusal is observably `Cost.endpoint`,
predicted product growth is `Cost.growth`, and candidate alignment refusal is
`Cost.comparison`. Candidate-height admission is a defensive invariant check,
not a currently reachable first refusal: every finite corner is bounded by its
already admitted growth prediction, and the only additional candidate is zero.
The explicit stage ensures a future candidate source cannot bypass endpoint
admission. The exact raw candidate enumerates the four
extended-endpoint products, omitting the undefined formal products
`0 * ±∞`; an attained zero candidate is added exactly when either nonempty
factor contains zero. Tied corner values combine attainment, so open and
closed extrema, zero attainment, independent unbounded sides, and empty
absorption are preserved. A successful result has an explicit selected lower-
and upper-cut characterization after normalization, and the Mathlib companion proves that every
product of source members belongs to it. No separate image-tightness converse
is currently claimed.

The public tree also contains the allocation prerequisite for
precision-indexed reciprocal and division. It exposes the checked operations

```lean
invWithin (limits : Arithmetic.PrecisionLimits) (precision : Precision)
  (input : Hex.Interval) : Arithmetic.Result

divWithin (limits : Arithmetic.PrecisionLimits) (precision : Precision)
  (numerator denominator : Hex.Interval) : Arithmetic.Result
```

Core `Dyadic.invAtPrec` converts a nonzero source through
`Dyadic.toRat`, inverts the rational, then calls `Rat.toDyadic`; `divAtPrec`
converts both sources and additionally runs reduced rational cross-products.
Neither `CompareCost` nor `Arithmetic.Growth` accounts for those shifts or
temporary numerators and denominators. `Arithmetic.PrecisionLimits` therefore
retains the existing endpoint-height and aggregate-shift policy while adding
separate precision-magnitude, encoded-precision, and rational-temporary bit
limits. Its embedded `EndpointLimit.maxAlignmentShift` is deliberately reused
as the cap on the sum of all source-conversion shift magnitudes plus the
precision-shift magnitude: this is an aggregate allocation-work budget, not a
claim that those signed shifts are one comparison alignment or may cancel.
`Arithmetic.Cost.precision` refuses an oversized request before any
source conversion or source-exponent/precision sum. After admitted precision,
`Arithmetic.QuotientCost` records exact source conversion shapes, the sum of
source exponent magnitudes and precision magnitude without signed
cancellation, an explicit division cross-product bound, the `toDyadic` shift,
and a conservative retained result-height bound. For positive precision the
precision magnitude can occur once in the shifted quotient-bit bound and again
in the canonical endpoint-height bound. This intentional doubled allowance
avoids assuming how many trailing zeroes `Dyadic.ofIntWithPrec` will remove;
zero quotients remain exactly zero-sized.

`preflightInv` and `preflightDiv` construct only this metadata; they
do not call the Core arithmetic. The reciprocal zero and division-by-zero
paths record Core's no-conversion short circuit, although division first admits
both retained public sources; their `QuotientPlan.zero` records those admitted
source costs rather than discarding preflight provenance. The result-height
bound deliberately allows one
extra quotient-magnitude bit for negative floor rounding and does not use the
denominator to claim cancellation. Conformance accepts positive and negative
`{3}` prerequisites and separately exercises precision encoding, zero
numerators, admitted zero-path sources, failure priority, converted and
cross-product temporaries, quotient size, non-cancelling conversion shifts,
and predicted retained result.

`invWithin` admits every finite source cut before classifying it relative to
zero, then preflights both required nonzero endpoint reciprocals before either
Core call. The operation invokes `Arithmetic.preflightInv` internally for each
endpoint it will evaluate and accepts no caller-supplied `QuotientPlan`. Its
lower endpoint is `invAtPrec upper precision`; its upper endpoint is
`-invAtPrec (-lower) precision`. Thus both directions reuse Core's downward
rounding, while the second is upward rounding after sign reflection. Every
moved finite result cut is conservatively closed: the operation proves outward
enclosure, not endpoint attainment or grid optimality. Every input not
separated from zero bypasses precision work; this includes empty, singleton
zero, one-sided-zero, and sign-crossing inputs. Open zero maps to the
corresponding unbounded one-sided limit and is never passed to Core.

Following Lean's total inverse, a closed zero contributes `0⁻¹ = 0`:
`[0,b]` has connected hull `[0,+∞)`, `[a,0]` has hull `(-∞,0]`, singleton
zero stays singleton zero, and a two-sign interval returns the whole line.
Unbounded sign-separated inputs retain a strict zero limit on the output side.
This is the connected-hull policy expressible by one `Hex.Interval`, not a
disconnected interval-set representation.

`view_invWithin_ready` exactly characterizes every successful computed cut;
the Mathlib companion independently proves that every real source member's
Lean-total inverse lies in that result. No converse image theorem, finite-cut
attainment, grid optimality, or disconnected-image tightness is claimed.

`divWithin` is a deliberately narrow first supported slice. Empty is
absorbing. A singleton-zero numerator or denominator returns singleton zero,
following Lean's total division. Two nonzero finite singletons call Core's
`divAtPrec numerator denominator precision` directly for the lower endpoint
and `-divAtPrec (-numerator) denominator precision` for the upper endpoint.
The operation internally rederives both `preflightDiv` plans, and both must
pass before either Core call executes; it accepts no caller plan and allocates
no intermediate reciprocal. Every other nonempty pair returns the whole
interval without precision work. This explicitly includes nonsingleton,
unbounded, zero-touching, and sign-crossing shapes.

Every finite cut in both nonempty sources is admitted before that
classification. After the selected Core cuts are computed, they still cross
`ofRawWithin`; its independent final endpoint-retention and comparison checks
may refuse the result.

`view_divWithin_ready` exactly characterizes those computed cuts, and the
Mathlib companion consumes both source memberships to prove a one-way theorem
for Lean's total real division. No converse image theorem, rounded-cut
attainment, grid optimality, useful bounded nonsingleton quotient, or
disconnected-result precision is claimed.

The same `PrecisionLimits` also supports public outward regularization, but a
rational-quotient cost would be fictitious for Core `roundDown` / `roundUp`.
`Arithmetic.RegularizeCost` instead records each nonzero finite source, a
non-cancelling bound for the exponent/precision subtraction, the shifted
integer temporary, conservative canonical result height, and a final two-cut
alignment bound. `preflightRegularize` admits all finite sources before the
precision and every rounding bound before either Core operation executes.
A shape with no nonzero finite endpoint performs no nontrivial rounding work
and does not inspect the requested precision. `regularizeWithin` then rounds
lower cuts down and upper cuts up and seals the resulting pair. A moved
endpoint is strict because it lies strictly outside the old cut; an unchanged
endpoint inherits its source strictness. Refusal remains an
`Arithmetic.Result.resourceLimit`, with the dedicated `Cost.regularization`
diagnostic rather than a fabricated quotient or comparison.

The public raw intersection and hull cut selectors, `intersectUnchecked`,
`hullUnchecked`, `negUnchecked`, `addUnchecked`, `subUnchecked`, `minUnchecked`,
`maxUnchecked`, `absUnchecked`, `powCutsUnchecked`, `powUnchecked`, and
`mulUnchecked`, together with `splitUnchecked`, `invUnchecked`,
`singletonValue?`, `divUnchecked`, and `regularizeUnchecked`, are related to
the checked operations by successful-result and semantic theorems.
`powCutsUnchecked` is
only the strictly monotone cut mapper;
its caller must establish the positive odd or nonnegative positive-exponent
case. `powUnchecked` performs the zero/odd/even direct-hull selection. Like
`Raw.normalizeUnchecked`, they
are decoder-level combinators: untrusted callers use the checked `Interval`
operations above.

The remaining target surface includes useful bounded nonsingleton division and
other arithmetic images. Their public signatures and resource policies are
fixed only after the corresponding allocation audits; no operation may
silently align, compare, or enlarge arbitrary-precision endpoints.

For the initial dyadic backend, `Precision` is an alias for signed `Int` and
the implementation reuses core `Dyadic.roundDown`, `roundUp`, `invAtPrec`, and
`divAtPrec` rather than reimplementing directed rounding.

The Mathlib companion proves their set-enclosure theorems. The computational
tests also check the following exactness rules.

- `intersectWithin` chooses the larger lower cut and the smaller upper cut. At equal
  endpoints it chooses open if either input is open.
- `hullWithin` chooses the smaller lower cut and the larger upper cut. At equal
  endpoints it chooses closed if either input contains the endpoint.
- `negWithin` swaps the ends and preserves their openness.
- `addWithin` absorbs empty, adds corresponding finite endpoints, and retains
  an unbounded side if either corresponding input side is unbounded. A finite
  endpoint of a sum is closed exactly when both contributing endpoints are
  closed.
- `subWithin` absorbs empty and uses crossed endpoints: the lower cut is left
  lower minus right upper, and the upper cut is left upper minus right lower.
  Either corresponding unbounded contributor makes that result side
  unbounded; a finite side is closed exactly when both contributors are
  closed.
- `minWithin` absorbs empty, chooses the smaller lower cut and the smaller upper
  cut, and uses hull attainment on the lower tie but intersection attainment on
  the upper tie. Thus a tied lower endpoint is closed if either input attains it,
  while a tied upper endpoint is closed only if both inputs attain it.
- `maxWithin` absorbs empty, chooses the larger lower cut and the larger upper
  cut, and uses intersection attainment on the lower tie but hull attainment on
  the upper tie. Thus a tied lower endpoint is closed only if both inputs attain
  it, while a tied upper endpoint is closed if either input attains it.
- After the empty-input short circuit, multiplication unconditionally
  enumerates the four extended-endpoint corners plus a justified zero
  candidate; sign inspection only resolves finite-by-infinite corners. It
  tracks whether each extremum is attained. Zero is an attained extremum whenever either
  nonempty factor contains zero, not only when a factor is the singleton zero.
  For example,
  `[0,1] * (0,1] = [0,1]`, while `(0,1] * (0,1] = (0,1]`.
- A power distinguishes zero, odd powers, and positive even powers. It does
  not implement powers by repeated interval multiplication when a direct hull
  is tighter.
- `abs` uses the same candidate-and-attainment discipline. In particular, it
  contains a closed zero exactly when the input contains zero, and a tied
  magnitude extremum combines both contributing closure witnesses rather than
  copying one endpoint flag.
- `splitWithin limit I m` returns `I ∩ (-∞,m]` and `I ∩ (m,+∞)` together.
  The left child owns `m` exactly when `I` does, the right child never owns
  `m`, and the children are disjoint and cover `I`.
- Empty is canonical. Unary image operations and regularization preserve empty;
  binary image and intersection operations absorb an empty argument; and
  `splitWithin limit empty m = SplitResult.ready empty empty` without charging
  the point. Hull instead has empty as a two-sided identity.
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

The supported `invWithin` implements the connected-hull and outward-direction
part of this target, but conservatively closes every computed finite cut. It
therefore does not yet claim the moved-cut attainment rule or grid-optimality.
The older `Experiment.DyadicInterval.reciprocal` still returns
`inapplicable` for singleton zero, a closed zero endpoint, or a sign-crossing
input; it implements only the sign-separated cases (including an open zero
endpoint mapping to an unbounded side). The concrete package has an executable
across-zero regression for that legacy behavior and is not the public
operation. Selecting an interval-set result remains a possible future
precision improvement rather than a requirement for sound connected-hull use.

The supported `divWithin` implements only the direct two-finite-singleton grid
enclosure plus exact empty and total-zero cases. Its whole-line fallback makes
all remaining shapes sound but does not satisfy the eventual bounded quotient
or grid-tightness target. In particular, a whole fallback is a deliberate
first-slice loss of precision, not a claim that the exact image is the whole
line.

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

`regularizeWithin limits p I` widens finite endpoints onto the grid
`2^-p · ℤ`. It rounds a lower endpoint down and an upper endpoint up. It never
replaces the strongest fact in the solver. Instead, it creates a coarser
outward view that a later rule may use. This is not necessarily cheaper to
store: coarse negative precision can raise retained endpoint height, and that
predicted result growth is preflighted before rounding.

If an endpoint moves, the regularized cut is strict: a moved lower endpoint
is strictly below the old lower endpoint, and a moved upper endpoint is
strictly above the old upper endpoint. An unchanged endpoint inherits its old
strictness. This is the candidate strongest sound outward view and makes
regularization idempotent without throwing away useful strict inequalities;
Core's one-sided rounding inequalities prove containment and its precision and
fixed-point lemmas prove raw-cut idempotence. The missing converse optimality
lemmas still prevent a global grid-tightest theorem.

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

The supported request contract gives each action a bounded, immutable
`ProgramView` containing the exact program version, operation table,
SSA node table, per-node theorem-instantiation generations, and per-node
structural expression depths. It contains no facts.
`ProgramView.check` validates the decoded SSA program and exact alignment of
the generation/depth side tables; the experimental engine constructs it only
from a validated state already covered by the
operation, node, arity, generation, and structural-depth limits. Thus an
external shape rule can follow a product argument to a nested difference,
compare opaque operation keys, recover the repeated `NodeId`, and construct a
proposal without duplicating either engine-owned depth calculation. It still
receives facts only for its registration's declared watch slots. Structural
inspection does not become a hidden fact dependency.
The current package-boundary dispatch deliberately runs this complete check
again through `RuleRequest.accepts` for every selected request. This is a
fail-closed structural authentication boundary, not a hot-path complexity
claim: it scans the whole program and reconstructs its depth array before the
package callback runs.
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

### Supported state and trace snapshots

`State.Branch Fact Cause` is the function-independent decoded branch contract.
It retains the exact base program and caller facts, current append-only
program, immutable version-zero seeds for the generated-node suffix, current
versions, structural generation/depth metadata, exact updates, and the
contradiction search flag. Base facts plus generated-node seeds and ordered
updates are authoritative: `Branch.snapshot` reconstructs current facts rather
than trusting an independently mutable fact cache. `Cause` is opaque data at
this layer. `Branch.check` reconstructs every current fact and version,
validates the base/program prefix and all aligned arrays, requires base-node
generations to be zero, and rejects an appended generation after the current
program version. Exact dependency-derived creation generation remains the
experimental engine transition's responsibility; the supported decoded table
does not independently authenticate that semantic relation. It does not
interpret a fact or provenance cause as evidence.

`Branch.startWithin`, `pushWithin`, and `extendWithin` are transactional.
Structural count/arity/depth/generation caps are checked before allocating
aligned arrays; fact-history capacity is checked before appending an update;
and a stale node/version, wrong program version, malformed current branch, or
non-prefix extension returns no replacement branch. Generated version-zero
facts are retained in the suffix seed array rather than reconstructed by a
later callback. This makes quotation independent of mutable package state.
The experimental engine separately caches current facts for scheduler speed;
that cache is runtime data and never replaces branch history during replay.
Checked branch mutation preflights both the decoded base and current program
sizes before `Branch.check` traverses either program. `restoredFacts?` checks
the base/suffix/current size relation before concatenating the two seed arrays.

`State.Dependencies` retains node-aligned watcher lists and separate dirty bits
for application and equality work. `State.Queue` is an append-only bounded work
log plus its FIFO cursor. A policy may consume work out of FIFO order through
`Queue.deactivate`, clearing that exact occurrence's live bit and leaving a
checked tombstone. A later wake appends a fresh live occurrence and cannot
resurrect the earlier tombstone; `Queue.pop` skips tombstones and clears exactly
the next live item. Initial queue construction preflights its retained count; queue
validation, enqueue, deactivation, and pop additionally receive the exact
program-node count and validate watcher/reference arrays, live bits, cursor,
and retained-count alignment before returning a new snapshot. The append-only
array is the current decoded/reference
representation, not a decision against a compacting or persistent production
queue with the same behavior.

`Trace.Order` is the authoritative interleaving of fact updates and program
instances. Its checked append operations require the exact next role-local
index and independent fact/instance history caps. The target-role index and
combined retained-count cap are preflighted before scanning chronology; after
that scan the exact role-local order and separate retained counts are checked.
The role-specific histories
retain payload and provenance; the order alone carries no proof authority.
`Trace.Log` is a separate diagnostic stream with exact event-count,
already-allocated payload-byte, declared-work, and code limits. Refusal marks
the diagnostic stream truncated without changing any branch or chronology.
Because byte admission occurs after an event exists, arbitrary callback and
Lean-object construction is explicitly non-preemptible and remains the
package's bounded responsibility.

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

inductive State.Work
  | application (application : ApplicationId)
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

`Registration.check` is supported and validates exact versioned heads,
duplicate-free keys, binding shapes, and local slot ranges against a checked
program. `ScopeBinding.check` validates ordered concrete ports and exact
anchor heads without interpreting a function. `RuleRequest.accepts` validates
the immutable program view plus the registration's exact stable key, action
kind, fact versions, and ordered read/write projection. Compact rule and
application identifiers, action serials, fact values, and pending-state
ownership can only be authenticated by the controller that issued the action;
these structural checks neither claim that authority nor create evidence.

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

The exact interval companion now exercises this boundary with an operation
whose real meaning is supplied entirely by its package:
`f(x) = 1/4 - (x - 1/2)^2`. The runtime registry sees only opaque operation and
rule keys. From the exact closed input interval `[0,1]`, the package's forward
contractor proposes `[0,1/4]`; a package-owned transparent schema proves that
proposal from the exact singleton input list, and the generic rule replayer
intersects it with the previous whole-line fact. No arithmetic rule or
function case is added to the engine or proof frontend. The live session's
one retained fact event is compared with the quoted action and arena entry,
and quoted replay produces the ordinary real theorem
`0 ≤ x → x ≤ 1 → 0 ≤ f(x) ∧ f(x) ≤ 1/4`. Replacing the quoted `[0,1]`
assumption by the whole line is rejected, so the function theorem's premise is
load-bearing rather than decorative. This is the minimal arbitrary-function
vertical against the exact interval domain.

A second, independently assembled package attaches a backward registration to
that same opaque operation without redefining it. From the exact output band
`f(x) ∈ [3/16,1/4]`, its runtime contractor narrows a whole-line input to
`[1/4,3/4]`; its own schema derives that inverse image from the centered
operation model. The live registry therefore contains two packages which own
different directions for one function, while both proof steps use the same
generic rule transition. The backward quote is rejected if its precise output
band is weakened to `[0,1/4]`, and its ordinary theorem confirms that the
watched output premise is load-bearing. Richer packages may add retries,
instantiators, and split suggestions without changing this interface.

The exact arithmetic package contributes its first replay schema through this
same boundary. This is package-callback replay over
`Experiment.DyadicInterval.Fact`, not a second supported interval-arithmetic
API; the public resource-checked operation remains `Hex.Interval.subWithin`.
The forward subtraction callback remains Mathlib-free and computes over the
complete experimental dyadic cut language; its companion schema recomputes the
successful proposal and proves the pointwise real subtraction law from the
exact ordered pair of input facts. The live conformance case uses
`x ∈ (1,+∞)` and `y ∈ (-∞,3]` to derive `x - y ∈ (-2,+∞)`, so both
strictness and independent unboundedness are load-bearing. The generic proof
emitter contains no arithmetic case. Weakening the left premise or adding a
trailing schema-zero payload cell is rejected, and the accepted quote yields
the ordinary theorem `1 < x → y ≤ 3 → -2 < x - y`. Further arithmetic
schemas extend this package-owned pattern without introducing a
rational-normalization dependency into propagation replay.

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
fact on an old node has the same meaning in old and new models whenever their
valuations agree on the complete old program. Whole-prefix agreement is
required because `Semantics.holds` may inspect values at old nodes other than
the node carrying the fact. This is separate from, and
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
prefix-stability theorem, caller program, a declared base-assumption list, and
a plain-data encoder; packages remain responsible for their replay schemas.
It seeds caller facts by checked position in that declared list, and the caller
hypotheses supplied to final closure discharge the same list. The reusable
frontend does not yet construct the `InitialContext` witness that relates the
declared list position-for-position to `CheckerInput.initialFacts`. The
complete `TraceReplay` checker already constructs its `initialBase`
position-for-position from `CheckerInput.initialFacts`; separately,
`ChronologicalReplay.Cursor.startInput` consumes `InitialContext` for cursor
replay. The later generic frontend must carry the corresponding binding into
direct emission. The current replay applications and final closure remain
indexed by the exact `CheckerInput.baseProgram` and target. The emitter also
seeds each instance event's fresh nodes with domain top after checking their
lookup in the reified final program. The real-sine tactic is now a client of
this module rather than the owner of the fold. Its semantic bridge and final
proof closure still name the canary's fixed base graph, declared base list,
and target; the goal reifier below begins removing that specialization.

A second live vertical validates this separation with `Real.exp`. Its
Mathlib-free package uses a distinct four-element fact lattice, contributes
one unconditional nonnegativity propagator, and has neither instantiation nor
equality transport. Its Mathlib companion contributes only real semantics and
one replay schema. The same policy session, joint package registry,
fact-polymorphic quotation, shared structural encoder, and generic evidence
fold produce the ordinary theorem `0 ≤ Real.exp x`. Thus both a multi-package
graph-growing sine proof and a single-rule exponential proof pass through the
same frontend API without a function switch. The reusable proof-emission
module does not construct the seed-to-input binding by itself. The exponential
client now sets the runtime and proof-side declared base lists to the same
reified facts, checks every seeded lookup definitionally, proves the recorded
hypothesis recipes, and supplies the resulting premise to closure. A reusable
`InitialContext`-style constructor remains future API work.

A mixed-function vertical tests the stronger requirement that independently
registered function packages cooperate in one search, rather than merely use
the same generic API in separate examples. The existing sine and exponential
canaries cannot soundly be concatenated: they instantiate different fact
types and hence different `Semantics`, fact-domain laws, and proof registries.
The mixed canary supplies the smallest shared range lattice needed to expose
that alignment requirement. A sine package unconditionally proves
`sin x ∈ [-1,1]`; a distinct exponential package is inapplicable until it sees
that exact input fact, then proves `exp (sin x) ≤ 3`. Its package theorem uses
the sine bound together with monotonicity of `Real.exp` and
`Real.exp_one_lt_three`. Thus the retained exponential event has the sine
event as an actual proof dependency, not merely an unrelated earlier
improvement. The structural goal reifier selects source, sine, and exponential
packages recursively from `Real.exp (Real.sin x)`, and the generic scheduler,
chronology quotation, and proof frontend remain free of function cases. The
result is the ordinary theorem `Real.exp (Real.sin x) ≤ 3`, without
`native_decide`. Runtime planning and the Mathlib-free packages perform no
rational normalization; the Mathlib companion may use `norm_num` for closed
side conditions such as `1 ≤ 3`.

This experiment also identifies the intended package boundary: independently
upgradeable operations may contribute their own syntax recognizer, executable
propagators, mathematical relation, and replay schemas, but packages taking
part in one run must agree on a fact representation and semantic value model.
Future domain adapters may embed a package's private facts into a richer shared
domain; merely joining registries with incompatible `Fact` parameters is not
meaningful. The mixed target already exercises recursive structural discovery
of both functions. Like the current package-composed semantics experiment, it
still requires the operation, meaning, and proof-package arrays in one fixed
aligned order; key-resolved package reordering remains future work. It does not
add a new expression during propagation; a
later mixed-function acceptance case should use the existing instantiation
protocol to introduce an auxiliary expression whose package then participates
in the same dependent chain.

That acceptance case is now executable for
`Real.exp (Real.sin (-x)) ≤ 3`. The caller graph contains only `x`, `-x`,
`sin (-x)`, and the outer exponential. The sine forward rule deliberately
declines an input whose instruction is negation, so direct propagation cannot
close the target. This is a search-side canary restriction that forces the
matcher path, not a mathematical limitation of the sine replay schema. A
sine-owned network matcher recognizes the oddness shape
and adds `sin x`, `-(sin x)`, and an equality between the latter expression
and `sin (-x)`. The resulting successful chronology is fixed by a live guard:
the instance event comes first; independent sine and negation packages derive
the unit-range fact on the two new nodes; generic equality transport installs
that exact fact, with its retained version, on the original `sin (-x)` node;
and only then does the independent exponential package derive the target.
The guard pins the complete initial matcher batch and engine-issued action,
every instance output and generation field, and the frozen quote entry's
origin, role, schema, and body. It also pins each narrowing event's program
version, predecessor slot/version and concrete previous fact, ordered
assumptions, and installed fact/version.
The dependent-typed emitter requires every exact predecessor proof to be
available at its retained version, so a missing or reordered dependency cannot
produce a type-correct replay term.

The goal reifier, target driver, policy session, chronology quotation,
`ProofFrontend`, and final semantic closure have no sine, negation, or
exponential branch. Each operation supplies its own syntax recognition,
planning, mathematical relation, and replay schema. They cooperate through
one shared fact domain and value semantics, while the sine matcher declares
the negation operation through the ordinary `requiredOperations` package
contract. The final theorem is an ordinary kernel theorem, and its
guarded axiom report contains only Lean's standard propositional extensionality,
choice, and quotient axioms. This vertical adds no rational backend and uses
neither `native_decide` nor an unchecked proof shortcut.

This is a deliberately exact canary, not yet the production abstraction. Its
instantiation and equality replay schemas validate the particular base and
extended programs, while its fact schemas and semantic model array still
resolve each operation by numeric position. The tactic rejects other graph
shapes rather than generalizing them.
Consequently it demonstrates that dynamic expression instantiation composes
with arbitrary downstream function propagation, but not yet that packages can
be reordered or instantiated under arbitrary surrounding graphs. The next
generalization should resolve operation meanings and replay obligations by
stable package keys, construct the extension proof for the actual appended
graph, and preserve this same guarded chronology as a regression test.

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
fixed-fixture exponential tactic currently requires only the target-reachable
operation and node prefixes, and the target fact, to match its semantic/proof
fixture.
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

The dynamic exponential vertical removes the canary's fixed compiled trace. It
starts `PolicySession` from the reifier's actual `CheckerInput`, runs the
target-directed controller below, quotes the retained session, and feeds it to
`ProofFrontend` with the dynamic base program, facts, and reflexive extension
proofs. The ordinary tactic theorem accepts an unrelated supported exponential
hypothesis which appends two nodes after the target, and it proves
`0 ≤ exp (exp x)` from a three-node target graph. Neither case adds a nested-
exponential or extra-hypothesis branch to goal closure, semantic model
construction, dependency assembly, or proof replay.

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
to the unchanged generic proof frontend. The target driver returns split plans
without itself owning a search tree; the separate checked branch-start layer
now creates exact child inputs. The operation table remains the fixed
source/exponential pair. Key-resolved semantic model selection must land before
operation packages may be reordered; array position is not a permanent package
identity.

The dynamic path is still bounded by the exponential package's engine envelope,
which permits at most five nodes and node depth four, even though the goal
reifier admits up to sixteen nodes and expression depth eight. Thus the single
unrelated supported hypothesis above fits, while two such hypotheses or a
sufficiently deep nested target fail at session preflight before search. The
current tactic adapter also collapses session-start failure, every non-target
`TargetRun` stop, and proof-registry failure into one generic diagnostic.
Separately, a missing target or a malformed or resource-limited fact-domain
target probe is conservatively treated as not yet reached, so search may
continue and later return another stop reason. Aligning the two envelopes and
preserving typed session-start, run-stop, and target-probe reasons in tactic
diagnostics remain future frontend work; none of these limitations is a
theorem-production assumption.

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

The semantic domain package does not check executable child construction a
second time. It independently proves only that the supplied parent, cut, and
children have the required coverage relation; authenticating those values
against a runtime `SplitPlan`, strict narrowing, and correct child construction
remain separate branch-layer obligations. The current transparent
`ProofEmitter.replaySplit` implements the generic join. Given a proof of
`parent` from the caller's `base`, a proof of
the target from `{node,left} :: base`, and a proof of the target from
`{node,right} :: base`, it applies `proveCover` and returns a proof of the
target from `base`. No policy callback, compiled session, branch score, or
runtime comparison enters that proof. A Mathlib-free Boolean canary uses a
nonempty inherited base; each supplied child proof explicitly consumes its
corresponding distinct assumption as well as that base. It obtains an ordinary
target not entailed by the empty context. Kernel-checked theorems pin both the
demo schema's chosen child orientation and the genuine failure of two positive
children to cover the parent. The former is a schema-format regression, not a
logical requirement that all coverage schemas use the same orientation.

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
Mathlib-free canary checks both routes, including an inherited derived fact
which is not a literal parent base member and an unrelated top entry. The
generic Meta frontend now quotes
the complete child `CheckerInput`, rejects any mismatch in its program, fact
array, or target, pins the full child assumption list, and turns the seed into
exact version-zero `FactProof` records. Its branch entry point then uses the
unchanged function-independent chronology fold.
The shared `emitSeeded` fold is a low-level Meta helper: its raw proof table
must already refer to the context's quoted base program and child assumptions.
The caller-root and branch-root entry points establish that precondition via
`seedBase` and `seedBranch`; later replay use sites still typecheck every
stored proof expression and fail closed on a mismatch.

The first live branch canary uses the independent real exponential package.
It partitions the source fact `.all` into `.nonnegative` and strict
`.negative`, justified by `0 ≤ x ∨ x < 0`. Each exact child input is paired
with a `BranchSeed`, starts an actual policy session, runs the exponential
propagator, and retains one ordinary fact event. `emitBranch` replays both
nonempty traces, `closeTarget` closes the same exponential target in each
child context, and `replaySplit` joins them into the caller theorem. The
assigned tactic term is built from those two live child results.

The corresponding executable split package now contributes a zero-landmark
rule for the source operation. The generic `BranchStart.prepare` transition
does not trust the public fields of the `SplitPlan` it receives. It resolves
the plan's exact retained suggestion identifier and requires that record to
contain a split with the same complete action (including its request serial),
node, dyadic cut, reason, and proposal-time fact version. It also checks the
exact scope and reconstructs the source key from that action. The action must
pass the retained engine's full freshness check: its application, registration,
watched versions, write authority, program-sensitive version, and structural
matcher provenance must still match engine-owned state. The transition
separately checks the current program version, node fact, and fact version for
precise diagnostics, and repeats the configured endpoint-cost preflight at
this boundary so a directly constructed plan cannot bypass it. This
authenticates the plan against retained engine data; the search controller
still owns the policy decision that selected that offer. A domain-supplied
`Splitter` interprets the dyadic cut; the manager independently requires both
returned facts to be distinct, exact `.improved` results of `FactDomain.narrow`.
It replaces only the selected slot in the parent's complete current fact
array, preserves the target and current program, assigns two fresh child scope
identities, and charges separate tree depth and total-scope limits. Branch-tree
state has a private constructor: its root is derived from an engine-owned
session, and only `prepare` can remove an active parent scope, register its two
children at the next depth, or advance the monotone counters. The live canary
checks that these prepared inputs are exactly the two proof-side inputs above,
then starts both child sessions under the allocated scopes. Its Meta tactic is
still deliberately hard-coded to quote those canary constants rather than the
runtime `Children` value; dynamically quoting an arbitrary prepared branch is
a later frontend bridge, not a property established by this experiment.

The executable split package currently emits no replayable fact, instance, or
equality event, but it still occupies a package-ownership position. Its proof
registry therefore contains an explicit empty package at that same position.
Conformance checks both directions: split-enabled registry assembly succeeds
with the placeholder and rejects the shorter ordinary proof-package array.

Branches may instantiate different auxiliary expressions. Each child replay
therefore closes its target back to the program snapshot at the split before
the two results are joined. The package-owned `Extends` theorem and semantic
stability law already provide the required direction: extend a split-snapshot
model into the child program, use the child theorem there, and transport the
old target back. Nodes, equality edges, payloads, and positive fact versions
created below one child are scoped to that child and cannot be resolved by its
sibling. Parent program nodes and proof terms may be shared structurally.

A runtime contradiction flag is also not a closed child. The generic
`ProofEmitter.RefuteSchema` now requires a domain companion to turn one exact
established bottom or inconsistent fact into `False`; `replayRefute` then uses
ordinary elimination to produce the branch target. The real exponential
adapter supplies the first `.empty` schema, and its conformance theorem closes
an arbitrary target from the exact bottom assumption while rejecting `.all`
by reduction. The conclusion is necessarily ex falso because the canary base
contains the bottom fact; the conformance obligations are successful
transparent replay, rejection of the satisfiable `.all` fact, and the guarded
kernel-dependency report. No engine flag or evaluator result enters that
theorem.

`ProofRegistry.Package` also contributes optional fact recognizers and
refutation handles. Lookup accepts exactly one matching handle; no match or an
ambiguous match fails closed. The low-level frontend treats its supplied fact
and version arrays as untrusted selector data; the live child passes its exact
retained engine arrays. For any selected fact, the frontend requires the same
node, version, and value in its chronology evidence table before it applies the
schema and produces the child target by ordinary elimination. Arbitrary arrays
cannot create evidence, but this helper does not itself certify their identity
with an engine snapshot. Its first mixed join splits the exponential output:
the left child closes directly from `.nonnegative`, while the right child
starts from `.negative`, replays the exponential proposal to derive `.empty`,
and closes only through `replayRefute`. The runtime contradiction result
selects this path but is not an argument to any emitted proof combinator. An
unexplored, fuel-limited, resource-limited, incomplete, or merely saturated
child likewise does not close the parent target.

The later proof-plan sketch represents an endpoint contradiction by two
`FactId`s, whereas `replayRefute` deliberately consumes one exact established
fact. Its frontend lowering must therefore either resolve an already-installed
contradictory meet fact or combine the two retained proofs through the domain's
`FactDomainSchema.proveMeet` theorem before invoking the refutation schema.
That lowering must first check that both identifiers name facts at the same
node. The current frontend consumes an already-installed single contradictory
fact; the two-proof lowering remains part of the open tree-frontend bridge.

The first branch-start layer also rebinds each completed child result to the
exact prepared base program and initial fact array, then rechecks the retained
target fact and version. Its ordinary two-target closure gate rejects a stopped,
saturated, fuel-limited, malformed, or wrong-input child. It classifies a
runtime contradiction separately but deliberately refuses to treat that flag
as proof closure; the frontend must first resolve an established bottom fact
and apply the refutation schema described above.

The first generic runtime tree manager now retains internal nodes recording
validated plans and exact child inputs, and leaves recording target,
contradiction, saturation, resource failure, split refusal, session-start
failure, or any other precise `TargetRun` result. It stores the append-only
node array and the supported stable pending frontier, so a global step limit
returns an honest partial tree rather than relabelling unexplored leaves as
closed.
Independent supported limits bound processed leaves, accepted splits, current
leaf count, pending frontier count, split depth, total created scopes, and each
leaf run's policy fuel in addition to the per-session engine and payload limits.
Split- and leaf-limit
exhaustion is retained at the exact parent leaf. A child session which cannot
start is likewise retained beside its sibling instead of silently deleting
the branch.

The manager is function- and representation-independent. Its configuration
supplies the fact domain, runtime packages, controller, splitter, child-policy
fork, and pending order. The initial orders are depth-first and breadth-first;
their frontier transformation is separately tested so later best-first or
hybrid queues do not affect branch validation. The exponential conformance
tree selects the authenticated root split, starts both exact scoped children,
runs the arbitrary exponential propagator in each, and retains two target
leaves. Separate guards show that one global step leaves both children pending,
and that zero split or one-leaf budgets retain an explicitly blocked root.

A second Mathlib-free runtime canary now makes the scheduling abstraction
observable on live work. Its root splits one source; the side-aware policy
fork sends only the left child to split a second source, while the right child
immediately runs the arbitrary exponential propagator. After the nested split,
the depth-first frontier is `[left-left, left-right, right]` and the
breadth-first frontier is `[right, left-left, left-right]`; both complete to
the same five-node retained tree. This catches an ignored `Side` argument and
an accidental exchange of the scheduler's old and fresh queues. The second
source is deliberately irrelevant to the exponential target, so this is a
scheduling and accounting canary, not the still-required useful nested
subdivision benchmark.

This runtime tree contains no proof evidence. The separate generic
`BranchProof` frontend now folds a settled retained tree bottom-up. It first
binds every leaf and split run back to its exact starting scope, base program,
and initial fact array. A split's parent snapshot is instead checked against
the completed run's current program and fact array, while retaining the
starting request's target. This distinction permits narrowing and expression
instantiation before subdivision without mistaking the post-run facts for
caller assumptions. Each child is checked against the exact child input
stored by its parent, including that input's target, and the stored split plan
must equal the plan which stopped the run. Pending, blocked, failed,
dangling, shared, cyclic, and unreachable nodes are rejected. Client callbacks
then replay each closed leaf and apply each package-owned split join; the final
emitted expression must have the requested Lean target type. A callback can
therefore cause rejection or choose a different kernel-checkable proof, but
tree data itself cannot become evidence.

Every child admitted by a split's coverage theorem must eventually close by
replaying a proof of its target or by deriving a package-checked refutation.
A retained runtime result is not by itself a proof of closure: the leaf
callback must turn it into the corresponding kernel-checked evidence before
the bottom-up join can accept it.

A Mathlib-free live canary first propagates an unrelated exponential node,
then splits a source, and finally closes both children on a second exponential
target. Its split parent contains the propagated fact and therefore differs
from the starting input; the generic fold accepts the exact post-run snapshot,
but rejects replacing it with the stale start snapshot or changing the stored
split point. The package callback remains responsible for replaying any
pre-split improvements needed by the eventual parent theorem.

The distinct-assumption ReLU canary now runs through this generic path. Its
retained root has two exact live target children; the leaf callback invokes the
unchanged generic chronology emitter with the side-specific proof registry, and the
split callback applies `replaySplit`. The resulting expression is assigned to
an ordinary declaration and its axiom report is compile-checked. Separate
negative tests reject the delivered step-limited partial tree, a fork whose
two edges share one child, and an otherwise valid but unreachable extra node.
For best-bound mode, unfinished leaves must contribute their inherited parent
fact to the global hull; they never inherit a tighter sibling fact.

Several operational choices deliberately remain experimental:

- restart a child session from a checked snapshot, or add a sealed session-fork
  operation which preserves reusable work and immutable payload sharing;
- use the delivered depth-first or breadth-first list frontier, or replace it
  with best-first execution or a bounded hybrid without changing retained
  nodes;
- store branch-local program suffixes directly, or hash-cons identical
  instantiations above the scope layer;
- retain `Dyadic` in real-domain executable plans while keeping the proof
  schema generic, or replace it with a registry-resolved opaque landmark.

These choices may change performance and certificate size, but not the
coverage-and-two-proofs contract. The real exponential canary supplies the
first two-sided live execution and proof join, but exponential nonnegativity
is unconditional: neither child target proof currently needs its split
assumption. The mixed target/refutation join does consume the two incompatible
output assumptions. A separate conformance-local max-zero/ReLU package now
uses deliberately conditional rules to supply the first explicit
non-contradictory distinct-assumption plumbing vertical. This conditionality
is a package-test design choice, not a claim that branching is mathematically
necessary for its unconditional final theorem. The nonnegative-side rule
proves the output fact by rewriting `max x 0` to `x` from the left split fact;
the strict-negative rule proves the same output fact by rewriting `max x 0` to
`0` from the right split fact. Both child sessions retain one ordinary rule
event with the exact side fact as an input, the unchanged generic frontend
replays them, and `replaySplit` produces the joined entailment evidence.
`closeRelu` specializes that evidence to the ordinary theorem `0 ≤ max x 0`.
Each rule rejects the unsplit top fact, and mutating either quote to use its
sibling's assumption makes emission fail. The package remains a compact
conformance fixture while we decide which parts belong in the Mathlib-free
runtime and Mathlib semantic
companion. Remaining acceptance tests include a theorem whose proof
mathematically requires branching, a nested split, a child-local
instantiation, a sibling-reference attack, a non-interior repeated split,
and per-leaf fuel exhaustion with no theorem emitted.

The concrete dyadic interval canary now composes the useful pieces across a
post-contraction split. A live backward centered-function contractor narrows
the source from the whole line to `[1/4,3/4]`; the exact splitter then produces
`[1/4,1/2]` and `(1/2,3/4]`. The left child uses its closed interval assumption
to prove `|x - 1/2| ∈ [0,1/4]`. The right child uses its strict lower cut together
with a separately modeled identity-node fact `x ≤ 1/2` to derive exact empty,
then closes only through the package-owned refutation schema. The root callback
replays the retained backward event to recover the contracted parent proof
before applying the package-owned coverage theorem. The generic `BranchProof`
fold binds that proof to the live post-run snapshot and exact child inputs;
mutating either child trace to name its sibling's interval is rejected.

### Proof-producing frontend

The fixed canary also requires a live session with no dropped work and an exact
proof history of one instance, one equality, three fact events, and the
expected interleaving before it reads historical values through
`Engine.factAt?`. This exact trace-shape gate is not a claim that
`Session.complete` holds. The values are quoted as data, while their proofs
come from caller assumptions, top soundness, or an earlier emitted replay
result. A future arbitrary-trace emitter must likewise obtain evidence from
its chronological proof table; a successful full-history lookup is never
evidence that the dependency was available at the required earlier step.

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
name is elaboration data, not trusted evidence. The direct assembler resolves
the selected handle and uses that declaration in its emitted proof term. A
missing name, wrong type, or schema whose own replay key does not match the
entry makes application construction or transparent replay fail. Current
safety comes from constant lookup, ordinary Lean typechecking, and the replay
transition's exact key check; only the resulting well-typed theorem
application enters the kernel.
`ProofRegistry.Package` now joins each package's semantic schemas and emitter
fragment, plus any domain-level refutation recognizers owned by that package.
Joint assembly first uses the semantic registry check to establish exact
package-for-package ownership and bidirectional coverage against the
executable formats. It then requires package-local equality of semantic and
emitter replay-key sets and global emitter uniqueness. Consequently an event
handle cannot be omitted, added under an undeclared key, or borrowed from
another package even if the final flattened key set would happen to match.
Refutation handles have no executable event key; exact-fact lookup instead
requires a unique matching recognizer, and the selected `RefuteSchema` must
accept the same fact during kernel-checked replay. The live real-sine semantic
replay and direct-emission table are both projections of this one checked
registry. This governance relation is still defense in depth rather than part
of theorem soundness: every selected schema must produce the required
kernel-checked claim.

The current real adapter places its domain-wide `.empty` refuter in the source
proof package solely to give it one registry-owned lookup position. The theorem
is about fact-domain bottom semantics, not the source operation. A second
matching owner would make lookup ambiguous and fail closed; a future explicit
domain-schema home may replace this provisional ownership convention.

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

## Lessons from RealPaver

RealPaver is the closest concrete reference architecture for the intended
combination of arbitrary nonlinear contractors, adaptive consistency, and
branching. The historical claims below come from the 2004 edition 0.4 manual;
implementation claims refer to the tagged RealPaver 1.1.1 C++ sources, rather
than assuming that both versions expose identical algorithms. The 1.1.1
system separates a generic `Contractor` interface, contractor composition,
dependency-driven propagation, strong-consistency contractors, variable
selection, and search-space order. This supports the SPEC's separation between
package rules, engine transitions, policy, and the branch layer, but RealPaver's
operational status values are not a proof boundary suitable for Lean.

The RealPaver 1.1.1 propagation loop initially queues every contractor. After
one contractor mutates its box, it examines only variables in that contractor's
scope; a sufficiently large relative width reduction wakes inactive dependent
contractors. HC4 builds one `HC4Revise` contractor per constraint over a shared
expression DAG. BC4 associates one `ContractorBC4Revise` with each constraint;
each such contractor first applies `ContractorHC4Revise`, then applies
`ContractorBC3Revise` only to variables which occur more than once in that
constraint. The source calls this combined operator hull/box consistency; it
should not be described as pure box consistency or conflated with standalone
BC3. The solver can compose a base HC4, BC4, or affine propagator with ACID,
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

In RealPaver 1.1.1, ACID is especially useful for the upgradeable policy
design. It ranks variables by a derivative-based smear score, alternates
learning and exploitation phases, measures contraction gains, and learns how
many variable-level 3BCID contractors are worth applying. The transferable
idea is not its particular average-gain formula. A policy-private state may
learn an effort frontier from bounded observations and choose fewer expensive
offers on later boxes. The engine must still own action identities, exact
inputs, budgets, and proof payloads. Learned scores are untrusted scheduling
data, and mutable ACID state must be branch-owned or keyed by the complete
semantic snapshot before it is reused across siblings.

RealPaver 1.1.1's variable 3BCID implementation first slices one variable, removes
inconsistent outer slices using a nested contractor, and then applies CID to
the remaining middle slices, returning the hull of surviving reductions. This
maps to the `shave` action rather than a global solver split. Its Lean replay
payload must enumerate a finite covering partition, give a checked
contradiction for every discarded slice, give the retained contraction for
every surviving slice, and prove the returned hull covers all survivors. A
coarse `Empty` status from a nested run is insufficient. The number of slices,
nested propagation work, and retained proofs are all charged to the one action.

RealPaver 1.1.1 keeps solver branching separate. Its variable selectors include
round-robin, largest/smallest domain, mixed discrete/continuous selection,
derivative-smear selection, and hybrids. Its pending-node containers include
DFS, BFS, distant-most DFS, and hybrids which search depth-first until a
solution and then resume from a best pending node by depth or perimeter. These
are useful initial policies to reproduce behind `Controller`; none belongs in
the proof-producing core. For proof goals, additional useful scores are
distance to a closing fact, predicted proof size, and whether both children are
likely to close rather than average contraction alone.

The principal non-transferable part of RealPaver 1.1.1 is its `Proof` enum. Its
`Empty`, `Maybe`, `Feasible`, and `Inner` values are operational certificates
returned by C++ methods, not kernel proof terms with replayable provenance. In
HexInterval each successful analogue needs a package theorem or checked
certificate tied to the exact box, constraint, and program snapshot.
`Maybe` maps naturally to an unproved search result. `Empty` needs the
refutation schema described in the split section. Feasible/existence results
from interval Newton need separate existence and uniqueness theorem schemas;
they must not be conflated with universal interval bounds.

The RealPaver 0.4 manual gives small, discriminating acceptance cases:

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
bounded frontier of offers and the policy echoes the complete controller-owned
description of one offer it observed; selection returns the retained offer,
never the policy's copy. In the sketch below,
`InstantiationSemanticKey` is the payload-erased canonical family,
engine-computed generation, proposed-operation/reference graph, and unordered
equality-pair key. Replay-facing trigger metadata is deliberately absent;
`PolicyFeature` is a bounded exact integer key/value; and frontier events are
engine-issued additions, refreshes, tombstones, and observations.

The current Mathlib-free `HexInterval/Policy.lean` contract implements the
generic part of this boundary. `OfferView Id SemanticKey` retains the complete
controller-issued offer, and `Decision Id SemanticKey` echoes its scope,
serial, program version, remaining budget, identifier, semantic key, class,
age, and bounded score. `checkViewWithin`, `revalidate`, and
`checkDecisionWithin` fail transactionally on malformed program/fact state,
duplicate identifiers, stale stamps or budgets, changed offer fields, and
independent offer-count, byte, pair, logical-work, and score caps. Identifier
and semantic-key measurement callbacks, equality on nested key values, and
equality on arbitrary reconstructed facts remain an explicit non-preemptible
envelope; the cap governs accepted retained data and subsequent adapter work,
not arbitrary callback allocation or time. Branch-backed decision validation
reconstructs and validates the branch snapshot once, then checks bounded offers
without repeating whole-program validation. The returned runtime value has no
theorem authority.

The supported Mathlib-free `HexInterval/Search.lean` layer owns the next
generic boundary. Under ordinary/public imports, its sealed `Search.Session`
binds one exact checked `State.Branch`, registration snapshot, scope, serial,
complete policy view,
controller-owned offer-to-`Action` bindings, bounded diagnostic log, and
the cumulative accepted-step count for that run. `Session.startWithin` is the
only reset point and creates a new run; no public-import client can use its
record constructor or update to install fresh counters into a live session.
Session-only accounting does not require frontier capacity, so
`maxFrontier = 0` does not reject a non-branching session. Before any semantic
scan or package measurement, session authentication uses `Policy.maxOffers` to
cap the retained offer array before
mapping or traversing it. It separately caps the base and current program,
history and aligned branch arrays, registry, binding/application/equality
arrays, every
operation/node/rule/binding port list, and every action input/write/structural
input list against the corresponding `State.Limits`. Binding count uses
`maxApplications`; `maxScopeNodes` independently caps each scoped read list and
write list. `State.maxActions` is cumulative controller work, not an offer-array
cap. The same preflight enforces operation/node/rule/arity/depth, matcher-batch,
effort, generation, application, equality, and accepted-fact limits with the
exact State resource class.

The checked `Envelope` is supplied to each session transition and is not stored
inside the session value. A later call may supply different, including tighter,
limits while the cumulative accepted-step count remains part of the session.

The current supported session retains generation stamps for compact
`ApplicationId`s but not the concrete application table compiled by the
experimental controller. Search therefore treats the compact identifier as an
opaque scheduler handle: it authenticates its bounds and generation while
independently checking the action's rule key and local rule id, anchor,
operation, kind, reads, writes, and structural inputs. A callback must not use
the compact application id as authority for a rule or anchor. Retaining and
checking the exact application table is an obligation for the supported
controller/package assembly; the present Search contract does not claim that
correspondence.

`prepareWithin` authenticates the session once, revalidates the external policy
decision against that already-checked immutable view, and returns only the
exact controller-owned action. `chooseWithin`, `acceptWithin`, and
`invokeWithin` use the same private-constructor checked artifact internally:
each public transition reconstructs branch history and invokes policy
measurement callbacks once, while callers cannot forge or retain the artifact.
`invokeWithin` authenticates the decision and checks step exhaustion before
executing the non-preemptible callback. `acceptWithin` checks an untrusted
callback batch against that action's serial, program version, input versions,
and write set, preflights total retained history, and folds exact successor
updates over the once-authenticated local branch before returning a replacement
session. A stale later update therefore cannot partially commit an earlier
update. Callback failure has an exact conservative stop, and diagnostic
truncation can change only the log, not facts, versions, provenance, scope, or
contradiction state.

`Search.Frontier` is a public ordering value, but ordinary-import live tree
authority is the sealed `Search.FrontierState`, which owns the pending frontier
and its cumulative step, split, retained-leaf, scope, and next-scope accounting.
The raw `Accounting` constructor and advance operations are private. Checked
composite start, settle-head, and split-head transitions consume and return the
whole sealed value, so a fresh counter cannot be transplanted onto an existing
frontier and a phantom frontier cannot advance live counters. Reusing an old
pure value may produce an alternative bounded successor; it cannot create a
successor which bypasses the limits supplied to that checked transition/run
handle. Limits are not stored in the value and may be tightened by a later
transition. A separate start creates a documented new run rather than resetting
an existing one.

The supported parent/depth/scope/branch contract adds a second
ordinary-import-sealed type, `Search.LeafFrontier Fact Cause Payload`. Its
private constructor and private inner `FrontierState (Leaf ...)` prevent callers
from feeding a generically
scheduled leaf-shaped frontier back into `Search.splitWithin`. Read-only head,
pending, raw-frontier, and accounting projections support inspection. Only
`startFrontierWithin`, `settleWithin`, and the specialized `splitWithin` return
another `LeafFrontier`, and the latter checks exact parent restoration, child
depth, fresh scopes, branch validity, and retained-scope uniqueness before the
new wrapper becomes available. Thus the generic composite remains usable by a
different sealed controller such as `BranchTree`, but it is not authority for
the stronger leaf protocol for public-import clients.

`Search.Result.Tree` is the supported retained-result prerequisite for a later
proof-tree fold. Its private constructor keeps the exact node array, sealed
`FrontierState Result.Id`, cumulative accounting, and logical cost together;
callers cannot transplant a raw frontier, reset counters, or supply a complete
child snapshot. `Result.startWithin` admits one checked root.
`Result.splitWithin` authenticates the exact pending parent and current
predecessor, structurally checks and retains the complete runtime split action,
allocates the two fresh scopes through the sealed frontier, and reconstructs
each restarted child from the checked current parent fact array with exactly
one version-zero seed delta. The restarted `State.Branch` represents every
inherited fact at version zero, resets every generation stamp to zero, has no
history, and has `contradictory = false`. Its inherited facts are not thereby
reclassified as assumptions or given intrinsic derived provenance by the child
branch. Instead, the retained tree's exact parent/side/seed edge authenticates
that they came from the current parent consequence snapshot. A downstream
controller or proof quotation must consume that edge and must not carry
pre-split generation stamps into the restarted child. `Result.splitWithin`
does not independently resolve the action's rule key against a package
registry. `Result.settleWithin` consumes the exact pending head and retains an
exact target, refutation, or unknown record.
Whole-tree validation reconstructs every parent/side/seed edge, restored
parent, pending set, step/split/leaf/scope equation, branch state, and logical
cost.

Result limits independently bound retained nodes, each package body, declared
logical bytes and work, plus the existing search and state resources. Count
caps are checked before retained arrays and body lists are traversed. Adapter
measurement, equality, and construction of arbitrary facts, causes, plans,
schemas, and bodies remain explicitly non-preemptible; packages must bound
those values before return. The split plan, schema, refutation record, target
record, and runtime contradiction state are untrusted data, never evidence.
As for the sealed frontier, `Result.Tree` is a reusable pure value rather than
a linear capability. Reusing an old tree may form alternative successors, but
the checked transition keeps scopes unique within each resulting lineage and
cannot reset that lineage's retained counters. Limits are supplied per call,
not stored in the tree: a later call may relax them, while a tightened call
rejects an already-retained value which exceeds the new caps rather than
grandfathering it.
Semantic split coverage, package-owned refutation theorems, recursive proof
replay, search-to-recipe quotation, and unknown-leaf rejection by a proof fold
remain later supported edges.

This visibility is not a claim against Lean's deliberate `import all
HexInterval.Search`. That form exposes private implementation names to trusted
source and is an explicit trusted-internals escape hatch, not decoded runtime
data or proof authority. Arbitrary trusted Lean source can already use `unsafe`
or introduce axioms, so it lies outside the fail-closed callback/data threat
model. The repository DAG check rejects `import all HexInterval.Search` outside
an exact reviewed owning/internal allowlist (currently empty); downstream code
which deliberately chooses `import all` accepts that trusted-source boundary.

Under ordinary imports, experimental `BranchTree.State` is likewise sealed and
contains one `FrontierState TreeId`; callers cannot independently replace its
nodes, frontier, branch manager, or counters. Its checked transitions derive
the exact head internally. The generic composite split authenticates only cumulative
resources and stable scheduling for at most two package-validated children;
the enclosing sealed `BranchTree` checks child construction and semantics.
The supported `Search.splitWithin` specialization additionally preflights
every retained parent/child branch, requires exact immutable parent records,
fresh scopes and depth, and rejects detached parents. `settleWithin` likewise
returns and charges the exact head rather than trusting a detached count.
`BranchTree.snapshot` deliberately exports editable retained nodes/frontier as
untrusted proof-fold input, but that snapshot carries no live accounting or
mutation authority. Callback execution, measurements, and equality on caller-
selected Lean objects remain explicitly non-preemptible: packages must bound
result construction before returning, after which search preflights returned
counts, retained bytes, and declared work.

The experimental target controller now implements the supported `Interface`
and returns the actual supported `Step`; it stamps a selected supported offer
into a supported decision before the policy session authenticates the exact
scope, serial, program version, remaining budget, identifier, semantic key,
class, age, and score and performs the existing engine-owned freshness checks.
The concrete `OfferId`,
`OfferKey`, instantiation/split encodings, staged/adaptive/feature policies,
package callbacks, semantic outcome interpretation, event history, concrete
policy sessions, target-specific stop taxonomy, and callback-to-proof-recipe
driver remain under `HexInterval/Experiment`. The Mathlib companion's generic
tree replay does not make the older concrete `BranchProof` controller a
supported API. The experimental `BranchTree` consumes the supported
search order, limits, accounting, and frontier container, while its
package-specific child construction remains behind `BranchStart`. The older
sealed propagator session is not presented as a supported `Search.Session`:
its concrete engine/registry/payload ownership must be migrated through the
new authenticated transition boundary rather than hidden by an alias. No
`balancedV1`, score model, storage layout, offer generator, scheduler default,
or proof format is selected by the supported contracts.

The implemented generic records and current concrete experimental keys are
sketched below:

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
  providerFamily  : Nat
  providerVersion : Nat
  key             : Nat
  value           : Int

structure ObservationSummary where
  outcome      : Nat
  changedFacts : Nat
  logicalWork  : Nat

structure PolicyBudget where
  decisions : Nat
  traversal : Nat
  noteBytes : Nat

structure EngineBudgetView where
  actions             : Nat
  matcherVisits       : Nat
  acceptedFacts       : Nat
  nodes               : Nat
  applications        : Nat
  equalities          : Nat
  retainedSuggestions : Nat
  instances           : Nat
  queueEntries        : Nat
  generation          : Nat

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

structure Decision where
  scope          : ScopeId
  serial         : Nat
  programVersion : Nat
  id             : OfferId
  expected       : OfferKey
  offerClass     : OfferClass
  age            : Nat
  score          : Int
  remaining      : EngineBudgetView

inductive PolicyEvent (Fact : Type)
  | frontier (added : Array OfferView) (removed : Array OfferId)
  | rule (observation : RuleObservation Fact)
  | equality (observation : EqualityObservation Fact)
  | instanceAdmitted (programVersion : Nat) (added : Array OfferView)
  | splitPrepared (scope : ScopeId) (node : NodeId) (point : Dyadic)
  | choiceRejected (choice : Decision) (reason : Nat)
  | engineResource (resource : Resource)

structure DecisionNote where
  stage  : Nat
  reason : Nat
  score  : Nat

inductive PolicyStep (State : Type)
  | select  (choice : Decision) (note : DecisionNote) (next : State)
  | dismiss (choice : Decision) (note : DecisionNote) (next : State)
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
diagnostic cap. The supported `Trace.Log` contract provides exact retained
event-count, payload-byte, logical-work, and code limits with explicit
truncation. The current experimental `PolicyEvent` protocol does not yet
encode into that log: it retains exact fact values and therefore still has no
general byte cap. `Trace.Log.append` sees an already allocated byte payload,
so it cannot preempt arbitrary callback, `Fact`, `String`, or Lean-object
construction. Packages must bound that explicitly non-preemptible construction
envelope before returning; controller retention begins only afterward.

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

The first executable staged baseline now implements this ordering without
inspecting facts, operation keys, or package identities. It ranks engine-owned
equality and forward/backward/rewrite offers first, then structural
instantiation discovery and admission, then improve/shave/regularize and
bounded retry offers, then split probes and their retained split plans.
Configuration independently disables instantiation, retries, or splits and
bounds retry effort; the oldest offer wins within a stage and stable view order
is the final tie-breaker. If enabled semantic work finishes while only
disabled offers remain, the target driver stops with `policyStop` and retains
the live-offer count; it does not dismiss or execute those offers.
Policy-private counters record rule and equality runs, actual fact-version
changes, no-change and inapplicable outcomes,
extensions, failures, dismissals, and rejected selections. These counters are
diagnostic inputs for later scoring, not evidence.

The first feedback-guided variant keeps the same function- and
representation-independent stages but accumulates observations at a stable
engine-owned application or equality site. Its bounded integer score rewards
engine-derived installed fact-version changes relative to bounded,
package-reported deterministic arithmetic, traversal, proof-node, or
equality-narrowing work. That reported work is only a search hint and is not
proof evidence or an independently measured engine cost. The record also
retains the last complete invocation snapshot. A repeated `noChange` on that
exact snapshot subtracts a configurable penalty, while changed input versions
reset that consecutive fixed-point penalty and receive at least the untried
optimism score.
Thus useful history survives an ordinary wake-up without letting an obsolete
fixed point suppress newly eligible work. The shipped coefficients are covered
by conformance: one unit-cost improvement outranks an untried peer, a repeated
fixed point falls below it, and a changed-version wake-up reuses the stable gain.
The fixed-point penalty applies only when an already observed exact invocation
is offered again without a snapshot change. Ordinary wake-ups change the
snapshot, so this first policy promotes historically productive sites but does
not generally demote unproductive sites across successive input versions.

The feedback table has an explicit deterministic record bound and evicts the
least recently updated stable site when full. Instantiation and split offers
retain their staged rank but do not yet have feedback records; invocation, retry, and
equality work do. Offers at or beyond the configured fairness age form the first
tier. On the normative finite frontier, where selection consumes an offer, this
eventually samples every continuously eligible item; stable offer order remains
the last tie-break. This policy still does not interpret interval width, target
distance, mathematical function, or package key. It tests the upgradeable
feedback seam before domain-specific potential features are admitted through an
equally bounded interface.

The first executable package-feature experiment supplies that interface
without adding fact or function cases to the scheduler. Independently
registered companion providers have a numeric family and compatibility
version. A stateless provider receives one exact immutable policy snapshot and
one engine-owned offer, and returns provider-local signed integer features; an
empty result means that provider contributes nothing for the offer. The
decorator attaches the provider identity to every local key. Package order,
offer order, and local
feature order determine one stable output order, while duplicate provider
identities and duplicate local keys are rejected.

The complete provider/offer cross product is preflight-counted before callbacks
run.
Independent limits bound provider count, provider checks, features from one
provider for one offer, features attached to one offer, total features, local
keys, and absolute feature values. Decoration is transactional: an oversized
or duplicate result yields no partially featured view. The resulting object
retains each complete original `OfferView`; a policy can only return that base
offer through the existing selection path. Thus an inaccurate or stale feature
can change scheduling and therefore which trace is generated, but it cannot
authorize a transition, enter proof evidence, bypass replay, or weaken replay
validation.

This is deliberately a companion registry rather than a field added to every
runtime package. It lets experiments compare interval-width, goal-distance,
and split-potential vocabularies before fixing their keys or formulas. A
production consolidation should assemble the feature companions alongside the
runtime packages and expose the program structure needed for dependency-slice
features. The callback is pure and accepted decorated output is bounded, but
the current experiment cannot preempt excessive computation or candidate-array
allocation inside a callback. Production providers therefore need either a
restricted bounded builder or an auditable
declared-work protocol in addition to these output bounds.

The first consumer of this interface is a generic bounded scoring adapter over
the feedback-guided policy. Its immutable plan is an ordered array of
`(provider family, provider version, local key, signed weight)` terms. Plan
construction transactionally rejects duplicate addresses and separately bounds
the term count, provider components, local keys, and absolute weights. Selection
revalidates that plan against its own limits, so a plan built under a more
generous configuration cannot bypass a stricter caller. It also requires the
base and decorated offer counts to fit before traversing them, then requires
the decorated offers to match the exact base view in order and field-for-field.
It subsequently bounds features per offer and the conservative
feature/term comparison count before scoring. Every decorated feature address
and value is rechecked against independent component, key, and absolute-value
limits before lookup or multiplication.
Consequently the adapter's own configuration sizes and traversal counts are
bounded. Equality of authentic offer keys may still traverse their engine-
bounded nested structural lists; hostile hand-built keys need a separately
bounded representation. The earlier limitation on work performed inside a
provider callback remains.
The decorator and scorer limits are independently valid configurations, so a
caller must choose compatible bounds. A decorated view which exceeds a scorer
bound fails closed with no selection. An adaptive learned score above the
configured score bound is likewise rejected rather than silently clamped and
allowed to flatten two different priorities.

Scores use exact `Int` multiplication followed by explicit symmetric
saturation, and saturating addition is applied in configured term order.
Unknown emitted features and configured addresses missing from an offer are
inert. Signed feature values and signed weights are both supported. Feature
score is combined with the bounded adaptive learned score only after the
fairness tier and staged semantic class have been fixed; it therefore cannot
move a fresh action ahead of a fairness action or move a split ahead of cheap
propagation. Age and stable decorated-view order remain the final tie-breakers.
The chosen result is the exact aligned base `OfferView`, not a reconstruction,
so ordinary engine revalidation remains authoritative. Conformance uses two
unrelated providers to make width and goal/split data reverse otherwise-tied
choices, and covers missing, unknown, negative, saturated, duplicate,
oversized, and runtime-resource cases.

Only `PolicyFeature.decorate` authenticates provider origin and uniqueness.
The public featured-view structure remains useful for scoring experiments, but
a hand-built view may fabricate or duplicate feature identities; those values
can influence ordering after passing the explicit bounds, yet cannot alter the
aligned base offer, authorize a transition, or enter proof evidence.

A live Mathlib-free arbitrary-function canary presents two exponential
forward contractors and one source split rule in the same frontier. The policy
selects both fact improvements, then invokes the split probe, then returns its
split plan; it contains no reference to any of those rule keys. This establishes
the replaceable staging seam. It does not yet claim that fixed stage order is
the best policy, nor does it implement width- or goal-sensitive scoring.

The planned scoring experiment computes a goal-directed potential rather than
summing raw widths.
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

The concrete `Dyadic` split point and `EndpointLimit` in the executable
engine/policy protocol are a deliberate real-domain-v1 seam, not a claim that
every future domain or runtime branch manager must use dyadic cuts. The
proof-side `SplitSchema` is already polymorphic in its cut type. Keeping the
runtime seam concrete lets the arbitrary real-function vertical proceed while
the later multi-domain runtime API remains open between a domain-owned split
interface and an opaque registry-resolved landmark. That runtime choice does
not require changing function-package, instantiation, or proof-replay
protocols now.

A split on term `t` adds `t ≤ m` to the left child and `m < t` to the right
child. This complementary form preserves strictness, avoids a duplicate
boundary case, and is justified by linear order. A split need not target a
free variable. Splitting a derived node is useful when several occurrences
share that node, though contractors are needed to transfer the cut to its
arguments.

### Budgets and termination

Every target search is required to be finite because its configuration bounds:

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

The current supported proof layer has two distinct decoded-data envelopes.
`Proof.Limits` bounds packages, schemas, body cells, ordered dependencies, and
flat chronology. `Proof.TreeLimits` additionally bounds retained proof nodes,
depth, aggregate tree/body cells, and structural proof work. It does not expose
a separate checker-execution counter. The Mathlib-free `Search.Result.Limits`
and exact caller-supplied `Measure` authenticate and bound the retained runtime
tree first; changing that measure can make the same pure tree fail validation.
These limits are checked independently because runtime tree records and proof
recipes are both untrusted data.

The current retained tree freezes each node's `Source.branch` when that node is
created. A split child restarts its program version and fact generations at
zero and the retained-tree API does not yet advance that child snapshot.
Consequently a non-root proof chronology must be empty or proof-state-only,
and a target/refutation terminal can cite only facts current at node creation.
This edge proves exact split/refutation folding, not recursive propagation in
children; authenticated callback-to-recipe quotation plus branch advancement
is the next controller edge.

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

The target branch-search API must report only global bounds after a split. For
each requested node, it will take the hull of the proved interval over every
live, completed, and pending leaf; an unexplored child must contribute at least
its inherited ancestor facts, never the tighter state of its sibling. That
partial-tree hull and its proof are not implemented by the current public
`interval_bound`: today that command runs only the supported direct-forward
derivation and prints its selected cuts as diagnostics. The retained-tree
proof fold implemented below closes a target only when every leaf is a checked
target or refutation; it rejects unknown leaves rather than manufacturing a
global bound from them.

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

The tactic is the first client, not the only one. The numerical acceptance
programs and two downstream applications below constrain the framework without
requiring all of them to be implemented in the first release.

### Example-driven numerical roadmap

The small propagation canaries above are architectural tests, not the intended
ceiling of the numerical system. Development after the generic proof frontend
is driven by the following executable acceptance programs. A generic mechanism
is justified when one of these programs needs it; passing a synthetic rule test
alone is not completion.

#### Large-argument elementary functions

The first range-reduction targets are:

- prove `Real.sin 10 < 0` from a certified enclosure of `Real.sin 10`; and
- produce exact dyadic `lo` and `hi` with `0 < lo`,
  `Real.cos (10 ^ 10) ∈ [lo, hi]`, and `hi - lo ≤ 2 ^ (-80)`.

These examples must not reduce a floating-point approximation and then ask the
kernel to trust it. A function package combines a checked constant enclosure,
an exact integer or quadrant reduction, a small residual interval, and a local
enclosure theorem. The large reduction integer, the selected quadrant, and the
residual are explicit replay data. An off-by-one reduction candidate must be
rejected. The reduced argument of `cos (10 ^ 10)` is not especially close to
a quadrant boundary. Its purpose is the `2 ^ (-80)` output width: multiplying
the pi error by a reduction integer near `10 ^ 10` forces a substantially
higher-precision constant enclosure than quadrant selection alone.

Range reduction depends on a pluggable constant service rather than a pi
literal wired into the sine package. Its first serious provider uses a Machin-
style arctangent identity whose identity and alternating-series remainder can
be proved from elementary Mathlib analysis. A faster Chudnovsky provider
follows once the Ramanujan-type identity connecting its series to `Real.pi` is
formalized; checking only its term recurrence, finite sum, and tail would not
establish that identity. Registry selection, fallback, and agreement of these
independently produced enclosures are load-bearing. Before Chudnovsky is
available, conformance compares two independently proved Machin-style
identities. The acceptance target is a 1,000-bit pi enclosure; the engine may
cache and share it across every trigonometric node in a run.

The first proof-side range-reduction canary toward the smaller
`Real.sin 10 < 0` acceptance target produces that ordinary theorem without yet
passing through the interval tactic. Its executable, Mathlib-free certificate
names three provider choices: a rational constant enclosure, a combined
integer-half-turn/quadrant reduction, and a local sine method. A
Machin-owned replay theorem derives the coarse enclosure `3 < pi < 16/5`
directly from Machin's arctangent identity and elementary kernel proofs that
`x - x^3/3 < arctan x < x` for positive `x`. It deliberately does not consume
Mathlib's existing decimal pi bounds, which are proved by a different
square-root iteration. Range-reduction replay uses that enclosure to prove
`0 < 10 - 3*pi < pi` and records the exact periodic reconstruction. The local
sine replay sees only the reduced core interval, and final replay composes its
positive result with the recorded odd-half-turn sign. Provider replay still
authenticates the fixed Machin certificate, but reduction replay consumes its
proved enclosure without matching the provider identity. A bounded numeric
guard first limits every endpoint field to `32`, rejects zero denominators,
then checks by cross multiplication that `3 * upper ≤ 10 ≤ 4 * lower`; those
inequalities authenticate half-turn `3`. Reduction and local-method choices
remain exact fixed-canary guards. Endpoint mutations outside the adequacy
envelope, half-turns `2` or `4`, the wrong output sign, and the alternate local
method return no evidence. The resulting theorem is ordinary kernel evidence
and uses neither `native_decide` nor an unchecked arithmetic oracle.

This canary resolves the first architectural risk: a formula can in principle
own a checked constant enclosure strong enough to authenticate a reduction
integer. It does not yet demonstrate a replaceable-provider registry or the
general interval tactic. The orchestration is a fixed four-stage pipeline; the
input `10` is hardcoded on the proof side; the local step proves only a strict
sign and produces no endpoint enclosure; its rational certificate is exact
fixed data rather than output from a precision-parametric series evaluator.
The current minimal sign-fact lattice cannot express a strict-negative result,
and the current goal parser recognizes only fixed non-strict targets, so
routing this certificate through that frontend would falsely imply an
integration that has not landed. Those are the next integration boundaries.
The 1,000-bit provider and `cos (10^10)` remain acceptance targets, not
delivered claims.

A second, deliberately narrow endpoint canary closes the chronology/replay
part of that integration boundary. From the first canary it reuses only the
Machin-derived coarse pi enclosure. It replaces that canary's exact-match
certificate authentication with per-schema guards: every proof schema checks
its own exact graph, assumptions, proposed fact or edge, and replay body before
returning evidence. Its Mathlib-free fact type carries rational lower and upper
endpoints plus independent closure flags. The retained target fact is
`sin 10 ∈ [-1, 0)`. Independent executable packages install the coarse pi fact
`(3, 16/5)`, reduce to `10 - 3*pi ∈ (2/5, 1)`, establish the local fact
`sin (10 - 3*pi) ∈ (0, 1]`, and negate it to `[-1, 0)`. An
instantiation handler owned by the reduction package appends the negated
local-sine node and the periodicity equality. Generic equality contraction then
transports the endpoint fact to the original `sin 10` node. The retained
chronology records, in order, the constant, reduction, local-sine,
instantiation, negation, and transport events, including exact input versions
and exact replay bodies.

The same six-event trace passes through the generic proof registry and
`ProofFrontend`. Constant, reduction, local-sine, instantiation, negation, and
equality schemas own their mathematical replay; the frontend contains no
function-specific case. Closing the extended graph back to the original graph
produces the ordinary theorem `-1 ≤ sin 10 ∧ sin 10 < 0`, with the standard
`#print axioms` guard and no `native_decide`, `sorry`, or new axiom.

This remains a fixed-data orchestration experiment, not a general interval
implementation. It deliberately reuses the D2 `Rational.Raw` certificate
representation because the exact Machin endpoints `16/5` and `2/5` are not
dyadic; its decoder accepts only top and four fixed endpoint facts, all of whose
denominators are nonzero. The source operation is proof-side constrained to the
hardcoded value `10`; there is no goal reifier for this endpoint fact, no
precision-parametric endpoint computation, no alternative provider whose
selection or fallback is exercised, and no general interval intersection. The
partial fact domain supports identical facts and top as an intersection
identity, and rejects other pairs as malformed. The canary uses a first-offer,
category-major controller; it does not claim that policy is the production
search policy. Its reduction and replay hardcode the half-turn count `3`; no
range-reduction choice is computed. The declared limits are an exact-fit
resource envelope for this retained run (five operations, six nodes, one
generated instance, one equality, and maximum node depth three), not evidence
that the controller succeeds under a general resource policy. General
open/closed/unbounded interval arithmetic, provider competition,
range-reduction selection, and computed local enclosures remain acceptance
work.

A fixed huge-argument cosine canary now establishes the ordinary theorem
`0 < Real.cos (10^10)` through the same generic package/session/proof frontend.
Its Mathlib-free reduction payload carries the exact odd quotient
`3183098861` and the rational residual window
`13/5 < 10^10 - 3183098861*pi < 27/10`. Replay derives that window from a
strict 20-decimal pi enclosure, proves the reduced cosine negative, negates the
fact, and uses a package-owned periodicity equality to transport the positive
fact back to the original expression node. The retained chronology contains
separate constant, reduction, local-cosine, negation, equality-only
instantiation, and transport events. Mutations with an off-by-one quotient or
a changed residual endpoint remain structurally decodable payloads but are
rejected by semantic replay, so both large-integer reduction fields are
load-bearing. Constant replay consumes a provider-agnostic enclosure claim;
the retained provider discharges it with Mathlib's independently proved
20-decimal pi bounds.

This is a sign canary, not the stronger huge-argument enclosure acceptance
target. The source value, quotient, residual endpoints, local sign rule, and
controller are fixed fixture data. The runtime does not compute a reduction
integer, refine the residual, select among competing constant providers, or
produce an 80-bit cosine enclosure. The 1,000-bit package-owned pi provider,
general huge-argument range reduction, and the exact-dyadic
`0 < lo ≤ Real.cos (10^10) ≤ hi` result with width at most `2^(-80)`
therefore remain acceptance work.

#### Series as package-owned numerical algorithms

A registered function may supply a power or Taylor series without teaching the
engine that function. The generic series interface carries a center, exact
coefficient recipe or recurrence, an admissible input region, a truncation
degree, and a theorem bounding the remainder. Replay proves the finite
polynomial enclosure and adds the remainder interval. Different formulas for
one function are ordinary competing providers selected by policy and checked
by their own theorems.

The first precision canary computes `Real.exp (1 / 8)` in an interval of width
at most `2 ^ (-100)` using the usual exponential series. It is followed by a
formula whose coefficients are not built into the interval library, proving
that the interface is genuinely package-owned. Increasing requested precision
must extend or refine cached series work rather than restart an unrelated
generic expression search.

#### Reusable exponential tails

The first source-pinned large-negative exponential probe covers PNT+'s
`LogTables.exp_neg_lt_1e_neg_100`. Its Mathlib-free package watches the fact
that an exponential input is at most `-231` and emits a package-owned recipe
containing the reduction point `231`, decimal exponent `100`, and outward
point enclosure `46/125` for `exp (-1)`. The companion checks
`exp (-231) = exp (-1)^231`, compares `(46/125)^231` with the exact rational
`1 / 10^100`, and reuses that boundary by monotonicity. Generic chronology
quotation and `ProofFrontend` replay then close both the boundary leaf
`exp (-231) < 1e-100` and the reusable theorem
`231 ≤ x → exp (-x) < 1e-100`.

The scientific literal is proved equal to `1 / 10^100`; it is never treated
as floating-point data. Replacing `231` by `230` is rejected twice: the
planner and replay schema refuse the incompatible input/certificate, and a
kernel theorem using a lower enclosure of `exp (-1)` proves the mutated
numerical claim false. Although the recipe has four named fields, its current
decoder accepts only the pinned constants `[231, 100, 46, 125]`; those fields
are not general checked parameters. This is evidence for one reusable
range-reduction route, not the general exponential implementation. The finite
fact lattice, fixed power, fixed point enclosure, and exact certificate body
remain local to the probe. Precision-parametric point evaluation, repeated
halving/squaring, provider selection, cached powers, and the package-owned
Taylor-series canary above remain acceptance work.

#### Source-pinned BKLNW power fold

The first certified-bound dependency probe replaces PNT+
`BKLNW_a2_bounds.lean:cert_pow433_upper`, specifically its use of
`LeanCert.CertifiedBounds.BKLNW.pow433_upper`. The Mathlib-free package
retains eight authenticated natural atoms: the upper limit `433`, structural
coordinates `4` and `5`, dyadic exponents `36` and `57`, exact tail
cardinality `429`, and numerator/denominator of the provider cut. The limit,
exponents, cardinality, and cut are load-bearing in the proof; the split
coordinates are pinned structural metadata for this fixed operation. Its checker
authenticates those coordinates, exponent inequalities, exact count,
the complete rational product inequality, and containment in the source
target before emitting one fact. The declared arithmetic work is the 429-term
tail represented by that analytic fold; the payload is bounded to eight atoms
and one retained entry.

The Mathlib companion proves a parameterized two-band fold theorem over the
actual `Finset.Icc 3 M` source sum. It proves the logarithmic floor at `2^M`,
evaluates the `k = 3` term, isolates `k = 4`, and uniformly bounds every
`k ≥ 5` term. Generic chronology and frontend replay close the exact PNT+
decimal inequality as an ordinary theorem. Mutated source limit, tail count,
dyadic exponent, and endpoint records decode structurally but fail validation,
planning, and replay; the smaller endpoint is independently proved false.

The complete source-pinned power ladder now adds limits `29`, `37`, `44`,
`51`, `58`, `63`, `145`, `217`, `289`, and `361` through one second schema.
Its package-owned table gives checked eight-decimal upper bounds for
`2^(1/k - 1/3)`, `4 ≤ k ≤ 21`; each decimal follows from the checked
20-digit `log 2` series window and an ordinary exponential remainder theorem.
The reusable fold handles `k = 4..20` separately and uses the `k = 21` base
for the authenticated remaining cardinality. Runtime acceptance authenticates
the exact source-row limit/endpoint lookup together with the split coordinates,
table denominator, and cardinality. Its Boolean validity test also evaluates
the complete all-natural inequality for that fixed row; the kernel soundness
theorem consumes the corresponding proposition to prove the rational bound.
Cross-row replay and reachable source/metadata mutations reject, and an
endpoint-at-one mutation is independently proved false; the mutation suite
does not claim to isolate the final inequality conjunct because exact row
lookup already pins its endpoint. For these fixed records the declared
observation budget is
`18M`, matching the 18 table bases raised to the selected limit, and the
payload atom bound is raised only to the selected source numerator (the
`M = 289` endpoint is the largest). These are explicit per-request bounds,
not a claim of input-independent constant work.

The same direct-interface migration covers the 22 declarations (eleven
lower/upper pairs) `a2_*_exp_lower/upper` at arguments 20,
25, 30, 35, 40, 43, 100, 150, 200, 250, and 300. One parameterized certificate
authenticates the exact source row, logarithmic floor, lower and upper target,
twelve-decimal base-table scale, explicit band through 63, and any tail from
64 onward. The companion kernel proof derives the floor from the package log-2
series, checks all 61 exponential bases by Taylor remainder, folds both bands,
and bounds the high-row tail by monotonicity. Generic planning and replay emit
one two-sided window; cross-row and structural mutations reject, while false
lower and upper endpoint mutations have independent ordinary refutations.

Consequently all eleven power declarations and all 22 exponential declarations
actually used by pinned `BKLNW_a2_bounds.lean` have ordinary-kernel Hex
replacements.
The inventory classifies that imported role as accepted after a localized PNT+
rewrite, not as LeanCert namespace or drop-in API compatibility. This remains
a fixed-source acceptance provider: arbitrary arguments, caller-supplied base
precision, incremental/chunked folds, caching, a big-integer complexity model,
and production balanced-tree scaling evidence are still future work. The
separate 128 BKLNW tactic occurrences and Table 10 workload are not implied by
this interface result.

#### Coordinate-pinned BKLNW Table 10 shard

The first Table 10 canary pins the shared source row

```text
(25, 1.8251e-4, 4.5626e-3, 1.1407e-1, 2.8516e0, 7.1291e1)
```

at PNT+ revision `21998bb6196b56789f72a52656a781a75e134eb0`.
The five coordinates correspond to
`BKLNW_table10_rows_20_43.lean:table_10_row25_k1_margin` through
`table_10_row25_k5_margin`; each source conclusion is
`B_8_exact k 25 26 ≤ listed_k * table_10_margin`, with
`table_10_margin = 1.002001`.

The exact consumer shape is
`BKLNW_table10_dispatch.lean:bklnw_table_10_verification`: it assumes
`(b, B 1, B 2, B 3, B 4, B 5) ∈ table_10` and quantifies
`k ∈ Finset.Icc 1 5`. The proof-side `sourceTable` copies the exact row-25
tuple, and `row25OfMem` preserves those membership and finite-column
hypotheses for the checked numeric majorant conclusion. The surrounding
`B_8_exact` reduction remains the explicit localized PNT+ rewrite boundary.

One bounded Mathlib-free row action authenticates the adjacent rows `25` and
`26`, the coefficient bounds `1.00000002`, `1.2196`, and `3.5032e-6`, four
source exponential windows, and all five listed/corrected coordinates. Exact
rational endpoint arithmetic must pass before a single payload produces five
facts. The Mathlib companion proves convexity of the `k = 1` majorant and one
parameterized `k = m + 2`, `m ≤ 3`, family for the other columns. Generic
chronology/schema replay and `ProofFrontend` close every coordinate as an
ordinary kernel theorem. This is a reusable shared-row mechanism, not five
copied row proofs.

The pinned source explicitly records that the bare row-25/column-5 endpoint
claim is false: its comment gives `G₅(25) = 71.2922 > 71.291`, so the theorem
uses the safety margin. A payload which changes only that target back to the
listed `71.291` remains structurally decodable but fails with coordinate code
`205`, retains no draft, and cannot become a precision retry. An independent
kernel lower bound proves `¬ majorant 5 25 ≤ 71.291`.

This shard accepts only the five numeric majorant leaves for row 25 after a
localized PNT+ rewrite to the source-shaped numeric bridge. It does not import
or wrap LeanCert, and by itself stops before the surrounding PNT+
`B_8_exact` reduction; the shared exact bridge below supplies that reduction.
The generated inventory's count of 87 is executable target tactic
occurrences, not 87 distinct row/column declarations; the next batch below
records coverage at both levels.

#### Parameterized Table 10 convex-row batch

The next bounded package pins the six source tuples at
`BKLNW_tables.lean:833–838`, with row intervals `60–65`, `65–70`, `70–75`,
`75–80`, `80–85`, and `85–90`. These are the largest contiguous source batch
sharing exactly the `row_bound_k1` / `row_bound_kge2` / `row_bound_k5`
convex-endpoint reduction and the fixed `a₁ = 1.00000002` bound. One payload
authenticates all six rows in order, their row-specific `a₂` and epsilon
bounds, thirty exact listed/corrected cells, and sixty rational endpoint
inequalities based on the checked decimal upper bounds for `exp (-1/2)` and
`exp (-2/3)`.

One generic operation installs thirty coordinate facts. The Mathlib companion
lifts each accepted rational endpoint through the exponential bounds, uses the
shared convexity theorem for columns 1 through 5, and exposes `rowOfMem` with
the pinned tuple-membership and `k ∈ Finset.Icc 1 5` hypotheses. Generic
chronology/schema replay and `ProofFrontend` close all thirty facts. A false
row-75/column-3 endpoint, a duplicated row-80 column, and a cross-row reorder
are decoded and rejected without drafts or a retry.

This replaces, after localized PNT+ majorant rewrites, the 30 margin
declarations for rows 60–85 and their 60 executable endpoint tactic calls. The
row-60 margin result is stronger than the separate bare `table_10_row60_k5`
target and also replaces its two endpoint calls, so this batch covers 62 of
the inventory's 87 target occurrences.

#### Parameterized Table 10 pointwise-row batch

The late-range pointwise package pins the two source tuples at
`BKLNW_tables.lean:839–840` and the ten declarations
`table_10_row90_k1_margin` through `table_10_row95_k5_margin` in
`BKLNW_table10_rows_90_95.lean`. Each declaration uses the same
`row_bound_pointwise` reduction and has one numeric premise

```text
A₁ * b' ^ k * exp (-(b / 2)) +
  A₂ * b' ^ k * exp (-(2 * b / 3)) + E * b' ^ k ≤ listed * 1.002001.
```

One bounded payload authenticates both rows in order, `b`, `b'`, `A₁`, `A₂`,
`E`, the ten listed/corrected coordinates, and the ten exact-rational
majorants. The Mathlib companion reuses the kernel proofs that
`exp (-1/2) < 0.606530660` and `exp (-2/3) < 0.513417120`, lifts their powers,
and proves the complete numeric premise. `rowOfMem` retains exact source tuple
membership and `k ∈ Finset.Icc 1 5`; generic chronology/schema replay and
`ProofFrontend` close every installed fact. A bare-target mutation, duplicated
column, cross-row reorder, and wrong replay target all reject without a draft
or precision retry. The kernel also proves that the rational majorant for the
bare row-90/k=1 target is strictly too large.

#### Large-decimal Table 10 pointwise row

The next fixed package covers all five margin declarations for source row
`13800.7464` in `BKLNW_table10_rows_regime3_12600_24000.lean`. It
authenticates the exact fixed-point row, upper endpoint `14000`, coefficients
`A₁ = 2`, `A₂ = 19913`, `E = 2.5423e-35`, the shared tail `1e-100`, and all
five source coordinates at `BKLNW_tables.lean:1067`. The rational checker uses
the same pointwise formula as rows 90/95, but avoids constructing powers with
13,800-digit exponents.

The Mathlib companion reuses the ordinary-kernel theorem behind the existing
PNT exponential-tail canary: both exponential arguments are at most `-231`,
so each exponential is strictly below the authenticated `1e-100` tail. The
five resulting rational premises are replayed through the generic frontend
and exposed through an exact tuple-membership `rowOfMem`. Bare-target,
wrong-column, wrong fixed-point row, and wrong replay-target mutations reject
without a retained draft or precision retry; the bare rational-majorant
failure is also an ordinary theorem.

#### Coupled logarithmic Table 10 transition

The final target-numeric package pins the consecutive source tuples at
`BKLNW_tables.lean:815–816`, the ten margin declarations split between
`BKLNW_table10_rows_20_43.lean:table_10_row43_k1_margin` through
`table_10_row43_k5_margin` and
`BKLNW_table10_rows_misc.lean:table_10_row19log10_k1_margin` through
`table_10_row19log10_k5_margin`, and the separate tighter source theorem
`table_10_row43_k5`. Their real intervals are
`43 → 19 * log 10` and `19 * log 10 → 44`.

One bounded Mathlib-free payload authenticates both source rows in order,
their coefficients and ten listed/corrected coordinates, the tighter
row-43/column-5 target `3.1563`, the integer-endpoint exponential bases, the
shared upper point `43.75`, and the two logarithmic endpoint tails `3.17e-10`
and `2.16e-13`. Every field participates in the rational endpoint checks and
exact source-payload equality. The Mathlib
companion independently proves `2.3025850924 < log 10 < 2.302585094` from a
finite logarithm series, derives the row chronology and `19 * log 10 ≤ 43.75`,
and proves both tail inequalities through exact real-power identities and a
kernel-checked power comparison. Convexity then covers both complete real
intervals; generic package chronology, replay, and `ProofFrontend` close all
ten margin facts. The same checked endpoints feed a narrow ordinary-kernel
adapter that reproduces the source's strictly tighter
`B_8_exact 5 43 (19 * log 10) ≤ 3.1563` theorem.

Bare-target, false-coordinate, cross-row chronology, exponential-base,
log-endpoint, and both tail mutations remain decodable but produce no draft
or retry. In particular, lowering the separate `3.1563` certificate below its
rational endpoint is rejected. The uncorrected row-43 first target is
separately refuted in the kernel. The runtime row tag `19010` is only a
bounded decoder code; the proof side source tuple uses the exact real abscissa
`19 * log 10`.

#### Supporting Table 10 `a₂` batch

The 38 supporting declarations are exactly `row21_a2_le` through
`row24_a2_le` and `row26_a2_le` through `row59_a2_le` in the pinned
`BKLNW_table10_rows_20_43.lean` and
`BKLNW_table10_rows_44_59.lean`. They are one coherent source family: each
uses `a2_mid_le` with a row-specific integer `b`, authenticated
`K = ⌊b / log 2⌋₊`, and rational upper target. Rows 20 and 25 use the
separate certified `a2_*_mem_Icc` route and are not included in this count.

The Mathlib-free `PntTable10A2` package accepts one of 38 exact source records.
Its payload carries the argument, floor, target numerator/denominator,
two-sided 20-decimal log window, and exponential-table scale. The natural
checker verifies both floor inequalities and a complete rational
head-plus-tail majorant before proposing one upper fact. All source records
use the same bounded operation, plan, decoder, and replay format.

The Mathlib companion copies the exact unfolded shape of
`Inputs.default.a₂`, proves the finite `f (exp b)` identity, and independently
bounds the second `max` branch `f (2^(K+1))`. It then bounds terms `4,…,12`
with the package-owned exponential base table and all terms `13,…,K+1` by
the term at 13. This proof consumes no Table 10 target-coordinate theorem, so
the supporting layer is not circular. `rowOfMem` gives one source-dispatch
theorem for all 38 records, and a row-21 instance closes through generic
chronology and `ProofFrontend`.

Wrong source, argument, floor, log endpoints/scale, table scale, and false
endpoint payloads decode but fail without drafts; cross-row replay rejects.
The false endpoint also has an ordinary-kernel refutation. The retained work
charge counts ten table powers per row but is not a big-integer complexity or
production throughput claim.

After localized PNT+ rewrites, the coordinate-pinned providers cover all 87
executable Table 10 target calls and the supporting provider covers all 38
`a₂` calls. `PntTable10Exact` supplies the remaining reusable analytic
bridge: `exactBound_eq_sourceSum` pins its supremum to unfolded PNT+
`B_8_exact`, `exactBound_le_of_majorant` handles the full-interval providers,
and `exactBound_le_of_pointwise` handles the late-row one-point reductions.
Source-pinned adapters retain row membership, column membership, chronology,
and PNT+'s three coefficient hypotheses while consuming the checked numeric
facts. The 87 target calls occur in 54 margin theorems and two bare helper
theorems. The row-43 bare statement is replaced at its original `3.1563`
endpoint by the tighter adapter; the row-60 bare statement follows from the
provider's stronger margin result. Thus both source theorem statements are
preserved while PNT+ replaces the 125 tactic calls locally and leaves the
287-row/five-column dispatcher unchanged.

The exact pinned Table 10 interface is therefore accepted after rewrite. This
does not claim a LeanCert compatibility layer, arbitrary caller-supplied table
generation, or production-scale performance for tables beyond the pinned
source.

#### Coordinate-aware numerical batches

The first source-pinned batch probe targets PNT+'s
`BKLNW.table_12_check`. At the pinned source revision, that theorem takes nine
real row fields plus membership in the 26-row `table_12` list and returns the
conjunction of the five bounds
`b ^ k * C_bk_S b c C ≤ Cb_k`, for `k = 1, …, 5`. Its ordinary-row tactic
site expands to 24 rows by five columns (120 numerical leaves), while two
logarithmic-row tactic sites each expand to five more leaves, for exactly 130
checks.

The numerical expression is pinned exactly, rather than reconstructed from the
paper prose. The source definition is:

```lean
noncomputable def C_bk_S (b c C : ℝ) : ℝ :=
  (C + 1) * exp (-b / 2) + RS_prime.c₀ * exp (-2 * b / 3)
    + c * exp (-3 * b / 4) + RS_prime.c₀ * exp (-4 * b / 5)
```

The representative source tuple is exactly:

```lean
(25, 1.750020e-4, 4.375050e-3, 1.093770e-1, 2.734410e0,
  6.836010e1, 0.88, 0.86, 32e12)
```

Consequently its first coefficient is `C + 1 = 0.86 + 1 = 1.86`; the other
coefficients are the tuple's `c = 0.88` and the pinned
`RS_prime.c₀ = 1.03883`. Both the proof definition and a kernel-checked
certificate-correspondence theorem record these equalities.

The retained mutation fixture proves the five cells of the ordinary `b = 25`
row. Five cell nodes are arguments to one row anchor, allowing one provider
action to install all five facts from one payload. The anchor result is only a
row token: actual sharing is in that single action and payload, and in the proof
theorem that computes the four point enclosures, natural powers, and row sum
once before exact rational projection into five targets. The retained
chronology contains five fact events sharing the same replay body, and the
generic proof frontend folds that chronology once before closing each
coordinate.

The row certificate's fields are pinned constants rather than general checked
parameters: its decoder accepts only the corrected source row. The original
paper value `6.65350e1` at `(b = 25, k = 5)`, instead of the corrected
`6.836010e1`, is a distinguished incompatible payload. Planning returns the
stable coordinate diagnostic `205`, which decodes to `(25, 5)`, emits no
draft, and does not request more precision; replay rejects the mutation, and a
separate lower enclosure proves that target false.

The generated ordinary-row extension covers the other 23 integer rows. A
package-owned `ordinaryRows` table contains their exact nine-field source
tuples; a kernel theorem equates every stored rational to the corresponding
scientific literal, including the source-only `M` fields. Flattening the table
produces 115 coordinate-bearing upper cuts and a single 391-atom authenticated
payload. One explicitly bounded action of arity 115 installs those cuts, whose
stable coordinates run from `(20,1)` through `(43,5)` with row 25 omitted. Its
resource envelope therefore states 116 nodes, 115 candidates and accepted
facts, one action, one retained payload entry, and bounded arena capacities
for the 115 shared payload references and exact scientific-decimal identity
fields. This is an acceptance-sized maximum chunk, not a proposed production
chunk policy.

The source's ordinary row 31 deliberately ends in the same three bounds as
the following logarithmic row: `1.034630e-2`, `3.217360e-1`, and
`1.000500e1`. The certificate preserves those exact pinned bounds even though
tighter values can be reconstructed for integer `b = 31`.

The proof is data-driven rather than 23 bespoke copies. Four Taylor point
windows are proved once at `-1/2`, `-2/3`, `-3/4`, and `-4/5`; a uniform
natural-power theorem supplies each positive integer row; and exact rational
checks discharge each row's five projections. One indexed replay schema uses
the coordinate's position in the authenticated table. The retained runtime
produces exactly 115 fact events, and one generic `ProofFrontend` fold is
required to close every coordinate. Representative first, middle, and last
closures are additionally retained as typed kernel-checked evidence. An honest
total meet compares the exact nonnegative rational cuts, including combinations
the retained chronology does not reach; equal cuts with different diagnostic
coordinates do not count as an improvement.

The two logarithmic certificates complete the remaining ten cells. Exact input
facts for `5e10` and `32e12` produce checked windows
`[24.6352888, 24.6352889]` and `[31.0967570, 31.0967571]`. The proof derives
`log 5` from a finite Mercator `log (1 - x)` series remainder at `x = 4/5`,
combines that result with checked
`log 2` bounds through the identities `log (5e10) = 10 log 2 + 11 log 5` and
`log (32e12) = 17 log 2 + 12 log 5`, and then uses fractional range reduction
about integer floors 24 and 31 for the exponential terms. Each five-cell row
action has its own checked log window as a replay assumption, so the dependency
is load-bearing rather than a separate bespoke numerical proof.

The logarithmic runtime has four actions, twelve chronological facts, and two
shared row payloads. One generic proof-frontend fold closes all ten coordinate
targets, with typed evidence retained at the first and last coordinates. The
exact 26-tuple `sourceTable12` is copied from the pinned source and a kernel
theorem equates it with the interleaved ordinary, row-25, and logarithmic
certificate list. The final theorem accepts an arbitrary nine-tuple membership
hypothesis and returns the source-shaped five-way conjunction. Thus the family
is accepted after rewrite with honest 130/130 coverage.

A zero cut at logarithmic coordinate `(log (5e10), 1)` is rejected as stable
diagnostic `401`, with no draft or precision retry; the replay format rejects
the mutated body and a kernel theorem proves the proposed inequality false.
These are still pinned fixed-row certificates, not a general logarithm or batch
API.

#### Generated FKS2 batch profiles

The generated-table scale probe carries all 1,000 cells of pinned PNT+
`Table4ExtData_11.lean`, from `b = 11010` through `b' = 12050`. The final ten
cells use width five, so the table and checker do not assume unit-width cells.
Its Mathlib-free `checkCell` is a package-owned exact-rational predicate, not
LeanCert's source predicate: it checks positive error, ordered square-root
endpoints, a 128-way reduced exponential argument, and the final rational
Taylor enclosure. Seven squarings compute the 128th power.

One 1,000-argument operation shares the row of margin facts. Fifty bounded
actions each install one twenty-cell chunk, retaining fifty payloads and 1,000
chronological facts. The exact resource envelope permits 1,001 nodes, fifty
rules/applications/actions, twenty candidates per outcome, 8,000 actual
payload cells under an 8,192-cell cap, 65,536 policy traversals, and payload
atoms at most `10^38`. A failed cell reports its source `b` coordinate before
payload allocation and does not trigger a precision retry.

The merge-gating fixture remains a bounded batching experiment, not a general
FKS2 table service. Direct indexed schema replay is retained for representative
chunks; proof registry emission metadata and a generic large-payload
`ProofFrontend` fold remain outside this acceptance fixture.

The separate full-family local/release profile extends the same provider to all
13,590 tuples in the fourteen pinned source shards. Thirteen generated data and
proof modules complement the retained shard-11 module. Each generated kernel
wrapper proves one complete source shard through ten- or twenty-cell proof
chunks; a fourteen-way fold then exposes `allCells_checked` and arbitrary
membership without one theorem per literal. Every source `cells_*_checked`
declaration therefore has a source-shaped package-owned replacement.
This substitutes the package-owned `checkCell` for upstream
`Table4ExtCore.checkCell`; it requires a localized PNT+ rewrite and is not a
literal reproof or LeanCert-compatible API.

Runtime uses 680 actions of at most twenty cells over one 13,590-argument
operation. Each payload contains one shard identifier and at most 160 cell
atoms. The explicit envelope permits 14,000 nodes and accepted facts, 700
rules/applications/actions and payload entries, 2,048 registry entries, twenty
candidates and drafts per reply, 161 cells per draft, and 110,000 aggregate
payload cells; the measured run retains 109,400. Stable diagnostics encode the
pair `(shard, b)` with radix 100,000. Cross-shard payload substitution fails
closed, and a false shard-00 cell reports `(0, 10)` before allocation with no
retry.

The complete campaign is the non-default `hex_interval_pnt_fks2_local` Lake
target, invoked fail-closed by
`scripts/conformance/run_pnt_fks2_family.sh`. The committed Mathlib-free family
data and checker remain in merge-gating `HexIntervalExperiment`; the thirteen
full-family Mathlib proof wrappers, aggregate proof, and complete conformance
driver belong only to non-default `HexIntervalPntFks2Local` and the local
executable, not `HexIntervalMathlibExperiment` or `HexConformance`. On the
shared 96-core development host, eleven uncached proof shards plus the
aggregate built in 226 seconds; the eleven simultaneous Lean processes peaked
at roughly 42 GiB in aggregate. Separately, shard 00 and shard 13 took 183 and
101 seconds. The full 680-action runtime and 13,590-event trace then elaborated
in 122 seconds. These measurements justify the separate local/release profile
and are observations, not stable budgets.

#### Bounded Chebyshev fold profile

The pinned PNT+ medium-range theorem keeps its exact real statement
`0 < x → x ≤ 11723 → ψ x ≤ 1.11 * x`. Its localized Hex rewrite
replaces the `native_decide` checker with a package-owned positive-integer
logarithm enclosure, bounded primality classifier, exact prime-power table,
and natural-number von Mangoldt fold. The logarithm provider reduces by a
power of two and proves a two-term atanh enclosure with an exact geometric
remainder before one upward rounding to tenths.

The 11,723-coordinate fold is replayed by 46 ordinary-kernel certificates of
at most 256 coordinates, joined sequentially by one structural prefix theorem.
This chunk bound is the retained resource boundary; it avoids a monolithic
proof term while preserving every coordinate inequality. Composite-as-prime
and wrong-prime-power-base mutations are rejected at their exact coordinates
without a precision retry.

This is a proof-side bounded campaign, not a retained runtime action or a
generic `ProofFrontend` fold. It accepts only PNT+'s `allChecks_11723` site
after a localized predicate rewrite. The shared Chebyshev import and interface
remain pending because the FKS2-floor and Ramanujan developments also consume
distinct theta-bound checkers.

#### Certified logarithm tables

The initial source-pinned PNT+ probe is intentionally narrower than this
table-building target. A Mathlib-free package recognizes the exact input fact
for `2` and emits a package-owned opaque fact through the generic policy
session. Its Mathlib companion interprets that fact as PNT+'s six-decimal
two-sided `log 2` window and replays the event from stronger existing Mathlib
point bounds. This validates exact-input dependency, package-owned fact replay,
and ordinary theorem closure. It is not a generic logarithm propagator, does
not compute a series, and does not satisfy any of the precision, batching,
ordering, or cache requirements below.

The source-pinned `log (log 6.58)` probe extends this boundary to genuine
two-stage replay.  One registered package first turns the exact rational input
fact into a strict positive enclosure for the inner logarithm, then runs again
and consumes that exact enclosure to derive the outer lower bound.  The two
events are replayed chronologically through the generic proof frontend; an
inner enclosure that includes zero is domain-unknown and cannot replay the
outer event.  The package's executable table is still finite, however.  The
Mathlib companion validates its entries with a general logarithm Taylor
remainder theorem, but the runtime does not yet provide arbitrary-rational
range reduction, series construction, or precision refinement.

The next fixed-source provider covers all twelve remaining natural-number rows
of pinned PNT+ `LogTables.lean`: the two-sided six-decimal bounds for
`3, 5, 7, 10, 11, 13, 17, 19, 23, 29, 30, 32`.  One bounded Mathlib-free
schema authenticates the exact input, dyadic shift, reduced atanh parameter,
eight-term count, decimal scale, and both endpoints.  The companion checks the
range-reduction identity, a finite atanh lower sum, an explicit geometric tail,
and the required `log 2` contribution before exporting the 24 source-shaped
ordinary theorems.  The representative row-29 result is also produced through
generic planning, payload authentication, chronology, and `ProofFrontend`,
while conformance executes the same runtime schema for every row.

Wrong reductions and insufficient term counts fail decoding; source, cross-row,
window, and false-endpoint mutations fail replay, and the false endpoint has an
ordinary mathematical refutation.  This accepts exactly those 24 source tactic
sites after localized rewrites.  It is not a general logarithm rule or a claim
about all of `LogTables.lean`: arbitrary inputs, requested precision, generated
endpoints, caching, persistence, and batch-performance evidence remain future.

The rational-logarithm companion applies the same proof architecture to the
largest coherent remaining direct-log family: fifteen exact positive rational
inputs supporting seventeen pinned source declarations. The Mathlib-free
runtime authenticates the source coordinate, numerator and denominator,
dyadic shift, reduced atanh parameter, eight-term count, scale, and both
endpoints. The semantic theorem checks the reduction identity, finite lower
sum, geometric tail, and `log 2` contribution, then exports every source
statement at its original strength. All fifteen rows execute through the
bounded package, while the tight large-shift `32e12` row traverses generic
chronology and `ProofFrontend`.

Wrong inputs, shifts, term counts, coordinates, windows, and a mathematically
false endpoint fail closed. Acceptance is exact source-row lookup plus a
reusable kernel theorem, not arbitrary-rational runtime range reduction,
endpoint generation, or a LeanCert compatibility layer. This slice does not
import or rely on any admitted LeanCert-owned public bound.

The negative-exponential table provider covers the complete 79-declaration
Table-10 block `exp_neg_10_lt` through `exp_neg_200_lt` in the same pinned
source.  Every argument is authenticated as an integer number of sixths.  One
package-owned fourteen-term Taylor enclosure for `exp (-1/6)` is raised to the
recorded natural power, and an exact integer cross-product check authenticates
the source endpoint.  The runtime schema records the source coordinate,
argument, Taylor anchor, term count, and output cut; all 79 rows run through
the bounded package, while representative `exp_neg_70_3_lt` also traverses
chronological replay and `ProofFrontend`.

Unknown coordinates and mutations of the sixth count, term count, source row,
or endpoint fail closed.  This is a fixed source lookup plus a reusable kernel
power reduction, not arbitrary exponential interval evaluation, requested
precision, generated endpoints, or a LeanCert compatibility layer.

The exponential-point provider covers the other nine pinned exponential tactic
sites in `LogTables.lean`, including lower and upper small negative points, the
`x ≥ 50` decay boundary, `exp 1.112`, and the isolated `exp 2`, `exp 20`,
`exp 22`, and `exp (-13.5)` bounds. One schema authenticates a signed rational
source, a rational step in `[-1, 1]`, its natural multiplier, the side and
endpoint of a fourteen-term Taylor enclosure, and the final source cut. The
kernel theorem raises the checked step enclosure to the authenticated power;
the `x ≥ 50` wrapper then applies exponential monotonicity. All nine rows use
the same runtime and proof theorem, while the tight forty-factor `exp 20` row
also traverses generic chronology and `ProofFrontend`.

Wrong sources, steps, powers, term counts, directions, cross-row cuts, and a
mathematically false endpoint fail closed. This is exact source lookup plus a
reusable rational Taylor/power certificate, not arbitrary exponential range
reduction or endpoint synthesis.

The final two nested-log sites use another genuine two-stage run of one generic
log package. The first event checks the strict positive enclosure
`0.6931471803 < log 2 < 0.6931471808`; the second consumes both endpoints in
two independent fourteen-term rational remainder checks and derives
`-0.366513 < log (log 2) < -0.366512`. A zero-touching inner enclosure is
domain-unknown, and wrong sources, bypassed inner facts, and wrong outer facts
cannot replay. Both original non-strict source statements follow from this
stronger ordinary theorem.

The final π site crosses a provider-agnostic constant-operation boundary. Its
Mathlib-free certificate authenticates the exact `315 / 100` upper cut; the
Mathlib companion replays `Real.pi_lt_d2` from
`Mathlib.Analysis.Real.Pi.Bounds`. That theorem has an ordinary axiom surface
and does not use the Chudnovsky development. Mathlib's Chudnovsky sum-to-`π⁻¹`
identity remains `proof_wanted` and is neither imported nor accepted as
evidence.

Thus all actual pinned PNT+ `LogTables.lean` tactic sites have accepted
localized rewrites or stronger replacement results. This is migration
coverage, not LeanCert API compatibility or an arbitrary-input transcendental
evaluator: row generation, requested precision outside the dedicated log-2
probe, caching, persistence, and performance at table scale remain future.

The first precision-indexed log provider moves beyond an opaque six-decimal
table fact. Its program contains separate exact-input and precision-request
nodes. The same Mathlib-free package accepts requests for 20 or 50 decimal
digits and selects 22 or 53 terms respectively. Each replay body authenticates
the requested precision, term count, both rational endpoints, and the exact
source fact for `2`. The proof companion instantiates Mathlib's two-sided
partial-sum bounds for
`1/2 * log ((1+x)/(1-x))` at `x = 1/3`, where the logarithm argument reduces
exactly to `2`. The certificate's recorded term count is the count supplied to
those bounds, so a certificate recording too few terms cannot prove its own
endpoints. A finite partial sum gives the lower bound and an explicit dominated
geometric tail gives the upper bound. Exact rational normalization proves a
strict interval of width `10^(-50)` around `Real.log 2`, and generic chronology
quotation plus `ProofFrontend` produces the ordinary theorem. Structurally
valid mutations with 52 rather than 53 terms, a changed endpoint, a mismatched
precision, or a non-`2` source assumption are rejected by semantic replay.

This remains a two-entry experimental provider, not a persistent table
service. The runtime selects already recorded rational certificates rather
than computing arbitrary endpoints, and there is no arbitrary rational input
reduction, adaptive term search, cross-request cache, serialized table,
257-entry batch, ordering proof, or performance result. Those remain part of
the full table-building acceptance target below.

The table-building acceptance program constructs enclosures for

`Real.log (1 + (i : ℝ) / 256)`, for every `i : ℕ` with `i ≤ 256`,

with width at most `2 ^ (-128)`. The table certificate binds the exact index,
exact rational argument, chosen range reduction, series data, and final
interval. It additionally proves monotonic ordering of adjacent entries. A
later `log` propagator may use the table for argument reduction, but every
lookup remains an ordinary replayable dependency rather than trusted generated
code.

Table construction is a first-class batch client: common constants,
coefficients, and remainder proofs are shared. The benchmark records total
integer work, proof size, cache reuse, and incremental cost when the requested
precision grows. Producing one correct entry 257 times independently does not
satisfy the table acceptance target.

#### Certified integral bounds

The first quadrature target proves the strict rational enclosure

`7468 / 10000 < ∫ x in 0..1, Real.exp (-(x ^ 2))`

and

`∫ x in 0..1, Real.exp (-(x ^ 2)) < 7469 / 10000`.

The executable planner may choose a partition and a quadrature or Taylor rule.
The proof package checks each local enclosure and its remainder theorem, then
adds the subinterval bounds exactly. Adaptive subdivision is driven by the
same policy observations as other refinement, but an integral certificate has
its own compositional theorem; sampling values is never evidence for an
integral bound. Polynomial integrands should use exact antiderivative or
polynomial-integration providers when available instead of being forced
through generic quadrature.

The first quadrature proof package lives in `HexIntervalMathlib`, which already
owns real-function semantics and imports Mathlib; it does not add a dependency
to Mathlib-free `HexInterval`. A general certified integrator with reusable
partition APIs remains a later downstream library with its own SPEC.

#### Specialized algebraic solvers before generic propagation

The generic interval engine is a coordinator and fallback, not a mandate to
solve every recognizable fragment by branch-and-contract. Hex already has
certified real and complex polynomial root-isolation engines. A provider may
recognize a closed univariate polynomial fragment with integer coefficients,
or rational coefficients that can be cleared with a proved nonzero scale,
reify it into the existing `Hex.ZPoly` representation, invoke the specialized
executable solver, and replay its existing certificate into interval facts,
disjoint cases, root counts, or refutations. Irrational, symbolic-coefficient,
and multivariate fragments decline this provider and remain with generic or
other specialized methods.

The initial integration targets are:

- use `HexRealRoots` to isolate the unique real root of `x ^ 5 - x - 1` and
  feed its isolating interval into the surrounding interval problem;
- use `HexRoots` to return a complete family of disjoint certified complex
  regions for `z ^ 5 - z + 1`; and
- solve a mixed problem in which real-root isolation supplies finitely many
  algebraic candidate intervals and arbitrary-function propagators, such as a
  sine or logarithm package, eliminate or refine those candidates.

For root counting, isolation, or a sign partition determined by the roots of a
supported univariate polynomial, the acceptance trace uses the specialized
provider and does not reproduce Sturm, Descartes, Pellet, Newton, or complex
argument-principle search as generic expression steps. A complete univariate
real-closed-field sentence should be sent by the caller to `hex-rcf`, which
already owns that end-to-end decision problem and may use real-root isolation
internally; this is usage precedence, not a dependency or dispatch edge from
the adapter. The adapter instead serves root-region fragments embedded in a
larger interval problem. Polynomial range bounds on boxes use the generic
Bernstein, centered, or Taylor-model portfolio unless they reduce to one of
those exact decision problems. Generic interval propagation remains
available around polynomial islands and as a bounded fallback when a
specialized provider declines. Provider choice cannot affect soundness: every
imported isolation is tied to the exact reified polynomial and a checked
squarefree or simple-root certificate, then replayed through the existing
`HexRealRootsMathlib` or `HexRootsMathlib` theorems.

The root-isolation adapter does not live in `HexInterval` or
`HexIntervalMathlib`: those libraries retain their present dependency order.
The planned Mathlib-facing `hex-interval-algebraic` integration library depends
on `hex-interval-mathlib`, `hex-real-roots-mathlib`, and
`hex-roots-mathlib`, registers the specialized providers, and translates their
results to interval facts and proof branches. This also prevents a generic
interval import from pulling in polynomial isolation machinery.

The same dispatch principle extends to other Hex libraries. Exact polynomial
factorization, real-closed-field procedures, and future specialized linear or
algebraic solvers should be preferred when their recognized fragment and
certificate language fit the goal. The interval engine composes their results;
it does not hide a slower duplicate implementation behind a uniform API.

#### Required provider boundaries

These examples require several independently registered numerical roles:

- constant providers, such as Machin and Chudnovsky pi enclosures;
- range-reduction providers for periodic and scale-reduced functions;
- local function enclosures, including Taylor or other convergent formulas;
- reusable certified table providers;
- quadrature and integral-remainder providers; and
- specialized algebraic solvers that return checked facts or branch families.

All providers are versioned, resource-bounded at their public boundary, and
replaceable. Their executable output is untrusted candidate data. Only exact
candidate data becomes a fact through a package-owned theorem, and `Evidence`
stores the resulting proof. Expensive provider internals may use compiled Lean
search code. An optional external program may
propose the same candidate only under the untrusted-dispatch contract in
Scope; this SPEC still approves no `@[extern]` planner hook. Rejection and
absence fall back without changing theorem statements.

The roadmap order is example-driven: large-argument sine and pluggable pi;
generic series and the high-precision log table; certified quadrature; real
and complex root-isolator dispatch; then mixed workloads combining several of
these providers. Verified raster and ODE clients below consume the same
capabilities rather than introducing private numerical engines.

In the companion development order, large-argument sine and the constant
provider refine D5-D7, with Chudnovsky a later stretch provider; the series and
log-table programs are D7-D8; the
selected PNT+ point, sum, and generated-table workloads are D8-D9; adaptive
quadrature and affine covers refine D9-D10; and root-isolator dispatch is a
separate integration provider after the root libraries. Surveyed PNT+
certified-bound and integral dependencies become milestone work only when a
migration workload selects them. This mapping keeps the dependency order
authoritative while the examples determine what each milestone must
demonstrate.

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
edges, `k` the number of registered operations, `q` the number of queued
candidates, and `b` the number of live branch states.

- `Program.check` is `O(n + e + k²)`: it checks the SSA nodes and edges and
  performs the current pairwise operation-key uniqueness check. Initial
  dependency construction is `O(n + e)`. `RuleRequest.accepts` deliberately
  revalidates the complete `ProgramView` per selected request, including depth
  reconstruction, so the current package-boundary dispatch performs this
  whole-program work before each callback.
- Dependency discovery for one changed fact visits only the rules attached to
  that node. The current decoded/reference state does **not** yet turn this
  semantic locality into a local mutation cost: every `Queue.enqueueWithin`,
  deactivation, and pop revalidates the complete dependency/dirty arrays and
  retained queue, including all watcher lists and `q` entries. Every accepted
  fact through `Branch.pushWithin` revalidates both base and current programs,
  reconstructs current facts and versions from the retained history, and
  checks the complete generation/depth tables; chronology append separately
  scans its retained order. Avoiding these whole-state scans is a requirement
  for the selected production store and queue, not a property of the current
  transparent reference builders.
- One supported `Search` transition first performs bounded prefix checks on
  every decoded list and O(1) size checks on every retained array, then validates
  the complete base/current branch chronology, registry, scoped bindings,
  offers, and actions. The current transparent reference contract therefore
  still has whole-branch/program/registry work; it does not claim local
  asymptotics. Within one `prepareWithin`, `chooseWithin`, `acceptWithin`, or
  `invokeWithin` call, that authentication and the package-owned policy
  measurements run once. Accepted callback batches fold already-preflighted
  exact successor updates without re-running `Branch.check` for every event.
  Split admission preflights every branch in the bounded retained frontier,
  then validates the popped parent and both children. With `f` pending leaves
  and branch validation cost `B`, its current transparent-reference cost is
  `O(f * B)`, plus bounded scope-uniqueness work; it is not one parent/child
  validation independent of frontier size. Arbitrary callback execution and
  equality on caller-selected facts, causes, identifiers, and keys
  remain non-preemptible.
- The current `Search.Result.Tree` reference builders validate the complete
  retained prefix before and after every split or settlement. If `N` nodes are
  retained incrementally and `B` is the bounded per-node branch/state
  validation cost, the repeated branch-validation term is `Θ(N² * B)`.
  The current pairwise retained-scope uniqueness scan adds `Θ(N³)` across
  the same incremental construction, for a combined `Θ(N² * B + N³)`
  reference cost. This is not an incremental tree-store bound. `maxNodes`
  therefore stays small and measurement-gated until a production
  representation avoids repeated full-prefix validation.
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

- `HexInterval/Basic.lean`: raw lower and upper cuts, comparison, and
  normalization.
- `HexInterval/Canonical.lean`: sealed canonical values, views, and
  resource-safe smart constructors.
- `HexInterval/Arithmetic.lean`: multiplication growth, direct-power
  retained-growth and exponent-work prerequisites, rational-backed precision
  prerequisites, and the dedicated regularization preflight metadata; it does
  not expose an interval operation.
- `HexInterval/Multiplication.lean`: resource-checked interval multiplication,
  unconditional extended-corner evaluation, attainment-aware extremum
  selection, and the sealed `mulWithin` entry point.
- `HexInterval/Interval.lean`: supported resource-safe intersection, hull,
  negation, addition, subtraction, minimum, maximum, absolute value, and
  natural power; outward regularization; transactional splitting; and checked
  precision-indexed reciprocal and first-slice division. Its public raw
  helpers, including the power, regularization, split, reciprocal, and division
  cut selectors, are decoder-level counterparts of checked operations. Useful
  bounded nonsingleton division remains future work.
- `HexIntervalMathlib/Interval.lean`: real-set semantics for the supported
  public construction, intersection, hull, and negation operations.
- `HexIntervalMathlib/Addition.lean`: exact summed-cut semantics and the
  successful addition image theorem.
- `HexIntervalMathlib/Subtraction.lean`: exact crossed-difference-cut semantics
  and the successful subtraction image theorem.
- `HexIntervalMathlib/MinMax.lean`: exact selected-cut semantics and one-way
  real-image enclosure theorems for minimum and maximum.
- `HexIntervalMathlib/Absolute.lean`: exact selected-cut semantics and the
  successful absolute-value image theorem, plus the raw one-way theorem
  `contains_absUnchecked` used by natural power.
- `HexIntervalMathlib/Multiplication.lean`: explicit selected-candidate-cut
  semantics and the one-way real-product enclosure theorem; it does not claim
  an image-tightness converse.
- `HexIntervalMathlib/Power.lean`: exact normalized selected-cut semantics and
  the one-way successful natural-power image theorem.
- `HexIntervalMathlib/Program.lean`: exact function-agnostic operation
  meanings, complete operation-array alignment, per-node SSA relations, and
  global model assembly over the supported decoded program.
- `HexIntervalMathlib/Proof.lean`: supported package-owned fact, equality,
  instance, refutation, and binary-cover theorem schemas; exact
  registry/action validation; chronological typed proof state and caller-target
  closure; separately authenticated retained-tree recipes; exact child seeding
  with one new branch assumption and derived inherited evidence; bounded
  target/refutation replay with unknown-leaf rejection and cover joins; and the
  expression boundary that rejects placeholders and metavariables, restores
  emitter environment/messages/information/metavariables and clears both
  environment-dependent elaborator caches, then transactionally runs
  `Meta.check` and exact type-definitional-equality checking in the caller's
  environment. Emitted terms may reference only declarations surviving that
  rollback. The kernel performs the final check when the caller installs the
  expression. Under
  ordinary imports, only `Registry.buildWithin` can construct the theorem
  registry; `import all HexIntervalMathlib.Proof` is a trusted-internals escape
  hatch rejected outside the exact empty repository allowlist. The built-in
  arithmetic package and direct-forward reifier/tactic are supported below;
  arbitrary-function packages, callback-to-tree-recipe orchestration,
  split-search tactic integration, and default registries remain experimental.
- `HexIntervalMathlib/Rule.lean`: the supported stable-key arithmetic package,
  exact real operation meanings, package-owned fact schemas, checked registry
  assembly, and state-to-proof quotation for negation, addition, subtraction,
  multiplication, natural power, absolute value, minimum, maximum, constants,
  reciprocal, division, and outward regularization. Every schema recomputes
  its fixed-resource public interval operation; decoded search results remain
  untrusted. One package `Config` supplies exactly one natural exponent and
  one dyadic constant, shared by every node at the corresponding built-in
  operation index; duplicate package registration and operation keys cannot
  add a second parameterization. Direct registry assembly does not preempt
  construction or equality of caller program/meaning arrays and therefore
  requires the supported search envelope for decoded inputs.
- `HexIntervalMathlib/Split.lean`: exact transactional child semantics,
  containment, coverage, disjointness, and left ownership of the cut point.
- `HexIntervalMathlib/Inverse.lean`: exact computed reciprocal-cut semantics
  and the one-way total-real-inverse connected-hull enclosure theorem.
- `HexIntervalMathlib/Division.lean`: exact computed first-slice quotient-cut
  semantics and the one-way total-real-division enclosure theorem.
- `HexIntervalMathlib/Regularize.lean`: exact normalized rounded-cut semantics,
  outward containment, and raw-cut idempotence without a grid-tightest claim.
- `HexIntervalMathlib/Frontend.lean`: bounded recursive arithmetic-term
  reification with structural sharing and stable-key resolution, checked
  node/term/root correspondence and exact source binding, derivation of the
  complete real `Program.Models` witness from caller source values, supported
  registry/flat-replay invocation, and programmatic lower, upper, conjunction,
  and closed-singleton equality closure about the evaluated target term.
  Search-to-recipe integration, Lean syntax, and Meta quotation remain outside
  this module.
- `HexIntervalMathlib/Tactic.lean`: exact runtime program/input/chronology
  construction and authentication, recursive forward-arithmetic expression
  and integer-cut parsing, reciprocal/division and automatic outward-
  regularization rows, independently checked caller-proof emission, and the
  current transactional bare `interval`, `interval?`, and `interval_bound`
  subset. `interval_bound` renders selected cuts as diagnostics; a noninteger
  dyadic endpoint is not pasteable into the current integer-only goal parser.
  Search-selected recipes, arbitrary functions, subdivision, and the
  expanded configuration syntax remain experimental or unimplemented.
- `HexInterval/Program.lean`: supported stable operation/domain/node
  identifiers, decoded typed SSA programs, fail-closed validation, and
  structural depths.
- `HexInterval/Fact.lean`: supported versioned fact snapshots, projected fact
  views, narrowing results, and the function-agnostic fact-domain interface.
- `HexInterval/Action.lean`: supported stable rule/action identities,
  registrations, scope bindings, validated immutable program/request views,
  and exact read/write projections. It has no callbacks, outcomes, policy, or
  proof evidence.
- `HexInterval/Trace.lean`: supported exact fact/instance chronology and
  bounded diagnostic-log contracts. Diagnostic bytes count retained `UInt8`
  payload cells after callback construction; they do not claim to preempt
  arbitrary Lean allocation.
- `HexInterval/State.lean`: supported immutable base and generated-node seeds,
  reconstructed current facts, exact version/provenance history, and bounded
  structural/generation side tables,
  dependency watchers, dirty bits, append-only work queues with policy
  tombstones, controller resources, and transactional checked builders. These
  decoded arrays do not select the optimized branch-storage implementation.
- `HexInterval/Policy.lean`: supported Mathlib-free scope and policy keys,
  generic bounded offer/view/decision/step/interface contracts, exact retained
  offer revalidation, and checked count/byte/pair/work/score admission. Concrete
  semantic offer keys and policies remain experimental; package measurement
  callbacks and equality on nested identifiers, keys, and reconstructed facts
  are explicitly non-preemptible.
- `HexInterval/Search.lean`: supported Mathlib-free sealed authenticated
  policy/action sessions, transactional callback-delta validation, exact
  generic stop/resource classes, stable depth-first/breadth-first frontiers,
  a separately sealed parent/depth/scope-checked leaf frontier, immutable parent
  restoration, sealed cumulative step/split/leaf/frontier/depth/scope
  accounting, and a sealed bounded retained result tree with exact single-delta
  child reconstruction and target/refute/unknown terminals. It contains no
  concrete callback, offer generator, semantic split/refutation theorem,
  policy algorithm, storage choice, proof recipe, or proof replay.
- `HexInterval/Experiment/Propagator.lean`: current experimental concrete
  applications, callbacks, outcomes, untrusted proposals and replies, and
  extension admission. Its engine extends and mutates only through the
  supported state/trace contracts, while its public record remains an
  inspectable experimental storage candidate.
- `HexInterval/Experiment/{PackageRegistry,PolicyDriver,PolicySession,
  StagedPolicy,AdaptivePolicy,FeaturePolicy,BranchTree}.lean`: current
   provisional package callback, policy implementation, semantic session,
   target driver, and split-construction designs. Optimized storage, concrete
   offer generation, package protocols, and a default policy will be selected
   from measurements; none is frozen by the decoded supported snapshots.
- `conformance/HexInterval/{Conformance,SearchConformance,MinMaxConformance,
  EmitFixtures}.lean`:
  Lean-only checks and oracle fixtures.
- `conformance/HexIntervalMathlib/ProgramProofConformance.lean`: supported
  program-model, registry, chronology, refutation, binary-cover/tree replay,
  target-closure, mutation, Meta-state restoration, and guarded
  ordinary-theorem canaries.
- `conformance/HexIntervalMathlib/RuleConformance.lean`: supported arithmetic
  package assembly, shared-DAG state quotation, chronological replay into an
  ordinary theorem, exact inv/div/regularize adapters, malformed-key/body/
  source/order/cut mutations, and registry/chronology/body/dependency/
  precision refusal guards.
- `HexInterval/Experiment/PntFks2FamilyData*.lean` and
  `HexInterval/Experiment/PntFks2Family.lean`: committed source-pinned family
  data and the Mathlib-free complete-family checker.
- `HexInterval/Experiment/PntLogNatural.lean`: bounded source-pinned
  natural-number log-table data, dyadic-reduction authentication, and generic
  package planning.  Its real semantics and source-shaped theorems live in the
  Mathlib companion.
- `HexInterval/Experiment/PntLogRational.lean`: bounded source-pinned rational
  log-table data, exact reduction and endpoint authentication, and generic
  package planning. Its ordinary-kernel atanh proof and seventeen
  source-shaped declarations live in the Mathlib companion.
- `HexInterval/Experiment/PntExpNegative.lean`: the bounded 79-row negative
  exponential source table, authenticated sixth-power certificates, and exact
  endpoint comparisons.  Real Taylor and power semantics live in the Mathlib
  companion.
- `HexInterval/Experiment/PntExpPoint.lean`: nine bounded signed-rational
  exponential point records with authenticated Taylor steps, natural powers,
  directions, and final endpoints. Real Taylor semantics and source-shaped
  theorems live in the Mathlib companion.
- `HexInterval/Experiment/PntNestedLogTwo.lean`: a bounded two-event log
  package for the strict positive inner `log 2` enclosure and its two-sided
  outer logarithm window.
- `HexInterval/Experiment/PntPiPoint.lean`: a provider-agnostic constant
  operation package authenticating the exact `315 / 100` π cut.
- `scripts/conformance/run_pnt_fks2_family.sh`: fail-closed entry point for the
  non-default complete-family proof and conformance profile.
- `conformance/HexIntervalMathlib/FrontendConformance.lean`: supported
  recursive shared-DAG reification, exact source binding, malformed-entry,
  root/operation-table, stable-key, and resource rejection, derived semantic
  model, flat chronological replay, and ordinary inequality, conjunction, and
  equality theorem/axiom canaries from source containment without a caller-
  supplied `Program.Models` or per-node initial-fact premise.
- `conformance/HexIntervalMathlib/TacticConformance.lean`: supported Meta
  parsing, runtime authentication, emission, strict and closed cuts,
  conjunction, equality, exact resource roles, transactional failure,
  diagnostics, and guarded ordinary-theorem canaries.
- `bench/HexInterval/Bench.lean`: Mathlib-free interval and scheduler
  benchmarks.

## Conformance

The required Lean-only profile covers every interval shape and operation with
typical, boundary, and adversarial inputs. In particular it includes:

- all four finite endpoint closure combinations;
- malformed structural programs, including duplicate operation keys, wrong
  arity/domain, unknown operations, and self/forward SSA references;
- malformed registration, scope, and request snapshots, including wrong
  operation/rule versions, duplicate or out-of-range ports, misaligned side
  tables, changed fact versions, and changed ordered write authority;
- malformed or over-budget state snapshots, including stale/cross-node update
  predecessors, wrong program versions, non-prefix extensions, exact generated
  version-zero seed restoration, dependency/watcher misalignment, stale dirty
  bits, policy tombstones, queue and chronology one-over limits, and reordered
  fact/instance chronology;
- diagnostic event count, payload-byte, logical-work, and code refusal,
  malformed cached totals, and a truncation canary showing that diagnostic
  loss cannot change branch facts, versions, provenance, or contradiction;
- stale or mutated search decisions and callback replies, unauthorized writes,
  stale later updates with whole-batch rollback, callback failure, and exact
  step/split/leaf/frontier/depth/scope one-over refusal; stable DFS/BFS order,
  exact parent scope/version/provenance restoration, and trace truncation with
  identical retained branch state;
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
- minimum and maximum preflight refusal on either same-side comparison and on
  the distinct selected-cut final comparison;
- precision-indexed reciprocal for `{3}`, positive, negative, singleton-zero,
  one-sided-zero, sign-crossing, and sign-separated unbounded inputs;
- first-slice division for all four singleton sign combinations, total-zero,
  empty, whole fallback, wrong endpoints, actual-result bounds, and every
  precision/quotient resource refusal stage including second-call priority;
- powers on negative, mixed-sign, open-zero, and singleton inputs;
- rational-to-dyadic projection at exact and inexact values, including the
  strict cut gained by moving a closed source outward;
- canonical raw rational tables, including negative numerators and canonical
  `0 / 1`, and rejection of zero denominators, noncoprime equivalent
  encodings, unused oversized entries, excessive projection shifts, and
  one-step-over-budget cross-products before allocation;
- regularization idempotence, outward containment, moved strict cuts, and
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
  and Laurent Granvilliers's August 2004 *RealPaver User's Manual*, edition
  0.4, distributed in the
  [official 0.4 source archive](https://sourceforge.net/projects/realpaver/files/realpaver/0.4/)
  (with a [browsable manual mirror](https://manualzz.com/doc/4136960/realpaver-user-manual)).
- Raphaël Chenouard and Laurent Granvilliers,
  [RealPaver 1.1: A C++ Library for Constraint Programming over Numeric or Mixed Discrete-Continuous Domains](https://doi.org/10.21105/joss.09331)
  (2026), with the
  [tagged 1.1.1 sources](https://github.com/realpaver/realpaver/tree/v1.1.1-joss2),
  especially the exact
  [`IntervalPropagator`](https://github.com/realpaver/realpaver/blob/v1.1.1-joss2/src/realpaver/IntervalPropagator.cpp)
  and
  [`ContractorBC4Revise`](https://github.com/realpaver/realpaver/blob/v1.1.1-joss2/src/realpaver/ContractorBC4Revise.cpp)
  implementations discussed above.
- [IntervalArithmetic.jl construction and exact input guidance](https://juliaintervals.github.io/IntervalArithmetic.jl/stable/manual/construction/).
- [Boost.Interval policies and representation](https://www.boost.org/doc/libs/latest/libs/numeric/interval/doc/interval.htm).
