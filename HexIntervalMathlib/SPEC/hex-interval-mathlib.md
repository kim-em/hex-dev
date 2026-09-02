# hex-interval-mathlib specification

`hex-interval-mathlib` is the Mathlib companion to the Mathlib-free
`hex-interval` computational library. It owns interpretations into Mathlib
types and ordinary-kernel proofs of the public interval operations; it does not
perform planner search or turn runtime checks into proof evidence.

## Supported surface

The foundational supported module is `HexIntervalMathlib.Interval`. It defines the
real value of a dyadic endpoint and membership for every public interval cut:
strict or closed finite ends, independent unbounded ends, and canonical empty.
`HexIntervalMathlib.Addition`, `HexIntervalMathlib.Subtraction`, and
`HexIntervalMathlib.Multiplication` add the public arithmetic image theorems,
while `HexIntervalMathlib.MinMax` supplies selected-cut and real-image
enclosure theorems for minimum and maximum, and
`HexIntervalMathlib.Absolute` supplies the corresponding absolute-value
theorems. `HexIntervalMathlib.Power` supplies exact selected-cut semantics
and a one-way real-image theorem for checked natural power.
`HexIntervalMathlib.Split` proves exact closed-left/strict-right membership
for transactional splitting. `HexIntervalMathlib.Inverse` proves the computed
connected-cut characterization and sound total-real-inverse enclosure, while
`HexIntervalMathlib.Division` proves the computed first-slice quotient cuts and
sound total-real-division enclosure. `HexIntervalMathlib.Regularize` proves
exact rounded-cut semantics, outward containment, and raw-cut idempotence.
`HexIntervalMathlib.Program` is the supported function-agnostic interpretation
of the Mathlib-free expression DAG. A package contributes an exact opaque
operation signature and relation; `Program.Models` requires pointwise
alignment with the complete operation array and one relation witness for every
SSA node. `HexIntervalMathlib.Proof` is the supported chronological proof
contract over `Program`, `Fact`, `Action`, `State`, `Policy`, and `Search`.
It owns semantic consequence, locality and conservative-extension laws,
package theorem schemas, globally unambiguous registry assembly, plain quoted
fact/equality/transport/instance/refutation steps, immutable typed proof state,
and exact caller-target closure.

`HexIntervalMathlib.Rule` is the first supported concrete registry. Its
immutable configuration fixes endpoint limits, natural-power work, precision
resources, and optional extra meanings. It owns stable
operation and rule keys, exact real meanings, local registrations, and forward
schemas for negation, addition, subtraction, multiplication, binary natural
power, absolute value, minimum, maximum, reciprocal, division, and
regularization. Source nodes obtain their version-zero facts from
caller hypotheses rather than a rule. Every schema authenticates the exact
node operation and argument order, source fact versions through the quoted
action, proposed interval, one-cell body, and the result of rerunning the
public checked operation. Its fact-domain meet independently reruns checked
intersection. `Rule.quote` converts the exact accepted `State.Branch` history
to plain proof chronology; that conversion grants no evidence. Additional
operation schemas extend the registry only when their public checked operation
and one-way image theorem are available in the same library revision.

`HexIntervalMathlib.Frontend` is a supported programmatic client of
those contracts. Its recursive arithmetic `Term` reifier resolves every
operation from the configured meaning array by stable key, preserves exact
structural sharing, checks the completed SSA program, and enforces explicit
source, operation, node, and depth caps separately from registry and replay
caps. Before seeding facts it rechecks the transparent result's one-entry-per-
node correspondence, structural sharing, stable operation key, ordered child
edges, and source-index range. Its generalized `InitialContext` has exactly one
node-indexed version-zero row per retained reifier entry. An absent selection
materializes as `whole`; a present interval is plain caller data and gains no
authority until a separate positional `InitialContext.Contains` proof relates
that exact row to the entry's retained term evaluation. This permits an
authenticated fact on a computed node without treating the data or the row
label as proof. Exact row count and order are checked only after source,
operation, node, and depth caps; `setFact` refuses out-of-range or mistargeted
writes transactionally.

The original `inputWithin` remains a source-only convenience wrapper: it binds
every caller-selected source interval exactly once, leaves computed rows at
domain top, and proves those top seeds automatically. Both constructors share
one common bounded reifier preflight, so the wrapper preserves its source-error
precedence without repeating the structural scan. Constants and later
improvements still enter through package-owned chronology. Exact dyadic and
natural-literal singletons are seeded through the checked node-indexed initial
context. Successful replay
can be eliminated from either source containment or generalized initial-row
containment to a target membership theorem, either endpoint inequality, their
conjunction, or equality for a closed singleton.
For Meta clients, `modelOfCheck` transparently projects the exact `Model` from
a kernel-reduced successful `modelWithin` call. `valuesAt` quotes a finite list
as the total source valuation used by the frontend, and
`SourcesContain.ofForall₂` converts one membership proof per list entry into
the exact array-indexed source obligation; indices beyond the list are never
observed. These helpers add no proof schema and do not replay chronology.
These are ordinary theorem combinators over a flat caller-supplied event
chronology: the module does not turn a generic search tree into proof recipes,
parse Lean expressions or hypotheses, or contain tactic syntax. The caps run
before array scans. A successful depth check may still traverse the complete
already-constructed branching `Term`; construction and structural equality of
caller terms remain an explicit non-preemptible envelope.

The Mathlib-free layer now retains an authenticated `Search.Result.Tree` with
exact parent/child seed relations and target/refute/unknown terminal data.
Restarted child branches themselves reset versions and generations and carry
no inherited derivation proof; the exact tree edge is what retains that
provenance. That runtime tree is not evidence. This companion now separately
checks package-owned split/refutation recipes, recursively replays and joins a
checked tree, and provides a one-selected-callback driver which advances the
retained source and appends the callback's exact fact events in one
transaction. Its supported `Controller` explicitly aligns stable application
generators with the same-order runtime and proof registries, regenerates
resource-first deterministic offers from the authenticated current head, and
runs bounded repeated policy selection over the sealed tree/session bundle.
The explicit `Controller.Package` vertical still uses toy fact-event callbacks
and application generators. Concrete built-in arithmetic has two explicit
adapters: the fact-only `Controller.Executable` route and the typed-batch
`RuntimeRule` route. `RuntimeRule` recomputes all eleven supported arithmetic
operations from exact executable requests, emits one typed fact batch with the
matching one-cell format, and seals its assembly against the same-order
`Rule` theorem registry through `RuntimeProof.Registry`. Paired caller packages
extend both sides for configured opaque meanings. The Mathlib-free
`Runtime.State` owns that executable assembly and
atomically validates typed fact/equality/transport/instance batches, including
an exact equality descriptor arena and append-only application/binding/node
suffixes; `Search.Result.Tree` retains its sealed transition in a child.
The built-in offers are deliberately one-shot: only a version-zero result node
whose current fact is domain top is scheduled, so the callback installs its
recomputed proposal as version one without raw access to the previous branch.
Direct repeats fail the runtime predecessor check. Runtime-to-proof quotation
and exact target/refutation correlation are supported. The public tactic uses
that route with a fixed topological application plan; automatic package
discovery and a general search-selected tactic policy remain later edges.

`HexIntervalMathlib.Tactic` is the first supported Meta client. It recursively
parses real local variables and the registered forward arithmetic operations,
selects strongest integer lower and upper hypotheses, constructs the exact
runtime program and source facts, starts the sealed branch/runtime/retained
tree/controller bundle, and selects each authenticated arithmetic application
in topological order. It requires a stopped controller with no live offers or
residual plan, resolves the exact final target version and fact, and settles
that lineage through `RuntimeEmit`. The emitter quotes the authenticated
`Proof.Input` and chronology into a transparent `Proof.replayWith` proof term;
the tactic then kernel-checks the input/program/target/fact/model correlations,
closes the exact caller source proofs, and proves that the reified term
evaluates to the original Lean expression. Every emitted boundary crosses
`Proof.emitChecked`; runtime success is never reflected into proof syntax. The
first residual application is resolved back through the same sealed assembly
and registration table for diagnostics, so a resource-starved built-in names
the responsible stable rule rather than exposing a brittle aggregate pending
count. Handler applicability currently retains only a Boolean; the tactic does
not rerun arithmetic to manufacture a more specific discarded refusal cost.
The bare `interval` tactic currently closes
strict or non-strict lower and upper goals, closed-singleton equality, and
conjunctions. `interval?` reports the fixed forward configuration only after
the same transaction succeeds; failure emits no misleading query result.
`interval_bound e` elaborates and derives inside `withoutModifyingState`, then
reports concrete selected lower/upper cuts and the recipe size. Those cuts are
diagnostics, not tactic syntax: noninteger dyadic endpoints may be displayed,
while inequality targets currently accept only integer endpoints and equality
targets accept exact dyadics, so reported cuts are not necessarily pasteable.
Programmatic
`Tactic.deriveBound` exposes the exact authenticated forward bundle.

This first vertical deliberately accepts only integer source and inequality
target cuts, exact dyadic literal/equality targets, per-node natural-literal
exponents, and forward negation, addition, subtraction, multiplication, binary
power, absolute value, minimum, maximum,
reciprocal, and division. It appends configured outward regularization after
each computed arithmetic row, and fails transactionally on precision-resource
refusal. Its fixed public-tactic precision is `16`, the dyadic grid `2⁻¹⁶`;
programmatic `deriveBound` may instead receive another precision admitted by
the explicit resource envelope. Automatic regularization adds one internal
`Term` layer after every computed arithmetic layer, so the reported/default
term-depth cap `32` permits about 16 nested arithmetic operations on a source
spine. Noninteger hypotheses are not authenticated as integer cuts. It has no
subdivision, contractors, arbitrary-function discovery, named-hypothesis
selection, or general search-selected policy. All parse, resource, controller,
settlement, replay, and emission failures leave the tactic state unchanged.

The proof contract treats runtime states, callback replies, payload bytes,
search decisions, contradiction flags, and diagnostic traces as untrusted
decoded data. Every accepted fact or equality is an ordinary theorem returned
by the exact package schema; every instance carries an append-only stability
theorem and a model-extension theorem. Replay authenticates the complete
schema address, registry rule index/key/kind, anchor operation, ordered
read/write projection, scope, action/program versions, node/fact versions,
dependencies, body, equality orientation, instance suffix, final program, and
target. A refuter consumes one already-proved exact fact; runtime
`contradictory` state is not an argument. The final Meta emitter runs
transactionally and accepts a package-produced `Expr` only after rollback,
placeholder rejection, `Meta.check`, inference, and definitional equality with
the exact expected proposition in the caller environment.

For every successful resource-checked public operation it proves:

- `contains_intersectWithin`: membership in the result is equivalent to
  membership in both inputs;
- `contains_hullWithin`: membership in the result is exactly the selected-cut
  interval closure, with explicit empty identities and no false set-union
  claim;
- `contains_hullWithin_left` and `contains_hullWithin_right`: each input is
  contained in the result;
- `contains_negWithin`: membership of `x` in the result is equivalent to
  membership of `-x` in the input;
- `contains_addWithin`: exact successful-result membership in the independently
  summed Minkowski cuts, with empty absorption, unbounded sides, and endpoint
  strictness;
- `add_mem_addWithin`: two input members add to a member of every successful
  result;
- `contains_subWithin`: exact successful-result membership in the crossed
  difference cuts, including empty absorption and independent unbounded
  sides;
- `sub_mem_subWithin`: two input members subtract to a member of every
  successful result;
- `contains_minWithin` and `contains_maxWithin`: exact membership in the
  computed selected cuts;
- `min_mem_minWithin` and `max_mem_maxWithin`: pointwise real minimum and
  maximum of two input members belong to every successful result;
- `contains_absWithin`: exact membership in the normalized selected absolute
  value cuts;
- `contains_absUnchecked`: raw absolute-value cuts contain `|x|` whenever the
  source raw interval contains `x`; this is a one-way image theorem, not a
  converse characterization;
- `abs_mem_absWithin`: the absolute value of every input member belongs to every
  successful result;
- `contains_mulWithin`: exact successful-result membership in the explicit
  selected lower and upper candidate cuts after normalization, including
  empty, unbounded, strict, closed, and zero-attainment cases;
- `mul_mem_mulWithin`: two input members multiply to a member of every
  successful result. This is an enclosure theorem; no separate image-tightness
  converse is claimed;
- `contains_powWithin`: exact membership in the normalized direct cuts selected
  for exponent zero, positive odd powers, and positive even powers;
- `pow_mem_powWithin`: every source member raised to the caller's natural
  exponent belongs to every successful result;
- `contains_regularizeWithin`: exact membership in the normalized Core-rounded
  cuts;
- `contains_regularizeUnchecked` and `mem_regularizeWithin`: every source
  member remains in the raw and checked outward views;
- `regularizeUnchecked_idem`: repeating the same requested precision leaves
  every computed raw cut unchanged, without claiming global grid tightness;
- `contains_splitWithin_left` and `contains_splitWithin_right`: exact child
  membership as source membership conjoined with `x ≤ point` or `point < x`;
- `splitWithin_contained`, `splitWithin_cover`, and `splitWithin_disjoint`:
  both children remain in the source, jointly cover it, and do not overlap;
- `splitWithin_point_left` and `splitWithin_point_not_right`: the cut point is
  left-owned exactly when it belonged to the source and never right-owned;
- `contains_invWithin`: membership in a successful reciprocal is exactly the
  normalized computed outward-cut predicate; this does not identify the
  connected hull with the generally-disconnected exact image;
- `inv_mem_invWithin`: every real source member maps under Lean's total
  reciprocal into the successful enclosure, including `0⁻¹ = 0`;
- `contains_divWithin`: membership in successful division is exactly its
  computed singleton outward cuts or explicit whole-line fallback;
- `div_mem_divWithin`: both source memberships are consumed to place their
  Lean-total real quotient in every successful enclosure.

These theorems depend on the exact successful result equation: `BuildResult`
or `Arithmetic.Result` for unary/binary images, and transactional
`SplitResult` for splitting. A resource refusal has no set interpretation and
is never treated as an empty interval. The proofs use the public operation's
checked view-characterization
theorems and independently establish the complete raw-cut semantics; they do
not import the experimental propagation fact domain.

## Boundary

The public companion grows only with the supported `Hex.Interval` API. Its
`Program` module gives exact meanings to the supported decoded SSA program,
and its `Proof` module owns function-agnostic package schemas, chronological
typed replay, target closure, and an expression-emission boundary that rejects
placeholders and unresolved metavariables, restores emitter environment,
message, information, and metavariable changes, clears both environment-
dependent elaborator caches, then runs `Meta.check` and checks exact type
definitional equality transactionally in the caller's environment. Emitted
terms may reference only declarations that survive that rollback. The kernel
performs the final check when the caller installs the expression.
Runtime search state, callbacks, payload bytes, and traces are untrusted and
cannot enter `Proof.Evidence`. The built-in arithmetic package registry and
its supported branch/session `Cause`-to-`Proof.Event` quotation ship below.
The Mathlib-free `Executable.Assembly` supports explicit arbitrary-operation
callback packages and raw replay formats. Those raw quotations are not
`Proof.Event`s and remain inert. The fact-only `Controller.Executable` adapter
correlates an accepted request/update with an exact fact format and decoder;
only later independent `Proof` replay invokes its theorem schema.
The separate Mathlib-free typed runtime authenticates and retains the raw
fact/equality/transport/instance event chronology without importing this proof
module. `HexIntervalMathlib.RuntimeProof` is the supported conversion edge: its
sealed registry checks bidirectional executable-format/proof-schema coverage,
then reconstructs fact, equality, transport, and instance `Proof.Event`s from
the sealed `Runtime.Applied` fields. It reruns append-only executable extension
to pin the exact program, registration, binding, concrete application, and
generation suffix before narrowing an instance record to `Proof.InstanceStep`.
Fact quotation preserves proposed/installed meet correlation; equality pins
the exact endpoints, origin, assumptions, and schema; transport carries no
quotation and replays only through the independently admitted equality and
exact live source fact; these checks authorize structural substitution but the
equality schema alone supplies semantic entailment. Complete retained
transition chains are quoted as one transaction into a sealed token containing
the exact registry and per-node recipe. Node-id order propagates each split
parent's post-chronology executable assembly to both restarted children, so an
instance before a split is retained exactly. Recursive replay consumes the
token without repeating quotation; the underlying proof fold independently
rechecks the retained tree and proof limits once at its theorem boundary.
Target, refutation, and split remain the separately authenticated
terminal schemas owned by `Proof.replayTree`; they are not synthesized from a
runtime callback batch.
`HexIntervalMathlib.RuntimeTerminal` supplies the sealed target/refutation
edge. Its ordinary-import-private constructors prevent direct token
fabrication. `Active` and `Lineage` carry the live controller/retained tree,
`RuntimeProof.Registry`, and admitted `Proof.Input`; `Checked` carries that
input while its nested `RuntimeProof.Bundle` independently retains the exact
registry used by quotation. `replayWithin` checks exact input equality rather
than claiming that constructor privacy alone prevents redirection. Sibling
restart consumes the retained token's tree. Target settlement resolves the
exact current target fact. Refutation first revalidates the retained tree,
requires the exact current version, then resolves and decodes the exact package
schema and invokes it against the retained source program/fact; recursive proof
replay independently proves it again. Search/result and proof body resources
are checked at settlement, while complete transition/event/structural/proof-
tree resources remain transactional at bundle quotation.

`HexIntervalMathlib.RuntimeEmit` is the supported Meta boundary from that
sealed root-target lineage to kernel syntax. Emitter packages pair exact
`Proof.Key`s with transparent theorem-schema expressions. One joint builder
checks package-local and global missing, extra, duplicate, and wrong-role
coverage. Preparation also projects each emitted schema's key and requires it
to be definitionally equal to the handle's declared key. The builder constructs
the `Proof.Registry` and `RuntimeProof.Registry` from the same package array and
seals those registries with the emitter table; there is no post-hoc
compatibility-key attachment. `Active`, `Lineage`, and `Checked` retain this
unified registry alongside the corresponding private `RuntimeTerminal` token.

`RuntimeEmit.Checked.emitResultWithin` supports only a one-node root target. It
quotes the already authenticated program, input, registrations, and exact
fact/equality/transport/instance chronology as ordinary data and applies the
transparent `Proof.replayWith` fold. A decidable success proof projects an
exact `Proof.Evidence` term. The sealed result contains both the quoted
`Proof.Input` expression and Evidence whose claim projects that same expression;
its private constructor prevents callers from pairing independently emitted
terms. Every fact and schema callback crosses `Proof.emitChecked`, and the input
and final evidence separately cross it against their exact types. Both are
independently charged against the expression cap in the same saved-state
transaction before rollback; metavariables, synthetic placeholders, temporary
declarations, or retained Meta-state leakage therefore cannot escape.

`RuntimeEmit.Checked.emitInitialTargetWithin` is the narrower version-zero
path. It admits only the sole root terminal with an empty chronology, no
parent/side/seed edge, program version zero, fact version zero, and a target
that is exactly the fact at the same index in the retained input. It quotes
that input through the ordinary fact quoter, constructs the target-node and
target-fact correlations as reflexivity terms, checks both exact equality
types through `Proof.emitChecked`, and applies `Proof.initialTarget`. This
theorem merely selects an existing `initialBase` assumption; neither the
runtime token nor the fact representation supplies semantic authority.
`Proof.initialTarget` is consequently a public tautological theorem with no
resource limits: any caller that supplies its exact index, node, and fact
equalities may use it directly. The emitter's limits bound only the checked
reflection work needed to quote and correlate those terms. They do not grant,
restrict, or otherwise contribute logical authority. The fast path revalidates
the complete proof package/program registry under the caller's `Proof.Limits`,
prepares and typechecks all quotation callbacks, and charges the input and
final Evidence expressions independently. Its explicit program- and
fact-version checks are defensive invariants currently implied by admission
of a sole root with an empty chronology.

For the built-in interval quoter, the same version-zero token also succeeds
through `emitResultWithin`: its `getValue (ofRawWithin ...)` representation is
reducible enough for the empty `Proof.replayWith` check. Conformance requires
both emitters to quote definitionally equal inputs and Evidence claims. The
initial-target path is therefore not a correctness workaround for the current
built-in encoding. It is the smaller direct proof and does not require the
fact domain's `DecidableEq` to reduce an opaque representation merely to
rediscover that the exact target expression is the exact indexed initial fact.
This distinction matters for checked quoters whose fact constructors expose
semantic view theorems but deliberately keep their constructor bodies opaque.

Retained result and proof-tree admission remains owned by
`RuntimeEmit.Lineage.quoteWithin`, which constructs `Checked` only after
`RuntimeProof.Limits.result` and `.tree` have accepted the entire tree and
recipe. `RuntimeEmit.Limits` deliberately has no second tree-node, edge, or
depth envelope. For the initial-target shape the admitted minimum is one tree
node at depth zero; the recipe's one root edge is included in `proofWork`.
Thus a caller cannot use the fast path to evade a smaller result-node,
proof-node, depth, or edge-inclusive work limit: those limits must first
produce the sealed `Checked` token.

`Checked.emitWithin` remains the evidence-only compatibility projection of
`emitResultWithin`. There is no refutation or split expression emitter.
`Quoter` and `Handle` callbacks are trusted reflection code: the kernel checks
the theorem in the world they quote, but a generic registry cannot prove that a
caller callback faithfully reifies an arbitrary runtime `Fact`. Supported
public builders must therefore own those callbacks and compare the emitted
claim with the caller's exact goal before installation.

For `S` emitter handles, `C` retained events, `B` total body cells, `D` total
dependency cells, and `X` cells in a checked expression, registry coverage is
quadratic in the worst case because list membership/count checks scan the
package and global key tables. Preparation is `O(S)` callback invocations plus
one `O(X)` syntax traversal per returned schema expression. Chronology
prechecking and quotation are `O(C + B + D)` apart from fact callbacks and
construction of quoted program/action data; the transparent replay then pays
the existing proof fold and package theorem callbacks, which are arbitrary
pure Lean code and are not preemptible. The two final expression caps perform
one `O(X)` traversal for the quoted input and one for its correlated evidence.
Schema, chronology, body, dependency, and
expression limits fail without returning a partial expression.

`HexIntervalMathlib.RuntimeRuleEmit` supplies the paired handles and fact
quoter for exactly the eleven built-in arithmetic schemas. Its convenience
builder jointly constructs the executable batch assembly, theorem registry,
and emitter registry. Configurations with caller-owned opaque meanings require
their own paired emitter packages and are deliberately rejected by this
built-in-only builder.

A general split terminal adapter is intentionally absent. `Proof.seedChild`
inherits the parent proof equality table and compact identities, whereas
`Runtime.State.startWithin` restarts a child with an empty equality arena and
identity zero. If the parent has `n > 0` equalities, the first child equality is
runtime identity zero but proof identity `n`. Supporting only the empty-parent
case under a general-looking API would weaken this invariant; the split edge
therefore remains blocked until the Mathlib-free restart contract imports an
authenticated equality arena or proof replay changes its identity model.
`Lineage.resumeWithin` detects this condition along the current node's exact
ancestor chain, excluding current-node and sibling events, and refuses before
starting the supplied runtime. Assembly generation is not a parallel semantic
identity gap: runtime restart authenticates the supplied generation base, and
transactional `RuntimeProof` quotation reconstructs the parent's post-event
assembly and checks each child's exact generation, bindings, applications, and
program. A wrong same-program assembly cannot yield a checked child event; if
there are no child events, no proof evidence depends on its assembly metadata.
`Search` never decrements its `remaining` view; executable refresh preserves
the controller-owned value stored in the sealed session. The adapter uses a
fixed structural `policyMeasure` for application identifiers and rule keys,
while callers supply only the measure for their policy state. A domain
`NarrowResult.resourceLimit budget` becomes the distinct
`Controller.Resource.narrow budget` refusal before any update is retained;
fixed-point `noChange` and malformed narrowing remain mismatches at this
fact-only boundary. Its public `Run` currently contains only a resumable
`stopped` result. Driver target, refutation, split, and unknown outcomes are
rejected as mismatches until separate typed terminal correlation is added.
The assembly constructors are sealed under ordinary imports; deliberate
`import all HexInterval.Executable` is a repository-guarded trusted-source
escape hatch, not decoded runtime or proof authority.
The typed-proof registry and bundle constructors are likewise sealed;
`import all HexIntervalMathlib.RuntimeProof` is rejected outside an
exact reviewed allowlist, currently empty.
Automatic arbitrary-function theorem-package discovery and default registries
remain experimental. `RuntimeRule.buildWithWithin` accepts only explicit paired
executable and proof packages for configured opaque meanings and then seals
bidirectional coverage over the complete registry; unpaired formats or schemas
are rejected. Its package cache counts committed callbacks and is independently
bounded by executable cache resources. Checked arithmetic refusal yields no
fact batch and is rejected transactionally by the runtime rather than gaining
theorem authority.
The supported explicit fact-event controller can produce and replay
search-selected recipes. The tactic below now crosses the typed controller and
emitter boundary, but remains a deliberately narrow deterministic topological
client rather than the generic discovery/policy bridge.
Further arithmetic images and useful bounded nonsingleton division require their own
operation-specific semantic theorems before promotion. An image operation must
at least prove successful-result cut semantics and sound real-image enclosure;
it claims a tightness converse only when that converse is separately proved.
Public reciprocal is sound but
conservatively closes finite rounded cuts; endpoint attainment, grid
optimality, and disconnected interval-set precision remain future work.
Public division directly encloses two nonzero finite singletons, handles empty
and total-zero cases exactly, and deliberately returns whole for every other
nonempty shape. No tightness converse or bounded nonsingleton quotient is
claimed.

The supported proof limits cap retained package and schema counts, certificate
body cells, ordered dependencies, and chronology. They do not claim to
preempt full `Program.check` or registration validation, equality on arbitrary
caller facts, schema decoding, or package theorem callbacks. Authenticated
search output must first pass the Mathlib-free `Search` envelope; a direct
trusted caller of `Proof` is responsible for bounding its program and package
assembly before replay.

Under ordinary imports, the theorem-registry constructor is private and
`Registry.buildWithin` is the only supported construction path. Lean's
deliberate `import all HexIntervalMathlib.Proof` exposes trusted internals and
lies outside the decoded-runtime threat model; the repository DAG checker
rejects that import outside an exact reviewed allowlist, currently empty.

`HexIntervalMathlib.Rule` is the first supported package registry. Its stable
arithmetic schemas recompute exact checked negation, addition, subtraction,
multiplication, binary natural power, absolute value, minimum, maximum,
reciprocal, division, and regularization results before producing evidence.
Source facts remain caller assumptions, while exact dyadic and natural literals
are authenticated node-indexed initial facts and have no callbacks. Direct
registry assembly bounds the retained packages and schemas but does not preempt
construction or equality of caller program/meaning arrays; decoded callers
must first cross `Search`.
Its `quote` and `quoteSession` functions convert supported branch/session
causes to proof events without making runtime state evidence. Each power node
has ordered `[base, natural-exponent]` edges, and literal operation meanings are
value-agnostic; exact values come only from their separately authenticated
initial singleton facts. Duplicate package registration and operation keys
cannot add another parameterization. Arbitrary-function package
discovery, Mathlib-free runtime packages, split-search tactic integration, and
default package discovery remain experimental. The
supported direct-forward reifier and tactic syntax are a narrow client of this
registry, not the autonomous split-search tactic.

The supported proof fold also accepts a `Search.Result.Tree` only after the
tree passes `Tree.check` under the exact caller-supplied search limits and
measure. A separate untrusted `TreeRecipe` must echo every parent, side, and
seed edge and supply the ordered proof events. On a split, the child proof
state restarts at program version zero: the one branch seed becomes a new
assumption, while every inherited parent fact remains derived evidence rebased
to the child-local version. Package-owned keyed split and refutation schemas
authenticate the cover and contradiction; runtime terminal tags, bodies, and
contradiction state never become evidence. `Proof.TreeLimits` separately bound
proof nodes, depth, body cells, and structural work. Pending and unknown leaves
reject transactionally. `HexIntervalMathlib.Driver` executes one
already-selected, authenticated package callback and returns the updated
sealed tree plus separately untrusted recipe atomically. The current head
source may advance through that callback before splitting or settling, so
child-local propagation and its chronology replay are supported. Its
caller-owned `Driver.Measure` must charge complete logical encodings of every
retained event and edge, including nested facts, actions, schemas, dependency
versions, body naturals, and seed data; independent recipe byte/work caps are
rechecked across the complete bundle on every transition. Measurement and
callback execution remain explicitly non-preemptible.
`HexIntervalMathlib.Controller` supplies the next supported explicit-assembly
layer: its sealed registry declares one stable compatibility key, exact
application slot to rule/runtime route, and same-order proof registration; its
sealed state rejects a selected compact identifier or live session transplanted
across registry keys. The key is deliberately a trusted compatibility epoch,
not callback-object identity: separately built registries using the same key
assert interchangeable implementations, whose returned data still crosses all
runtime and proof checks. Generator/policy/equality callbacks remain
non-preemptible, while program, branch, registration, binding, action-port,
structural-input, application, offer, and retained-result caps are checked
before controller-owned traversal or allocation. A caller-owned logical
policy-state measure is also non-preemptible, but the initial value and every
callback successor must fit explicit byte/pair/work caps before retention.
Offer age is the bounded
sealed session serial rather than package data. The choice cap is cumulative
per returned sealed state lineage; explicit `State.startWithin` creates a new
handle from a sealed bundle and resets choices, the dismissal latch, and the
search session's serial, steps, and trace even at the same retained head/scope.
Pure state reuse creates separately bounded successors rather than a global
budget, and a new handle does not inherit proof closure or saturation. This
explicit `Controller.Package` route is a fact-event Mathlib assembly whose
conformance callbacks are toy packages, not concrete built-in arithmetic
driver adapters. Built-in arithmetic reaches this controller only through the
separate sealed `Controller.Executable` route. Automatic package discovery and
the public split-search tactic remain absent. Every immutable offer snapshot has
one constant controller-owned serial age; any malformed draft aborts its whole
regeneration. Dismissing a non-split offer sets a controller-owned incomplete
bit which survives accepted refreshes in the same scope within one returned
handle lineage. The next split/terminal scope transition clears it, and an
explicit new `State.startWithin` lineage resets it even at the same scope;
dismissing a split probe does not set it.
Policy stop returns a resumable sealed chunk boundary, while `maxChoices`
exhaustion is a resource error. `Run.complete` says only that no pending runtime
frontier remains; proof closure still requires replay. The
reference cost of up to `maxChoices` selected transitions includes entry
session authentication, current and replacement retained-tree/bundle
validation, and regenerated-session authentication each time. The
current retained-tree builder repeatedly
validates retained branches and pairwise scope uniqueness; incremental
construction therefore has the documented `Θ(N² * B + N³)` reference cost,
where `B` is branch validation work, rather than a production-local-update
claim.

`HexIntervalMathlib.Experiment.PntLogRational` is a fixed-source acceptance
provider rather than public interval arithmetic. It proves the original
strength of seventeen pinned PNT+ direct-log declarations over fifteen
rational inputs from an authenticated dyadic reduction, eight-term atanh sum,
geometric tail, and checked `log 2` bounds. The runtime accepts exact source
rows only; arbitrary rational inputs, generated precision/endpoints, table
persistence, and every admitted LeanCert-owned public bound remain outside its
claim.

`HexIntervalMathlib.Experiment.PntExpPoint` proves the nine remaining pinned
exponential statements from one rational Taylor/power theorem. Each source row
fixes a signed rational input, a step in `[-1, 1]`, a positive natural
multiplier, one checked side of a fourteen-term Taylor enclosure, and the final
rational cut. The result preserves the source statements and does not import a
LeanCert theorem. It is not a public arbitrary-input exponential operation.

`HexIntervalMathlib.Experiment.PntNestedLogTwo` proves the two pinned
`log (log 2)` statements through two chronological checked log events. The
first establishes a strict positive two-sided `log 2` enclosure; the second
consumes both endpoints in fourteen-term rational remainder checks. The
ordinary replay theorem is strictly stronger than both source statements, and
zero-touching or bypassed inner facts reject.

`HexIntervalMathlib.Experiment.PntPiPoint` interprets a provider-agnostic
constant operation as `Real.pi`, authenticates the exact `315 / 100` cut, and
uses the axiom-clean `Real.pi_lt_d2` theorem from `Analysis.Real.Pi.Bounds`.
It does not import Mathlib's Chudnovsky development; the latter's
`proof_wanted` sum-to-`π⁻¹` identity is not migration evidence.

Together with the other source-pinned providers, these slices cover every
actual pinned `LogTables.lean` tactic site after localized rewrites or stronger
results. They do not provide LeanCert API parity, arbitrary input/precision
support, persistent tables, or table-scale performance evidence.

## Conformance

`HexIntervalMathlib.IntervalConformance` pins both directions of intersection
membership, exact hull closure and both input inclusions, negation transport,
addition, subtraction, and multiplication cut exactness and image transport,
exact split membership/coverage/disjointness/point ownership, and the exact
regularization cut semantics/outward containment/idempotence, together with the
ordinary-kernel axiom surface. It also pins reciprocal computed-cut exactness
and total-real-inverse enclosure, plus division computed-cut exactness and
total-real-division enclosure, without tightness converses.
`HexIntervalMathlib.MinMaxConformance` separately pins exact selected cuts,
both image enclosures, and their axiom surfaces; it does not assert a set-image
converse.
The interval conformance module also pins absolute-value cut exactness, image
transport, and its ordinary-kernel axiom surface, together with natural-power
cut exactness and image transport. The power theorem is one-way: no unproved
set-image converse is exported.
The Mathlib-free companion tests separately pin representative strict, closed,
unbounded, and empty shapes together with pre-allocation resource refusal. The
semantic theorem itself is exhaustive over the complete cut language.
`HexIntervalMathlib.ProgramProofConformance` independently pins exact operation
alignment and a live instance → fact → equality → transport chronology,
including body/source/version/final-state mutations, refuter ownership, a
nonvacuous ordinary theorem with a guarded axiom report, and transactional
Meta-state restoration after a wrongly typed emitter.
`HexIntervalMathlib.RuntimeProofConformance` pins the supported typed-runtime
adapter with a real `sin (-x)` instance → equality → fact → transport theorem
at the root and after both split children restart. A second split canary extends
the root first and proves both children restart from the inherited extended
program and generation. It mutates every typed event role, executable/proof
package ownership, schema, body, order, and child splice; checks exact one-under
retained-transition, event, structural-cell, and proof-chronology resources;
and guards the ordinary root/recursive axiom surfaces.
`HexIntervalMathlib.RuntimeTerminalConformance` pins exact target settlement
after the ordinary typed chronology at the root and in both restarted split
children, exact package-owned refutation, cross-schema/current-fact/input and
resource refusals, private constructors, and the ordinary replay axiom surface.
`HexIntervalMathlib.RuntimeRuleConformance` assembles every built-in arithmetic
handler, starts `Runtime.State` from frontend-shaped version-zero facts,
executes all unary and binary operations (including repeated argument slots),
settles the exact final target, and consumes `RuntimeTerminal.Checked.replay`
over the complete retained chronology without a fallback theorem. It checks
exact proposed/installed facts, one-cell bodies, semantic schema execution,
sticky cache refusal and replayability, sealed rule mutation rejection, and a
paired opaque-operation extension.
`HexIntervalMathlib.RuntimeEmitConformance` installs target Evidence only from
the sealed input/evidence pair for all eleven built-in rules, including repeated-input
binary applications, and separately emits the mixed `sin (-x)` instance,
equality, fact, and transport chronology. Its version-zero canary quotes a
checked opaque interval directly from the initial base with no chronology; it
also compares ordinary empty replay against the same token, requiring exact
input/claim agreement and a strictly smaller direct Evidence expression. It
pins computed-chronology refusal, the exact singleton tree/depth minimum,
an exact mismatched-target-fact lineage refusal, result-node, proof-node,
edge-inclusive work, proof-package, emitter-schema,
input-expression, and evidence-expression limits, plus transactional rollback.
It rejects package-local/global
coverage errors, cross-package and input transplants, a wrong schema
expression, ill-typed/open/placeholder/temporary emitters, Meta-state leakage,
and exact one-under schema, chronology, body, dependency, input-expression, and
evidence-expression resources while guarding every private constructor and the
ordinary theorem axiom surface. `FrontendConformance` additionally pins
transparent model projection and conversion from per-source list membership to
the indexed containment obligation.
`HexIntervalMathlib.RuleConformance` replays a shared arithmetic DAG through
the supported state quote and proof registry. Its ordinary theorem makes both
source assumptions load-bearing through add/sub/mul and checked
inv/div/regularize successors; mutations pin rule keys, bodies, argument order,
proposed cuts, chronology, and proof-resource limits. A precision refusal is
recomputed by the package and cannot be interpreted as a fact.
`HexIntervalMathlib.PntLogRationalConformance` additionally runs all fifteen
fixed rows and sends the representative large-shift `32e12` certificate through
generic planning, payload authentication, chronological replay, and the proof
frontend, with source, reduction, term-count, cross-row, window, and false-cut
rejection guards.
`HexIntervalMathlib.PntExpPointConformance` runs all nine fixed exponential
rows and sends the tight `exp 20` certificate through generic planning,
payload authentication, chronological replay, and the proof frontend. It also
pins source, Taylor-step, natural-power, term-count, cross-row, and false-cut
rejection.
`HexIntervalMathlib.PntNestedLogTwoConformance` pins the two-event dependency
chain, positive-domain rejection, both exact source wrappers, and generic
proof-frontend closure of the stronger two-sided theorem.
`HexIntervalMathlib.PntPiPointConformance` pins the exact constant certificate,
wrong-source and false-endpoint rejection, the ordinary π-bound axiom surface,
and generic proof-frontend closure.
`HexIntervalMathlib.FrontendConformance` reconstructs that shared arithmetic
DAG recursively, pins exact source and node-indexed literal binding,
rejects malformed result entries, duplicate stable keys, and one-over
source/operation/node/depth limits, replays a flat supported chronology, and
closes fully discharged lower inequality, two-sided conjunction, and equality
theorems from source containment alone. It additionally pins transactional
initial-row writes, structural and semantic anti-permutation, every generalized
input refusal, and a real zero-event replay of a computed target fact, with
guarded ordinary-theorem axiom reports. This first computed-row canary targets
version zero directly; an interior computed assumption feeding later rule
chronology is a distinct coverage target.
`HexIntervalMathlib.TacticConformance` exercises supported Meta parsing and
caller-proof emission over closed, strict, negative, shared-expression, power,
absolute-value, minimum, maximum, reciprocal, and division examples. It pins
conjunction and both equality orientations, a decimal-hypothesis poisoning
regression, diagnostic non-mutation, unsupported and false-target rejection,
exact zero-node and reciprocal-quotient resource roles, the load-bearing
nonintegral `2⁻¹ + 2⁻¹ = 1` default-precision theorem, and guarded
ordinary-kernel axiom surfaces.
