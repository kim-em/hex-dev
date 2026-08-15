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
immutable configuration fixes endpoint limits, natural-power work and one
exponent, precision resources, and one dyadic constant. It owns stable
operation and rule keys, exact real meanings, local registrations, and forward
schemas for that constant, negation, addition, subtraction, multiplication,
natural power, absolute value, minimum, maximum, reciprocal, division, and
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
edges, and source-index range. It then binds every caller-selected source
interval exactly once, proves computed domain-top seeds automatically, and requires
constants and every improvement to enter through package-owned chronology.
Successful replay can be eliminated to a target membership theorem, either
endpoint inequality, their conjunction, or equality for a closed singleton.
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
provenance. That runtime tree is not evidence. This companion still does not
quote it into package-owned split/refutation recipes or recursively replay and
join it; those remain separate later proof edges.

`HexIntervalMathlib.Tactic` is the first supported Meta client. It recursively
parses real local variables and the registered forward arithmetic operations,
selects strongest integer lower and upper hypotheses, constructs the exact
runtime `Program`, `Proof.Input`, and chronology as plain checked data, reruns
`Frontend.replay`, and independently reconstructs a caller proof
through package-owned image theorems and `Proof.emitChecked`. It does not emit
those discarded runtime records as Lean expressions. The bare `interval`
tactic currently closes
strict or non-strict lower and upper goals, closed-singleton equality, and
conjunctions. `interval?` reports the fixed forward configuration only after
the same transaction succeeds; failure emits no misleading query result.
`interval_bound e` elaborates and derives inside `withoutModifyingState`, then
reports concrete selected lower/upper cuts and the recipe size. Those cuts are
diagnostics, not tactic syntax: noninteger dyadic endpoints may be displayed,
while the current goal parser accepts only integer targets, so reported cuts
are not necessarily pasteable. Programmatic
`Tactic.deriveBound` exposes the exact authenticated forward bundle.

This first vertical deliberately accepts only integer source and target cuts,
zero, the configured natural exponent, and forward negation, addition,
subtraction, multiplication, power, absolute value, minimum, maximum,
reciprocal, and division. It appends configured outward regularization after
each computed arithmetic row, and fails transactionally on precision-resource
refusal. Its fixed public-tactic precision is `16`, the dyadic grid `2⁻¹⁶`;
programmatic `deriveBound` may instead receive another precision admitted by
the explicit resource envelope. Automatic regularization adds one internal
`Term` layer after every computed arithmetic layer, so the reported/default
term-depth cap `32` permits about 16 nested arithmetic operations on a source
spine. Noninteger hypotheses are not authenticated
as integer cuts. It has no subdivision, contractors, arbitrary-function discovery, named-
hypothesis selection, or search-selected recipe emitter. All parse, resource,
replay, and emission failures leave the tactic state unchanged.

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
Arbitrary-function package discovery, generic search-selected recipes, and
default registries remain experimental. The supported tactic below is a
deliberately narrow direct forward client, not the generic search bridge.
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
multiplication, natural power, absolute value, minimum, maximum, constant,
reciprocal, division, and regularization results before producing evidence.
Source facts remain caller assumptions. Direct registry assembly bounds the
retained packages and schemas but does not preempt construction or equality of
caller program/meaning arrays; decoded callers must first cross `Search`.
Its `quote` and `quoteSession` functions convert supported branch/session
causes to proof events without making runtime state evidence. `Config` fixes
exactly one natural exponent and one dyadic constant: every node at the
built-in power operation index shares that exponent, and every node at the
built-in constant index shares that value. Duplicate package registration and
operation keys cannot add another parameterization. Arbitrary-function package
discovery, generic search-to-recipe orchestration, split-search tactic
integration, and default package discovery remain experimental. The supported
direct-forward reifier and tactic syntax are a narrow client of this registry,
not the missing generic search bridge.

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
reject transactionally. Search callback quotation into this recipe and tactic
integration remain later work. The current retained-tree builder repeatedly
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
DAG recursively, pins exact source and configured-constant node binding,
rejects malformed result entries, duplicate stable keys, and one-over
source/operation/node/depth limits, replays a flat supported chronology, and
closes fully discharged lower inequality, two-sided conjunction, and equality
theorems from source containment alone, with guarded ordinary-theorem axiom
reports.
`HexIntervalMathlib.TacticConformance` exercises supported Meta parsing and
caller-proof emission over closed, strict, negative, shared-expression, power,
absolute-value, minimum, maximum, reciprocal, and division examples. It pins
conjunction and both equality orientations, a decimal-hypothesis poisoning
regression, diagnostic non-mutation, unsupported and false-target rejection,
exact zero-node and reciprocal-quotient resource roles, the load-bearing
nonintegral `2⁻¹ + 2⁻¹ = 1` default-precision theorem, and guarded
ordinary-kernel axiom surfaces.
