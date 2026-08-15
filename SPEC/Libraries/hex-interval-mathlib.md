# hex-interval-mathlib (real semantics, verified propagators, and the `interval` tactic)

`hex-interval-mathlib` gives mathematical meaning to
[hex-interval](../../HexInterval/SPEC/hex-interval.md) and owns soundness
theorems for interval operations and propagators. It depends on Mathlib and
`hex-interval`. There is no separate proof-only companion beyond this library.

The current supported surface interprets public canonical intervals over `ℝ`
and proves exact semantics for successful resource-checked intersection, hull,
negation, addition, subtraction, multiplication, minimum, maximum, absolute
value, natural power, and transactional splitting. Natural power exposes exact
computed cuts and a sound pointwise real image theorem, without claiming a
set-image converse. Splitting exposes both children together and proves exact
closed-left/strict-right membership, containment, cover, disjointness, and cut
ownership.
Propagator, provider, replay, and tactic modules remain experiments and are not
re-exported by the public umbrella. The user-facing tactic contract below is
the release target, not a claim that the tactic is already supported.

The tactic proves bounds for ordinary Lean expressions over `ℝ`. It reads
bounds from the local context, reifies shared expressions to an immutable
single-assignment base plus validated bounded extensions, runs the compiled
`hex-interval` search, and turns
the successful trace into an ordinary Lean proof. Search is untrusted. A rule
can affect the generated theorem only by supplying a proof through its
registered soundness theorem or verified certificate checker.

This design is intended to replace LeanCert for interval proofs, not to wrap
it. The compatibility milestone includes the actual PNT+ workloads and checks
that generated theorems do not depend on compiler trust. No implementation,
example, test, or fallback in this library uses `native_decide`.

A later domain registration may give direct interval semantics to `ℚ`. The
first release handles `ℚ`, `ℤ`, and `ℕ` literals and casts into `ℝ`. Direct
interval facts for the discrete types need ceil/floor normalization and a
separate domain contract; the dense dyadic-cut invariant is not reused for
them. No frontend uses recursive typeclass search to synthesize
per-expression propagators.

## Target user contract

The eventual main tactic is best-effort:

```lean
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) : x * (1 - x) ≤ 1 / 4 := by
  interval

example (x : ℝ) (hx : x ∈ Set.Ioo 0 1) : x + x < 2 := by
  interval

example : (3 : ℝ) < Real.pi := by
  interval
```

On success, the goal is closed by a kernel-checked proof. On failure, the
tactic leaves the goal unchanged and reports the best relevant bounds, the
main source of overestimation, useful untried actions, and the exhausted
budgets. It never changes a strict goal to a non-strict one and never accepts a
numerical candidate without checking its enclosure theorem.

Bounds obtained only after assuming the negation of the goal are labeled as
conditional counterexample-box bounds. They are not offered in a pasteable
`have` statement. Context-wide bounds come from the original assumption scope
or a separate `interval_bound` search.

The initial target forms are:

- `s < t`, `s ≤ t`, `s > t`, and `s ≥ t`;
- `s = t` when both sides reduce to the same singleton enclosure;
- `s ≠ t` when an enclosure of `s - t` excludes zero;
- membership in `Set.Icc`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`, `Set.Ici`,
  `Set.Ioi`, `Set.Iic`, or `Set.Iio`;
- `False`, when the interval facts in the context are inconsistent;
- conjunctions whose leaves all have one of these forms.

The tactic does not introduce quantifiers or implications. Users write
`intro` when needed. It declines unsupported propositions with a message that
names the first unsupported expression.

## Semantic layer

Finite endpoints use the exact embedding `(d.toRat : ℝ)`, following the Hex
root libraries without adding a dependency on them. The interval membership
relation is:

```lean
namespace Hex
namespace Interval

def Lower.Contains : Lower → ℝ → Prop
  | .unbounded, _      => True
  | .finite a false, x => (a.toRat : ℝ) ≤ x
  | .finite a true,  x => (a.toRat : ℝ) < x

def Upper.Contains : Upper → ℝ → Prop
  | .finite b false, x => x ≤ (b.toRat : ℝ)
  | .finite b true,  x => x < (b.toRat : ℝ)
  | .unbounded, _      => True

end Interval

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  match I.view with
  | .empty        => False
  | .bounds lo hi => lo.Contains x ∧ hi.Contains x

end Hex
```

Future tactic modules may use local notation for this predicate. Conversions
to the corresponding Mathlib set intervals remain future surface API;
infinities are endpoint markers, not real values.

The currently supported foundational theorems are:

```lean
theorem contains_intersectWithin
    (h : intersectWithin limit I J = .ready result) :
    result.Contains x ↔ I.Contains x ∧ J.Contains x

theorem contains_hullWithin
    (h : hullWithin limit I J = .ready result) :
    result.Contains x ↔ I.view.HullContains J.view x

theorem contains_hullWithin_left
    (h : hullWithin limit I J = .ready result) :
    I.Contains x → result.Contains x

theorem contains_hullWithin_right
    (h : hullWithin limit I J = .ready result) :
    J.Contains x → result.Contains x

theorem contains_negWithin
    (h : negWithin limit I = .ready result) :
    result.Contains x ↔ I.Contains (-x)

theorem contains_addWithin
    (h : addWithin limit I J = .ready result) :
    result.Contains x ↔ I.view.AddContains J.view x

theorem add_mem_addWithin
    (h : addWithin limit I J = .ready result) :
    I.Contains x → J.Contains y → result.Contains (x + y)

theorem contains_subWithin
    (h : subWithin limit I J = .ready result) :
    result.Contains x ↔ I.view.SubContains J.view x

theorem sub_mem_subWithin
    (h : subWithin limit I J = .ready result) :
    I.Contains x → J.Contains y → result.Contains (x - y)

theorem contains_minWithin
    (h : minWithin limit I J = .ready result) :
    result.Contains x ↔ I.view.MinContains J.view x

theorem min_mem_minWithin
    (h : minWithin limit I J = .ready result) :
    I.Contains x → J.Contains y → result.Contains (min x y)

theorem contains_maxWithin
    (h : maxWithin limit I J = .ready result) :
    result.Contains x ↔ I.view.MaxContains J.view x

theorem max_mem_maxWithin
    (h : maxWithin limit I J = .ready result) :
    I.Contains x → J.Contains y → result.Contains (max x y)

theorem contains_absWithin
    (h : absWithin limit I = .ready result) :
    result.Contains x ↔ I.view.absUnchecked.Contains x

theorem contains_absUnchecked
    (h : raw.Contains x) :
    raw.absUnchecked.Contains |x|

theorem abs_mem_absWithin
    (h : absWithin limit I = .ready result) :
    I.Contains x → result.Contains |x|

theorem contains_mulWithin
    (h : mulWithin limit I J = .ready result) :
    result.Contains x ↔ I.view.MulContains J.view x

theorem mul_mem_mulWithin
    (h : mulWithin limit I J = .ready result) :
    I.Contains x → J.Contains y → result.Contains (x * y)

theorem contains_powWithin
    (h : powWithin limit workLimits I exponent = .ready result) :
    result.Contains x ↔ (I.view.powUnchecked exponent).Contains x

theorem pow_mem_powWithin
    (h : powWithin limit workLimits I exponent = .ready result) :
    I.Contains x → result.Contains (x ^ exponent)

theorem contains_splitWithin_left
    (h : splitWithin limit I point = .ready left right) :
    left.Contains x ↔ I.Contains x ∧ x ≤ toReal point

theorem contains_splitWithin_right
    (h : splitWithin limit I point = .ready left right) :
    right.Contains x ↔ I.Contains x ∧ toReal point < x

theorem splitWithin_contained
    (h : splitWithin limit I point = .ready left right) :
    (left.Contains x → I.Contains x) ∧
      (right.Contains x → I.Contains x)

theorem splitWithin_cover
    (h : splitWithin limit I point = .ready left right) :
    I.Contains x → left.Contains x ∨ right.Contains x

theorem splitWithin_disjoint
    (h : splitWithin limit I point = .ready left right) :
    ¬(left.Contains x ∧ right.Contains x)

theorem splitWithin_point_left
    (h : splitWithin limit I point = .ready left right) :
    left.Contains (toReal point) ↔ I.Contains (toReal point)

theorem splitWithin_point_not_right
    (h : splitWithin limit I point = .ready left right) :
    ¬right.Contains (toReal point)
```

For two nonempty bounded raw inputs, `HullContains` is exactly
`(I.lower.Contains x ∨ J.lower.Contains x) ∧
(I.upper.Contains x ∨ J.upper.Contains x)`. If either input is empty it is
the other input's membership predicate. Thus hull denotes the least interval
selected by the outer cuts and can contain points in the gap between disjoint
inputs; it is not their set union.

`AddContains` characterizes the computed summed cuts. Empty is absorbing;
otherwise it conjoins the sum lower cut and sum upper cut. A corresponding
side is unbounded if either input side is unbounded, and a finite summed cut is
strict if either contributor is strict. The successful image theorem consumes
both source membership proofs. A representation-independent tightness theorem
for the real Minkowski sum remains future work. Resource refusal has no
membership semantics.

`SubContains` is the directional crossed-cut analogue: left lower minus right
upper, and left upper minus right lower. Empty is absorbing, either relevant
unbounded input makes that output side unbounded, and finite strictness is
disjunction. `sub_mem_subWithin` proves the representation-independent image
enclosure. As for addition, a separate real Minkowski-image tightness converse
remains future work rather than a current claim.

`MinContains` uses the union of lower-cut predicates and intersection of
upper-cut predicates; `MaxContains` uses the intersection of lower-cut
predicates and union of upper-cut predicates. These characterize the exact
computed cuts. The corresponding image theorems are one-way enclosures of
pointwise real `min` and `max`; no converse set-image theorem is claimed.

Absolute value and natural power likewise expose their exact normalized
selected cuts and one-way pointwise image enclosures. Power distinguishes
nonempty exponent zero, positive odd, and positive even cases; the even case
maps the exact absolute-value hull. Neither operation exports an unproved
set-image converse.

Transactional splitting returns both sealed children or one resource refusal;
it cannot expose a partial pair. Empty bypasses point inspection. For a
nonempty input, the retained point, both finite source/point selectors, and
both selected child normalization costs are admitted before final sealing.
Successful children are exactly `I ∩ (-∞, point]` and
`I ∩ (point, +∞)`, so they remain inside `I`, cover it, and are disjoint.

The remaining target theorems include:

```lean
theorem mem_intersect : x ∈ᵢ I → x ∈ᵢ J → x ∈ᵢ intersect I J
theorem not_mem_empty : ¬x ∈ᵢ .empty
```

Each arithmetic operation has an image theorem. Representative shapes are:

```lean
theorem mem_mul : x ∈ᵢ I → y ∈ᵢ J → x * y ∈ᵢ mul I J
theorem mem_invAt : x ∈ᵢ I → x⁻¹ ∈ᵢ invAt p I
theorem mem_divAt : x ∈ᵢ I → y ∈ᵢ J → x / y ∈ᵢ divAt p I J
theorem mem_pow : x ∈ᵢ I → x ^ n ∈ᵢ pow I n
theorem mem_regularize : x ∈ᵢ I → x ∈ᵢ regularize p I
```

Proofs cover empty and unbounded inputs directly. They do not infer field laws
from interval operations.

### Total functions and domain conditions

The theorem statement follows Lean's function, including its values outside a
traditional analytic domain. For example, a reciprocal rule crossing zero
must account for `0⁻¹ = 0`. A logarithm rule may use a tight monotonic theorem
only after proving the input interval is positive. Otherwise it uses a theorem
for Mathlib's total `Real.log`, returns a coarse result, or reports the rule as
inapplicable.

A rule result records analytic side conditions separately from its interval:

- input lies in the theorem's domain;
- differentiability or continuity holds where a centered method uses it;
- a monotonicity sign is proved;
- a reduction identity is valid for the selected parameters.

This is more useful for proof construction than attaching an IEEE decoration
to every interval value.

## Trust model

There are three computational layers.

1. The planner and propagator evaluators run as compiled Lean code during
   elaboration. They may select precision, Taylor order, algebraic form,
   contractors, and split points. Their answers are untrusted.
2. Each retained rule application has a small soundness theorem. Expensive
   rules also have a rule-specific certificate and checker.
3. The replay elaborator applies those theorems, constructs kernel-checkable
   evidence for literal certificates, and emits the final proof. The Lean
   kernel checks that proof in the ordinary way.

The planner is never reduced in the kernel. The compiler does not certify any
mathematical fact. A compiler error may cause search to fail or propose bad
data, but bad data cannot satisfy the replay theorem.

Every kernel-facing checker must demonstrably reduce in the module that emits
the proof. Structural recursion is preferred, but explicit natural fuel and
well-founded recursion with an explicit `Nat` measure are permitted when
`decide +kernel` and `Lean.Kernel.whnf` probes show that the complete exposure
closure reduces and replay benchmarks remain acceptable. Auto-derived
lexicographic measures on multi-clause recursion are rejected when those probes
stick. A checker path must not contain an `@[extern]`-backed opaque constant,
and the emitting module must expose transitive helper bodies rather than assume
that an umbrella import recursively exposes them.

When the kernel-friendly specification and fast runtime shape differ, the
public name follows the repository's proved `@[csimp]` `*Impl`-twin policy,
never `@[implemented_by]`. A compiled precheck runs first, but raw proof
emission constructs the equivalent of
`of_decide_eq_true (Eq.refl true)` with the decision instance explicit and
without asking elaborator `isDefEq` to normalize the reflexivity slot. Compiled
and kernel evaluation are benchmarked separately before a checker is admitted
to generated proofs. This applies in particular to logarithm, bit-precision,
fold, and trace-validation helpers.

A compiled call to a Boolean checker is only a preflight optimization. It is
never converted into a proof. Every premise such as
`hcheck : check payload = true`, as well as program and trace validity, is
supplied by transparent kernel reduction (`rfl` where practical), ordinary
kernel `decide`, or an explicit theorem chain. If that construction is too
large or fails to reduce, replay fails. Splitting a certificate into chunks
does not change this rule; each chunk receives its own kernel-checkable
equality proof.

### Axiom contract

Every public tactic regression checks its theorem's axioms. CI also enumerates
every built-in registered soundness theorem and checker theorem and audits its
transitive axiom set. Before the library is released, those registrations,
representative proofs, and every PNT+ compatibility fixture must exclude:

- `Lean.ofReduceBool`;
- `Lean.trustCompiler`;
- generated declarations matching `*.native_decide.ax_*`;
- `sorryAx`;
- every project-local axiom.

The expected dependencies are ordinary mathematical axioms already used by
Mathlib, such as choice or quotient soundness when the invoked theorem needs
them. The audit reports the exact set rather than asserting an informal
"axiom-free" label.

A release source audit rejects declarations of `axiom`, `sorry`, or `admit`,
uses of `native_decide`, and uses of `Lean.ofReduceBool` anywhere in the
library family. Import tests ensure that a consumer of the logarithm rules
does not acquire unrelated unfinished obligations from trigonometric or
error-function modules. User registrations remain the user's trust choice,
but the trace and diagnostics identify them and their transitive axiom set can
be requested by the same audit command.

`native_decide` is banned even for a fallback or a supposedly temporary large
fixture. Small literal checks may use kernel `decide` when their transparent
reduction is measured and stable. Proof-producing tactics such as `norm_num`,
`ring`, and `linarith` are also admissible. Large batches use the certificate
scheme below rather than one enormous kernel reduction.

In particular, `norm_num` is a useful Mathlib-side way to discharge exact
rational leaves, but it is not required by `hex-interval`. The shared library
can replay rational arithmetic through exposed wrappers for core's
`Rat.normalize`, justified by the core `Rat.*_def` lemmas, or through a
canonical numerator/denominator checker. D2 compares these proof-facing
encodings with direct Mathlib `norm_num` leaves; the compiled planner remains
free to use the ordinary optimized `Rat` operations in every case.

## Program semantics and the golden theorem

The design below is the primary D2 candidate. The fixed requirement is a
generic soundness theorem over a validated shared program with semantic links
back to the quoted Lean terms. D2 selects the checker granularity, exact
`Natural.Prim` encoding, and balance between reflected regions and direct
theorem leaves before this representation is frozen.

The reified program is an array of typed instructions whose arguments refer to
earlier entries. A valuation assigns real values to free-variable nodes. The
program's `OpKey` table gives each instruction its real meaning; a chosen
`RuleKey` is only a method for enclosing that meaning.

In this candidate, the natural checker does not interpret arbitrary operation keys from the
extension registry. It has a fixed, kernel-visible `Natural.Prim` language for
variables, exact constants, negation, addition, subtraction, multiplication,
and natural powers. A validated natural region records the translation from
its program-local `OpId`s to those primitives. Adding a user propagator cannot
extend this trusted interpreter. Custom functions, alternate forms, and
adaptive steps replay through explicit theorem applications or
rule-specific checker theorems.

Natural interval evaluation has one generic theorem for such a validated
region:

```lean
theorem Natural.eval_mem
    (hregion : Natural.Region p region)
    (hinputs : Inputs.Mem valuation inputBox)
    (hcert : Natural.check region inputBox output cert = true) :
    Natural.eval region valuation output.node ∈ᵢ output.interval
```

The exact API may separate validation, evaluation, and the output lookup. The
essential point is that one induction over the shared program proves all
ordinary arithmetic instructions. Repeated subexpressions are evaluated and
proved once.

Reification also constructs semantic links. For each region boundary or
custom node, replay retains a proof that its program meaning equals the quoted
Lean term it represents. In particular, the root has an equality between the
checked program value and the original goal expression. Goal closure composes
`Natural.eval_mem` with this root link; it never concludes a theorem merely
about an internal program. A missing or ill-typed link is a reification
failure, not an unchecked assumption.

Every accepted instantiation extends this same contract. The extension is a
new immutable, topologically validated snapshot; each generated instruction
has either fixed natural semantics or an explicit semantic-link recipe, and
each new equality edge has a scoped equality proof. `Natural.eval_mem` is
applied to the validated snapshot actually referenced by the retained trace.
No theorem observes an in-place mutation of a previously checked program.

This theorem is the fast path for straight natural evaluation. Adaptive
derivations use additional theorem nodes for intersection, centered forms,
rewrites, contractors, and branches. The result is a hybrid proof:

- a reflected checker handles regular runs of simple SSA instructions;
- explicit theorem applications describe the shallow adaptive structure;
- rule-specific checkers handle Taylor remainders, range reduction, and other
  expensive leaves.

This avoids both extremes: a huge tactic-generated tree of low-level
inequalities, and a single giant Boolean reduction containing the entire
search.

## Propagator registration

Propagators use an explicit environment extension. They are not typeclass
instances. The registry can contain several methods for one head symbol and
can prioritize them without affecting elaboration of unrelated terms.

A registration supplies:

- the fully qualified head declaration and arity;
- the accepted argument and result domains;
- a compiled evaluator declaration;
- an initial cost class and supported effort range;
- an optional state constructor and cache invalidation rule;
- a proof recipe that names either a direct theorem or a checker soundness
  theorem;
- optional backward contractor, rewrite, local-refinement, and split-suggestion
  declarations;
- optional bounded-instantiation triggers, generated-operation schemas, and
  semantic/equality proof recipes;
- a stable rule name and natural certificate-schema version, together forming
  the `RuleKey` used in diagnostics and replay traces.

For a simple rule, the soundness theorem has this form:

```lean
theorem add_check_sound
    (hcheck : addCheck I J out payload = true) :
    x ∈ᵢ I → y ∈ᵢ J → x + y ∈ᵢ out
```

For a transparent checked operation, the registration may recompute
`addWithin` from its recorded limit and inputs, discharge the successful-result
equation, and apply `add_mem_addWithin` without a separate certificate payload.
A Taylor rule instead stores its polynomial degree, reduced argument, endpoint
values, and remainder witness, then uses a checker theorem for those fields.

The registration command validates the theorem's conclusion against the head
symbol and argument mapping. It also rejects duplicate `RuleKey`s.
It cannot turn an invalid theorem into a proof. If a compiled evaluator and
its theorem disagree, replay fails with the rule name and candidate data.

Applicable rules are ordered by declared cost class, explicit priority, and
versioned stable rule key. Import order and fresh declaration identifiers are not
tie-breakers. Registrations are scoped through the environment extension, so a
function module contributes rules only when imported.

### User extensions

A user-defined real function can register one or more forward rules without
modifying the tactic. A minimal rule needs only an executable enclosure and a
theorem proving it. Optional methods are independent registrations.

The intended authoring progression is:

1. state a direct range theorem on dyadic input intervals;
2. implement the executable endpoint calculation;
3. package any nontrivial arithmetic as a small certificate checker;
4. register the rule under the function's head declaration;
5. add typical, boundary, and adversarial conformance cases.

An approximation theorem plus a computable modulus of uniform continuity can
produce a generic forward rule. The rule partitions the input interval finely
enough for the modulus, evaluates certified point approximations, and takes an
outward hull. The modulus may depend on the input interval. This construction
is a later convenience API, not a requirement imposed on every function.

## Reification

Reification uses `Qq` and `Lean.Meta`. It preserves user sharing and introduces
additional common-subexpression sharing after normalization.

### Supported initial language

The first arithmetic language contains:

- real variables and exact integer, rational, and decimal constants;
- negation, addition, subtraction, multiplication, division, inverse, and
  natural powers;
- `abs`, `min`, `max`, and the syntax of `Real.sqrt` (whose first enclosure
  rule arrives at D7, so earlier use safely reports no applicable rule);
- named real constants with registered nullary rules;
- registered unary and binary functions.

The D5 elementary-function milestone adds `Real.sin` and `Real.cos`. D7 adds
`Real.exp`, `Real.log`, `Real.sqrt`, `Real.atan`, and `Real.rpow` on proved
positive bases. The LeanCert compatibility milestone then audits the rest of the expression
heads its downstream users need, including hyperbolic functions, `arsinh`,
`atanh`, `sinc`, and `erf`. A name in the reified language is not considered
supported until at least one sound propagator covers its stated domain.

### Context facts

The frontend recognizes:

- strict and non-strict comparisons with rational expressions;
- equality as two closed bounds;
- all finite and one-sided `Set.Ixx` membership forms;
- conjunctions of recognized facts;
- local definitions that are definitionally equal after elaboration;
- the intrinsic fact `0 ≤ (n : ℝ)` for every reified cast from `n : ℕ`, proved
  by `Nat.cast_nonneg` even when no local hypothesis states it. Casts from `ℤ`
  contribute no sign fact by themselves.

Facts about arbitrary derived terms are retained. They are not restricted to
free variables. Unknown hypotheses remain in the context but do not enter the
interval program.

`interval only [...]` restricts user hypotheses, not intrinsic type-driven
facts such as nonnegativity of a natural-number cast.

A propositional hypothesis `h : s = t` does not merge SSA nodes. It becomes a
source constraint with `SourceId h` and bidirectional bound transfer. This
avoids cycles such as identifying the node for `x` with its descendant
`x + 1`, and it lets inconsistent equalities be contracted and reported.

### Certified normalization

Normalization is a portfolio, not one irreversible simplification pass.

- Casts and exact rational literals receive canonical nodes.
- Syntactic identities such as `sub_eq_add_neg` can share a common primitive
  form.
- When two operands have the same `NodeId`, proved identities such as
  `sub_self` and `add_neg_cancel` create an exact zero alternate. CSE alone
  would not make interval subtraction dependency-aware; this rule is what
  closes `x - x` and `10^9*x - 10^9*x + 1` exactly.
- Polynomial fragments may keep the original form, a Horner form, a centered
  form, and a normalized polynomial form. Each alternate has a proof of
  equality to the original node.
- A source equality may justify a contextual alternate. The first required
  case reduces the target `x^4 + y^4` modulo `x^2 + y^2 = 1` to
  `1 - 2*x^2*y^2`, with a `ring` or `linear_combination` proof recipe. How far
  to extend polynomial ideal reduction is an explicit experiment; the tactic
  does not silently normalize every goal modulo every equality.
- Repeated finite sums use a fold instruction instead of an expanded chain of
  additions.
- Function-specific rewrites such as `exp (-log N / k)` or trigonometric range
  reduction are registered theorem applications, not unchecked expression
  mutation.

Blind ring normalization can improve one dependency and destroy another. The
planner may evaluate several proved forms and intersect their ranges.
`maxProgramNodes` and `maxFormsPerNode` apply while these alternates are
materialized. If the original DAG alone exceeds `maxProgramNodes`, reification
fails safely with a budget diagnostic. If alternate generation reaches either
limit, the original DAG remains valid, skipped alternates are reported, and
search continues without them.

### Instantiation frontend

The frontend supports versioned instantiation rules whose triggers match
expressions, source facts, or newly proved bounds and propose additional
expressions for the shared program. A rule can return:

- new typed SSA instructions with a canonical expression key;
- equality edges to existing nodes;
- derived interval facts about a generated residual or difference node;
- side conditions and a theorem or certificate recipe for replay;
- suggestions for contractors or local partitions that become applicable to
  the new node.

For example, a monotonicity rule may need the shaped expression `a*b ≤ a*c`
even though neither product appears in the original goal; it can instead add
the difference node `a*b - a*c` and derive its upper bound from `0 ≤ a` and
`b ≤ c`. An inverse exponential contractor may introduce `log y` while
processing `y = exp x`. These are not trusted e-matching consequences: the
program extension and every first fact about it are replayed from the rule's
registered theorem.

Triggers are indexed by head symbols and explicit patterns rather than
recursive typeclass search. The engine deduplicates substitutions and generated
expressions, enforces generation and node budgets, and records why a tempting
trigger was suppressed. Branch-local inputs produce branch-scoped facts and
edges. The companion validates each new program snapshot before assigning any
goal metavariable.

The first prototype compares eager bounded closure, propagation-epoch
instantiation, and fully lazy append-only generation. It also compares
`grind`-style E-matching, a structural `apply_rules` loop, and rule-supplied
direct proposals. Success rate, useless instances, program growth, proof size,
and deterministic work decide the production default.

## Tactic interface

The planned syntax is:

```lean
interval
interval [h₁, h₂]
interval only [h₁, h₂]
interval (config := { maxSplits := 8, maxEffort := 80 })
interval?
interval_bound e
```

The tactic parser interprets the partial record in `(config := { ... })` as an
update of the fully populated `Hex.Interval.defaultConfig`; users need not
supply every budget field. `interval?` prints a complete versioned
configuration when exact search reproducibility matters. Default budget values
may be tuned before release and are benchmark data, not soundness constants.

`interval [h₁, h₂]` adds the named facts to the local facts already recognized.
`only` restricts hypothesis ingestion to the supplied facts. `interval?` runs
the same proof search, reports the successful action summary and a pasteable
configuration, then closes the goal. `interval_bound e` leaves the goal
unchanged and reports the best enclosure of `e` together with a pasteable
`have` statement whose proof is `by interval`. If an exact rational source cut
is stronger than its dyadic working projection, the report retains the exact
cut.

After subdivision, “best” means the proved hull over every live or pending
leaf, never the enclosure from one favorable branch. Replay uses the partial
branch tree to prove that hull even when the original search result is
`unknown`.

The programmatic frontend exposes a `deriveBound` entry point for other
tactics. It returns an exact proof-facing bound bundle, including its endpoint
encoding, a dyadic projection when requested, proof expressions for the
selected global cuts, and search diagnostics. Under the dyadic prototype it
also retains stronger exact rational source cuts; under a rational working
backend, propagated rational cuts are first-class rather than mislabeled as
sources.
This is the future integration seam. This SPEC does not register it with
`grind`.

### Configuration

The stable configuration fields are:

```lean
structure Hex.Interval.Config where
  policy         : Name := `balancedV1
  maxProgramNodes : Nat
  maxFormsPerNode : Nat
  maxGeneratedNodes : Nat
  maxEqualityEdges : Nat
  maxInstantiations : Nat
  maxGenerationDepth : Nat
  maxSteps       : Nat
  maxRuleCalls   : Nat
  maxEffort      : Nat
  maxSplits      : Nat
  maxDepth       : Nat
  maxLeaves      : Nat
  maxLocalPieces : Nat
  maxEndpointHeight : Nat
  maxAlignmentShift : Nat
  maxTraceNodes  : Nat
  maxProofNodes  : Nat
  maxPayloadEntries : Nat
  maxPayloadBytes : Nat
  maxCheckerSteps : Nat
  rules          : RuleFilter
```

The displayed `balancedV1` value is the D4 prototype default, not a promise to
make it the first public release default. The versioned name remains available
for pinned experiments if measurements select a different default alias.

The implementation also has an emergency timeout, but test expectations and
successful replay do not depend on a particular machine reaching it.

`Config.policy` is resolved in the fixed importing environment through the
companion's versioned registry to a pure `Policy` implementation. A missing,
ambiguous, or wrong-kind name is a configuration error before search starts;
it never falls back to an environment-dependent arbitrary choice. Determinism
claims quantify over a fixed import closure and registry contents as well as a
fixed program and configuration.

Effort is a natural-number precision tier. Rules are encouraged to interpret
effort `p` as an error target near `2^-p`, but no monotonicity or error law is
part of the generic interface. The scheduler measures actual gains.

## Built-in enclosure methods

The tactic tries cheap natural evaluation first and then selects from the
methods below. Every method returns an ordinary interval and a proof. The
planner may intersect several results.

### Exact arithmetic

The required initial rules are constants, identity, negation, addition,
subtraction, multiplication, natural powers, `abs`, `min`, and `max`. Inverse
and division use the precision-indexed outward operations, with sign-specific
rules and a sound coarse fallback. The `D7` elementary portfolio adds square
root using monotonicity on nonnegative inputs and accounts for Mathlib's value
on negative inputs when the interval is not known nonnegative.

Exact arithmetic primitives preserve their tight endpoint-attainment flags.
An approximate elementary or user rule may deliberately close a cut when that
is the cheapest proved enclosure. The diagnostic record distinguishes a
semantic loss of openness from numerical width.

### Centered form and automatic differentiation

For a function of the relevant free variables, the first dependency-reduction
method is the multivariate mean-value enclosure

```text
f(X) ⊆ f(c) + sum_i (X_i - c_i) * partial_i f(X).
```

Here `X` is a bounded box, `c` lies in `X`, and every segment from `c` to a
point of `X` stays within the certified differentiability domain. Derivative
intervals enclose each partial derivative on that whole box. An unbounded
dependency coordinate must first be bounded or omitted by a proved
independence result. The univariate formula is the one-coordinate special
case.

Forward automatic differentiation computes value intervals and a sparse
gradient on the shared program. If one partial derivative interval has
constant sign, the rule can evaluate the appropriate boundary face instead.
If a second derivative later has constant sign, convexity can reduce a maximum
to boundary faces.

Nondifferentiable nodes return an unknown derivative interval and let natural
evaluation continue. They do not invalidate unrelated parts of the program.
The planner first applies centered refinement at the requested output and at
high-influence internal nodes. Applying it at every node is an optional policy
for comparison.

### Polynomial forms

Polynomial expressions receive several inexpensive alternatives:

- natural evaluation with shared subexpressions;
- Horner evaluation under several variable orders;
- centered first-order evaluation;
- Bernstein coefficients over a bounded box;
- monotonicity from derivative intervals.

The first release need not implement every item. The registration and policy
interfaces must permit them without changing the proof trace format.
Bernstein and centered forms are prioritized before affine arithmetic because
they require less certificate machinery and address many small nonlinear
goals.

### Backward contractors

Forward-backward propagation follows the HC4 pattern:

1. evaluate every affected instruction forward;
2. intersect a constraint node with its required interval;
3. apply inverse rules to narrow arguments;
4. re-enqueue only instructions whose input facts changed.

Initial contractors cover addition, subtraction, sign-separated
multiplication, square, `abs`, and monotone elementary functions. A contractor
that naturally returns a union either creates two solver branches or uses a
later two-component interval type. It never drops one alternative.

When the tactic proves a goal by eliminating counterexamples, it adds the
logical negation of the target comparison and proves that every resulting
branch is empty. The contractor theorem states that it preserves all possible
counterexamples. This prevents circular use of the desired conclusion.

### Affine arithmetic and Taylor methods

Affine forms are a later registered abstract domain. They preserve linear
correlation with noise symbols and convert their final result back to an
ordinary interval fact. Symbol compaction and nonlinear remainder bounds are
part of their certificate.

Second-order midpoint Taylor bounds come before full Taylor models. They give
derivative-sign, monotonicity, and convexity reductions without introducing a
general multivariate polynomial remainder representation. Full Taylor models
remain a later challenge milestone. They do not block the initial tactic.

## Elementary functions

Point enclosure and range enclosure are separate APIs.

### Certified point bounds

A point algorithm works only with exact dyadic or rational data:

1. apply a proved argument-reduction identity;
2. evaluate a convergent series or rational approximation on a small domain;
3. prove an outward remainder bound;
4. reconstruct the original function with proved identities;
5. in the dyadic prototype, round the final cut outward to the requested
   dyadic precision; a selected rational backend supplies its corresponding
   exact projection contract.

The certificate contains the reduction parameters, approximation order,
endpoint values, and remainder witness. The planner selects them. The checker
verifies them.

### Sine and cosine

The initial sine rule follows the existing experiment on `[-1,1]`: evaluate a
rational Taylor polynomial and bound the Lagrange remainder. Its dyadic D2
candidate uses dyadic endpoints in hot arithmetic and retains the experiment's
Mathlib proof of the analytic remainder; the backend comparison measures the
same certificate with rational working endpoints.

Outside that range, two proved methods may coexist:

- recursively apply `sin x = 3 sin (x/3) - 4 sin(x/3)^3` until the argument is
  small, then propagate the reconstruction polynomial;
- use certified bounds for `π`, reduce modulo a period, and isolate critical
  points between certified dyadic guards when needed.

The triple-angle method avoids requiring `π` for the first working rule. The
periodic method is necessary for tight ranges and large-argument performance.
If an interval covers a complete period, the range rule returns `[-1,1]`
without point evaluation. Ambiguous period indices cause a precision increase
or a dyadic global split. An exact symbolic critical point may be handled
inside the range theorem, but it is not inserted as an irrational solver cut.
Very large arguments have an explicit work cap and a sound coarse fallback.

Exact identities such as `sin Real.pi = 0` are rewrite rules. Increasing
numeric precision is not a substitute for an exact symbolic theorem.

### Exponential and logarithm

`Real.exp` uses monotonic endpoint evaluation plus certified point bounds.
Range reduction may use repeated halving and squaring, which directly covers
the PNT+ pattern that was manually rewritten as
`(exp (C * s / 64)) ^ 64`.

`Real.log` uses monotonicity on a proved positive interval. Rewrites for
`exp (log x)` and expressions such as `exp (-log N / k)` require explicit
positivity side conditions and are registered with proofs. Nested logarithms
are reified normally once each inner interval is positive.

Nullary `π` propagation returns successively tighter dyadic enclosures.
Square root uses integer square-root bounds after scaling. The same point-rule
interface later admits `atan`, hyperbolic functions, `sinc`, and `erf`.

Positive-base real powers use the proved identity
`x ^ y = exp (log x * y)` together with a direct monotonicity rule when the
signs of `log x` and `y` make it sharper. A dedicated unary rule for `x ^ x`
retains the correlation that a generic binary `x ^ y` rule loses. This rule is
required by the IMO 2020 and BKLNW corpora. Inputs containing zero or negative
bases use the exact Mathlib definition and separate the necessary cases rather
than importing the partial-domain convention of a numerical library.

### Rule state and local partitions

A higher-effort elementary rule may refine its previous partition and reuse
certified point evaluations. It can split its input interval locally, prove
that the pieces cover it, evaluate each piece, and return their hull. This
does not duplicate the complete solver state.

Function-specific split suggestions include zero, domain boundaries, kinks,
poles, and dyadic guards enclosing certified trigonometric critical points. A
theorem-specific local partition may use symbolic landmarks inside its
payload; a global split suggestion always names a dyadic cut. The scheduler
decides whether local refinement, more endpoint precision, or a global case
split has the best predicted gain.

## Efficient replay

Proof efficiency is a correctness-adjacent release requirement. A tactic that
finds a bound quickly but emits a theorem that takes minutes to elaborate does
not satisfy this SPEC.

### Sharing

- Every SSA fact is proved at most once per branch.
- Proofs established before a split are `let`-bound outside both children.
- The derivation slice removes unused propagations and every failed probe.
- When equal cuts have several derivations, replay prefers the lower estimated
  proof cost.
- Repeated constants, Taylor tables, and fold certificates are shared.

### Batch and fold certificates

Finite sums and arrays are not expanded into thousands of tactic applications.
The reifier recognizes `Finset` ranges and other supported folds. A batch
certificate contains the element enclosures and a balanced aggregation tree.
A generic theorem proves the fold bound.

Large batches are checked in measured chunks and combined by a balanced proof
tree. The initial chunk ceiling is selected by batch-replay measurements. It is
not hard-coded by this SPEC. This avoids both a linear-depth proof term and one
enormous Boolean reduction. Kernel-facing recursive checkers use exposed
definitions and reduction-stable payload types. They do not rely on opaque
array equality reduction across module boundaries.

The BKLNW sums with upper limits 29, 37, 63, 145, 289, and 433 are the scaling
ladder. Their index set is `Icc 3 N`, so they contain `N - 2` summands. The
13,590-cell FKS2 corpus is the full `local` acceptance test used by the
migration and release criteria. Per-PR
`core` uses a small deterministic sample, while per-PR `ci` uses a measured
medium shard. The complete data is streamed from split JSONL fixtures; it is
not generated as one enormous Lean source file. JSONL is only data transport:
the runner turns each measured chunk into the same proof/checker invocation,
elaborates it, kernel-replays it, and includes the resulting theorems in the
axiom audit. A compiled pass over all cells without those proof obligations
does not satisfy the migration criterion.

### Failure during replay

Replay is normally run only after compiled search finds a derivation. If a
rule candidate does not check, the tactic reports:

- rule name and version;
- input and proposed output intervals;
- certificate field or theorem application that failed;
- source location of the registration.

It does not try `native_decide`, insert `sorry`, trust the candidate, or hide
the failure by returning a weaker theorem.

## Evidence and resulting requirements

### Research note and sine experiment

The [interval arithmetic note](https://hackmd.io/ZagrUv95RFSU-7WP9TNxUQ)
supplies the central model adopted here:

- saturate all shared subexpressions with bounds;
- associate stateful forward propagators with function symbols;
- measure the gain from an action and use that sensitivity to choose later
  work;
- allow function-specific subdivision suggestions;
- consider backward propagation without requiring it for the first version;
- let effort trade work for tighter output without demanding a global law;
- regularize growing rationals by sound outward compression;
- permit multiple propagators for one symbol;
- derive propagators from point approximations and moduli of continuity;
- keep rule selection out of recursive typeclass search.

The associated
[sine experiment at commit `f174f318`](https://github.com/kim-em/mathlib4/blob/f174f3188252c99f17be96feee42b242cc465b2d/Mathlib/Analysis/SpecialFunctions/Trigonometric/Intervals.lean)
demonstrates rational Taylor bounds for sine, unary and binary forward rules,
an effort parameter, and the need for open and unbounded rule domains. It only
sketches outward regularization: `Real.rounding.mem` still contains three
`sorry`s at that commit. This SPEC retains the proved ideas but does not
inherit those unfinished proofs. It replaces the fixed closed rational
interval and speculative heterogeneous type list with exact dyadic cuts, SSA
instructions, and an explicit rule registry.

### Lean Zulip requirements survey

The public Lean Zulip discussion supplies both early requirements and concrete
failure cases.

- The first
  [interval arithmetic and Lean thread](https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/interval.20arithmetic.20and.20Lean/near/211251141)
  asks for rational certificates, square root, sparse numerical linear algebra,
  special-function error bounds, and a two-variable positivity problem split
  into about 80 regions. It also records immediate numerator and denominator
  growth with unrestricted exact rationals. This supports outward
  regularization and a strict separation between fast candidate computation
  and Lean checking.
- The
  [representation and tactic thread](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Interval.20arithmetic.20--.20what.20approach.3F/near/212077493)
  argues for abstract real enclosure theorems with rational certificates,
  notes that infinite endpoints are necessary, and separates interval
  operations from the witness values they enclose.
- The
  [verified software floating-point thread](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Verified.20software.20floating.20point/near/419936247)
  describes a fixed-integer closed-interval implementation with arithmetic,
  powers, `exp`, and `log`. Its nonempty-closed representation and sentinel for
  the whole interval are too narrow here, but its endpoint monotonicity and
  empirical tightness measurements are useful comparison points.
- The
  [constant real inequality tactic thread](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/An.20interval.20tactic.20for.20constant.20real.20inequalities/near/445456796)
  includes `exp 1 < 2.7182818284591`, a logarithm product, nested `exp` and
  `log`, and real powers. It also records ordinary reduction getting stuck on
  a well-founded `Nat.log2`, then succeeding after a structural or fueled
  implementation replaced it. Later repository experiments show that explicit
  `Nat`-measure well-founded recursion can itself kernel-reduce when definitions
  are exposed; the durable requirement is the mechanical reducibility probe
  above, not a blanket ban on that recursion style.
- A newer
  [transcendental `norm_num` discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/norm_num.20extension.20for.20Real.2Eexp.2C.20Real.2Elog.2C.20sin.2C.20cos/near/612728678)
  links the kernel-clean
  [`lean-interval-bounds` prototype at `1586bcb`](https://github.com/peti12352/lean-interval-bounds/tree/1586bcbc5ea84e5ed0ecdbdc941dbf18d4055d48).
  It adaptively tries Taylor degrees for rational `exp`, `log`, `sin`, and
  `cos` bounds, has a standalone extensible handler registry, and checks that
  representative proofs avoid `native_decide`. Community feedback there
  independently favors a standalone extensible tactic over making interval
  search a `norm_num` extension. Its point-focused scope and first-success
  handler loop remain migration baselines, not the desired propagation
  architecture.
- The
  [`by_approx` discussion](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/New.20.60by_approx.60.20tactic.20for.20proving.20real.20inequalities/near/407069390)
  identifies one global precision, discarded work, unrounded rationals, and
  repeated `norm_num` construction as failure modes. Local error attribution,
  memoized facts, and node-specific effort directly address them.
- The
  [interval component API discussion](https://leanprover.zulipchat.com/#narrow/channel/345428-mathlib-reviewers/topic/components.20for.20interval.20tactics/near/532547860)
  asks for user-defined propagators and the regression
  `x^2 + y^2 = 1 ⊢ x^4 + y^4 ≤ 1`. It also exposed awkward definitional
  interactions between `WithTop` and `WithBot`. Dedicated lower and upper cut
  types avoid making those implementation details part of the theorem API.
- A public
  [`grind` failure analysis](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/grind.20failures/near/599591286)
  gives a concrete expression-generation failure: a theorem's E-matching
  pattern has the shape `a*b ≤ a*c`, but those product expressions are absent
  from the local expression database, so no instance is produced; a useful
  distributive equality can likewise remain outside the relevant congruence
  classes. This is the direct regression for the bounded instantiation
  frontend above. Saturating bounds only on syntax that happened to occur in
  the original goal is not enough.
- The
  [sharp inequalities thread](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Proving.20sharp.20inequalities.20using.20interval.20arithmetic/near/446334247)
  supplies an entropy inequality with a sharp endpoint and singular derivative,
  plus the dependency example `10^9*x - 10^9*x + 1`. A good tactic needs
  analytic boundary lemmas, alternate forms, and a diagnosis of dependency
  loss rather than endless uniform bisection.

The survey also requires the engine to return its best proved interval even
when no contradiction or target closes. Interactive proofs, plotting, and
integral bounds all consume such facts. `interval_bound` is therefore part of
the first frontend, not a later diagnostic addition.

The complete direct-message history between Kim Morrison and Bhavik Mehta was
also reviewed for requirements. Because that correspondence is private, this
SPEC does not quote it or reproduce distinctive unpublished problems. Its
technical consequences are recorded here: count rational height in policy
cost, test continued-fraction regularization, compare backward propagation
against function-directed subdivision empirically, retain a first-class
best-bound query, include exact-`π` and very-high-precision logarithm stretch
certificates, and test nonlinear-equality handoffs plus active-subset split
planning. Public artifacts linked by that discussion are cited in the corpus
below; the unpublished planner case is represented by a synthetic generator.

The working endpoint choice remains empirical. The primary D2 candidate uses
arbitrary dyadics for propagated facts and preserves exact rational source
facts. The backend-comparison milestone compares that hybrid against a
separate exact-rational search prototype with deliberate regularization on
tactic-scale examples. D2 records a selection before endpoint-dependent trace
formats are frozen; the public search protocol and certificate concepts do not
prejudge the outcome.

### Existing `bound` tactic

Mathlib's `bound` tactic recursively combines monotonicity, positivity, and
local inequalities through an Aesop rule set. It already proves structural
goals such as `(exp x)^2 ≤ (exp y)^2` from `x ≤ y`, and it can move between a
goal like `0 ≤ a*c - b*c` and the simpler facts `b ≤ a` and `0 ≤ c`.

`interval` must be compared against this existing capability rather than
claiming every structural inequality as new. The division of responsibility
is:

- `bound` applies local order lemmas to the expression already present;
- `interval` maintains simultaneous numerical enclosures, attributes error,
  retries rules at local effort, contracts a shared program, and performs
  certified case splits;
- either tactic may use an ordinary theorem produced by the other, but neither
  tactic's search is trusted.

The common regressions include:

- `x ≤ y ⟹ (exp x)^2 ≤ (exp y)^2`;
- `0 ≤ x ∧ x ≤ y ⟹ 0 ≤ x*(y-x)`;
- `a ≤ b ∧ x ≤ y ⟹ a*(y-x)^3 ≤ b*(y-x)^3`.

Measurements compare an explicit worklist policy with Aesop-style
backtracking. Stable priorities, bounded backtracking, and a traceable
tie-break are required because tactic outcomes must not depend on fresh
identifier order.

### LeanCert and PNT+

The originally inspected LeanCert snapshot is
[`31579b5`](https://github.com/alerad/leancert/tree/31579b55618d11e4fbe622a6b5e30b0359b2ee6d).
The current PNT+ audit snapshot is
[`21998bb`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/21998bb6196b56789f72a52656a781a75e134eb0).
Its
[lakefile](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/21998bb6196b56789f72a52656a781a75e134eb0/lakefile.toml)
pins LeanCert `v4.32.2.2` at commit
[`58edbea`](https://github.com/alerad/leancert/tree/58edbea59458e9b010262238eaca27b6e0240dae).
The earlier detailed source audit used PNT+ snapshot
[`be5e07e`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/be5e07e04cde20c5ceabf63759bd097a9c88173f)
and its LeanCert `v4.32.1` pin. The audited `interval_decide` totals and file
set are unchanged between those snapshots: the current tree still has 290
textual occurrences across the same 15 files. The newer LeanCert pin has
substantial new router, integration, root-finding, algebraic, and trust-mode
APIs. Those APIs
are not silently claimed as PNT+ requirements here; replacing LeanCert beyond
the API actually exercised by PNT+ requires a separate refreshed audit.

The useful LeanCert ideas are a small semantic expression language, a golden
soundness theorem, exact rational and dyadic evaluators, affine arithmetic,
derivative-sign pruning, and untrusted discovery followed by checked
evaluation. The migration keeps those ideas.

The following comparison originally described the `31579b5` snapshot. The
current `58edbea` baseline adds a semantic router and explicit
[`kernel`, `native`, and `auto` verification modes](https://github.com/alerad/leancert/blob/58edbea59458e9b010262238eaca27b6e0240dae/docs/architecture/trust-model.md).
Comparative runs must use the exact PNT+ pin: its kernel mode is the
trust-equivalent baseline, while its default native mode is reported separately
as a compiler-trusting performance reference. The requirements below record
the remaining design differences rather than attributing superseded
limitations to current LeanCert.

- At the older audit snapshot practical tactics usually closed checks with
  `native_decide`. The current pin can instead require kernel reduction and
  never fall back. Hex likewise excludes `Lean.ofReduceBool`,
  `Lean.trustCompiler`, and generated
  `<decl>._native.native_decide.ax_*` dependencies from claimed kernel-only
  results, together with `sorryAx` and every project-local axiom forbidden by
  the Axiom contract above.
- `IntervalRat` represents only nonempty finite closed intervals. This library
  represents empty, open, half-open, and unbounded intervals.
- The current LeanCert pin has a semantic router. Hex's distinct requirement is
  independently registered package methods whose measured outcomes can drive
  escalation among precision, form, rewriting, propagation, and subdivision;
  comparative measurements include LeanCert's current router.
- Raw-expression reification has bespoke cases and proof-tree growth for large
  sums. This library uses a shared program and generic fold certificates.
- Manual rewrites and fixed midpoint depths are common downstream. This
  library registers proved rewrites and arbitrary split suggestions.
- Heavy verified facts are sometimes separated from sorry-bearing public
  interfaces. This library requires the ordinary public theorem to replay its
  certificate and rejects `sorryAx` in the acceptance audit.

The LeanCert
[axiom audit](https://github.com/alerad/leancert/blob/31579b55618d11e4fbe622a6b5e30b0359b2ee6d/Tests/AxiomAudit.lean)
and PNT+ PR [#922](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/922)
provide regression expectations for the trust boundary.

PNT+ supplies the principal real-world corpus:

At the current pinned snapshot it contains exactly 280 actual `interval_decide`
invocations, and 290 textual occurrences including ten explanatory prose or
comment mentions, across 15 files. These counts define the audit surface, not a
promise to clone every LeanCert API or preserve PNT+ source syntax. A checked
manifest records the PNT+ commit, LeanCert pin, Lean toolchain and Mathlib
revision, every executable occurrence's file and enclosing declaration, raw
textual matches by file and line, and the generated batch families that one
source occurrence expands into. Declaration labels are the nearest preceding
declaration header found by the lexical scan, not elaborated ownership. Every
entry that represents executable or imported behavior is ultimately classified
as one of:

- accepted unchanged by a Hex frontend;
- accepted after a documented PNT+ source rewrite or proof reorganization;
- replaced by a stronger shared Hex theorem or numerical provider;
- unrelated to the interval migration and retained through another dependency;
  or
- redundant, malformed, or a known false target with an expected-failure
  enclosure.

Before the D8 migration is performed, `pending` is an explicit allowed state;
raw matches in comments or strings are classified `not-a-call`. Qualified
LeanCert references are lexical audit evidence classified `inventory-only`;
the six imported-interface records, rather than every namespace-open token,
carry the migration obligation. The ordinary per-PR structural gate permits
`pending` so that adding the inventory does not pretend the port already
exists. The D8 migration/release gate must run the same checker with
`--require-classified`, which rejects every remaining obligation marked
`pending`. A completed classification also carries structured evidence: an
accepted fixture, documented rewrite, stronger replacement theorem, retained
dependency, or expected-failure fixture as appropriate. The release claim
requires both this classified manifest and the referenced ported proofs; a
status label alone cannot establish coverage. The inventory checker validates
that evidence references are structured and nonempty and that repo-relative
proof paths exist; the release profile must also build and axiom-audit the
referenced proof fixtures.

The first classified acceptance probe covers the pinned declarations
`LogTables.log_2_gt` and `LogTables.log_2_lt`. The Mathlib-free
`PntLogTable` package watches an exact-input fact for `2`, runs the generic
policy session, and emits one package-owned two-sided-window fact. Its Mathlib
companion interprets the opaque logarithm operation, checks the stronger
`Real.log_two_gt_d9` and `Real.log_two_lt_d9` theorems, and replays the exact
event through `ProofFrontend` before closing the original six-decimal
conjunction as an ordinary theorem. Conformance rejects a changed payload,
input assumption, output node, or output fact and audits the closed theorem's
axioms. These two records are classified as replacements by stronger numerical
provider results, with the exact Mathlib theorem recorded explicitly; no
LeanCert declaration is imported.

This probe establishes the package/planning/replay path, not the eventual
numerical logarithm algorithm. Its four-element finite fact lattice and its
reuse of Mathlib's existing point bounds are deliberately local. It does not
satisfy the high-accuracy table, arbitrary input, nested-logarithm, range
reduction, or package-owned Taylor-series milestones, and must not be counted
as evidence for those records.

The next classified probe covers inventory record 404,
`LogTables.log_log_6_58_gt`.  `PntNestedLog` runs one registered logarithm
handler twice over the three-node graph for `log (log 6.58)`: an exact rational
source fact produces the strict enclosure
`1.884034 < log 6.58 < 1.884035`, then the second event consumes precisely that
positive enclosure to prove `0.633415 < log (log 6.58)`.  The Mathlib companion
checks both table entries from `Real.abs_log_sub_add_sum_range_le`; the outer
schema uses the inner assumption and logarithm monotonicity rather than a
pre-existing nested-log theorem.  Chronological replay and `ProofFrontend`
close the source theorem.  A domain-isolation mutation removes the exact
source fact and replaces the inner enclosure by one that includes zero; it is
domain-unknown to the planner and rejected by replay.  Removing the source is
deliberate because retaining it would let the first rule refine the mutated
inner fact back to the strict positive table enclosure.

This is a reusable two-stage dependency and domain-rejection vertical, but its
runtime numerical provider is still a finite package-owned table.  It neither
accepts arbitrary rational inputs nor constructs Taylor coefficients at
runtime, and therefore is not evidence for the general logarithm or certified
table-building milestones.  Its private Mathlib proofs use the general Taylor
remainder theorem only to validate the finite entries at kernel replay time.

The next classified acceptance probe covers the numerical leaf in
`LogTables.exp_neg_lt_1e_neg_100` while preserving the source theorem's useful
monotone shape. At the pinned commit, the enclosing declaration is exactly
`lemma exp_neg_lt_1e_neg_100 {x : ℝ} (hx : 231 ≤ x) :
Real.exp (-x) < 1e-100`; after proving the boundary at `231`, its source proof
uses exponential monotonicity. The classification therefore records the full
reusable declaration shape, not only the inventory's tactic-line snippet.

The Mathlib-free `PntExpTail` package consumes an input fact `y ≤ -231` and
retains a four-field certificate: reduction point `231`, decimal exponent
`100`, and the rational point enclosure `46/125` for `exp (-1)`. Its Mathlib
companion uses `Real.exp_neg_one_lt_d9`, `Real.exp_nat_mul`, and an exact
rational-power comparison to prove the boundary. It then reuses that result
for every `231 ≤ x` by exponential monotonicity. The generic runtime
chronology and `ProofFrontend` close both
`Real.exp (-(231 : ℝ)) < 1e-100` and
`231 ≤ x → Real.exp (-x) < 1e-100` as ordinary theorems.

This fixture treats Lean scientific notation exactly: a checked lemma exposes
`(1e-100 : ℝ)` as `1 / 10^100`, and no floating-point conversion enters the
certificate. Mutating the reduction point to `230` is an incompatible
enclosure, not a precision retry: planning saturates without a proposal,
direct replay rejects both the changed assumption and changed payload, and a
separate lower range-reduction proof establishes that the mutated strict bound
is false. The inventory record is accepted after replacing its one-shot
boundary tactic call with this shared checked provider and retaining monotone
reuse. No LeanCert or PNT+ theorem is imported.

Although `ReductionCertificate` gives the four payload atoms names, its current
decoder accepts only the pinned constants `[231, 100, 46, 125]`; the fields are
not general checked parameters. The probe is not the general `exp` algorithm.
Its finite fact lattice, fixed point enclosure, fixed power, and exact payload
do not establish arbitrary precision, repeated-halving selection, cached
powers, interval endpoints, or a package-owned Taylor remainder. Those remain
D7/D8 acceptance work; this fixture establishes the large-negative
range-reduction and reusable-tail interfaces without overclaiming them.

The first load-bearing `LeanCert.CertifiedBounds.BKLNW` probe targets the
private PNT+ declaration `BKLNW_a2_bounds.lean:cert_pow433_upper`, whose first
step is exactly `LeanCert.CertifiedBounds.BKLNW.pow433_upper`. Rather than
wrapping that theorem, `PntBKLNWPow` copies the source definition

```lean
∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊,
  x ^ ((1 : ℝ) / k - 1 / 3)
```

and authenticates its specialization at `x = 2^433`. The kernel proof first
checks the logarithmic floor identity, isolates the exact `k = 3` and `k = 4`
terms, and bounds all 429 terms from `k = 5` through `433` uniformly. The
certificate carries the limit, split coordinates, two dyadic exponents, exact
tail cardinality, and rational output cut. Its pure-natural predicate checks
`12a ≤ M`, `15b ≤ 2M`, exact cardinality, the complete rational product
bound, and containment in the PNT+ endpoint. The companion theorem is
parameterized over every accepted choice of exponents and endpoint; the
retained certificate uses `a = 36`, `b = 57`, and the stronger cut
`100000001948 / 100000000000`.

The package sends that certificate through the generic policy session,
chronology, schema replay, and `ProofFrontend` before closing the exact PNT+
decimal target as an ordinary theorem. Structurally valid mutations of the
limit, tail cardinality, exponent, or rational endpoint are rejected by both
planning and replay. The endpoint mutation additionally has a kernel theorem
showing that the proposed smaller cut is false. The guarded axiom report has
only the permitted Mathlib foundations and, unlike the pinned LeanCert
implementation of this provider leaf, no `native_decide` dependency.

This is partial evidence for the imported BKLNW certified-bound interface, not
a completed classification of that interface or of the 128 BKLNW tactic
sites. The retained runtime operation still names the `M = 433` source leaf;
it does not dispatch the smaller limits 29, 37, 44, 51, 58, 63, 145, 217,
289, and 361, enumerate per-term interval facts, handle the exponential-bound
half of the imported interface, or establish the required comparative
replay/size measurements.
The uniform tail theorem avoids expanding 431 terms, but this fixed canary is
not yet evidence for the production balanced-fold implementation.

The coordinate-aware Table 12 implementation is a bounded acceptance fixture
that completes this family migration. At PNT+ commit
`21998bb6196b56789f72a52656a781a75e134eb0`, the exact declaration is
`BKLNW.table_12_check (b Cb1 Cb2 Cb3 Cb4 Cb5 c C M : ℝ)` with a hypothesis
that the nine-tuple belongs to `table_12`; its conclusion is the five-way
conjunction `b ^ k * C_bk_S b c C ≤ Cbk` for `k = 1, …, 5`. The tactic
occurrence at line 1313 expands over 24 ordinary rows and five columns (120
leaves). The occurrences at lines 1319 and 1325 are the final numerical
premises of `C_bk_log_row_bound` for two logarithmic rows and expand to five
leaves each. This confirms the inventory total of exactly 130, despite the
source comment's approximate `~135`.

The fixture pins the source calculation literally:

```lean
noncomputable def C_bk_S (b c C : ℝ) : ℝ :=
  (C + 1) * exp (-b / 2) + RS_prime.c₀ * exp (-2 * b / 3)
    + c * exp (-3 * b / 4) + RS_prime.c₀ * exp (-4 * b / 5)
```

Its exact nine-field row is:

```lean
(25, 1.750020e-4, 4.375050e-3, 1.093770e-1, 2.734410e0,
  6.836010e1, 0.88, 0.86, 32e12)
```

For this row, the first source term has coefficient
`C + 1 = 0.86 + 1 = 1.86`; the third has coefficient `c = 0.88`; and the
second and fourth use the pinned `RS_prime.c₀ = 1.03883`. The proof-side
definition preserves that shape, and a kernel theorem checks every tuple field
encoded in the certificate, including `M = 32e12` even though `M` does not
occur in `C_bk_S`.

The retained mutation fixture covers the five leaves of the ordinary `b = 25`
row. One row operation has five coordinate arguments; one runtime request,
reply, provider action, and authenticated payload produce five chronological
fact events. Generic `ProofFrontend` replay performs the bounded fold and
closes all five scientific-decimal inequalities. The Mathlib proof computes
four Taylor point enclosures once, reuses their natural powers for the shared
row sum, and projects that sum into the five column targets. The row
operation's output is only a token; sharing occurs in the single action/payload
and proof theorem, not in a separate row-sum DAG node. The certificate fields
are pinned constants, not general checked parameters.

The paper's false `(b = 25, k = 5)` target `6.65350e1` is replaced in the
pinned source by `6.836010e1`. The false payload is rejected before replay with
coordinate code `205`, which decodes to `(25, 5)`; it emits no draft and cannot
turn into a precision retry. Replay also rejects it, and an independent lower
enclosure proves the claimed paper bound false. No LeanCert theorem or PNT+
result is imported.

The generated extension covers the other 23 ordinary rows without copying 23
proof schemas. Its package-owned table records every exact source tuple and
flattens to 115 coordinate-bearing rational cuts. A kernel correspondence
theorem checks those stored values against the pinned scientific literals,
including each source-only `M`. One source-pinned 391-atom payload and one
explicitly bounded arity-115 action produce exactly 115 chronological fact
events. The declared envelope charges 116 nodes, 115 candidates and accepted
facts, and the coherence-required payload-use, atom, and draft/entry
capacities. This single maximum-sized acceptance chunk is not the production
chunk-size policy.

The pinned source itself gives row 31 columns 3--5 as `1.034630e-2`,
`3.217360e-1`, and `1.000500e1`, the same tail values as the following
logarithmic row. They are intentionally retained as source bounds rather than
silently tightened to values reconstructed from the defining formula.

The Mathlib companion proves the four Taylor point windows once and uses one
natural-power range-reduction theorem for every positive integer row. Exact
rational side conditions then close all five cuts for each table member. One
uniform indexed replay schema handles all 115 events, an honest rational-cut
meet proves semantic intersection universally, and a single generic
`ProofFrontend` fold must close every coordinate. Together with the retained
row-25 theorem this establishes all 120 ordinary leaves. The fold elaborates
all 115 closures, and first, middle, and last typed `Evidence` declarations
also force representative emitted proof terms through the kernel.

The final two certificates cover the ten logarithmic cells. Exact inputs
`5e10` and `32e12` are converted to checked windows
`[24.6352888, 24.6352889]` and `[31.0967570, 31.0967571]`. A finite Mercator
`log (1 - x)` series remainder at `x = 4/5` proves the needed `log 5` enclosure;
checked `log 2`
bounds and the exact identities `log (5e10) = 10 log 2 + 11 log 5` and
`log (32e12) = 17 log 2 + 12 log 5` supply the two large logarithms. Fractional
range reduction about floors 24 and 31 then checks the exponential terms. The
two row schemas consume those exact window facts as replay assumptions, so the
logarithm dependency is load-bearing.

Four provider actions install twelve chronological facts: two log windows and
ten coordinate cuts. One generic frontend fold closes every logarithmic target,
with typed first/last evidence guards. A copied 26-tuple source list and kernel
correspondence theorem check the exact interleaving of ordinary, corrected
row-25, and logarithmic certificates. The final wrapper maps arbitrary pinned
membership in the copied 26-tuple source list to its certificate and returns
the five source inequalities, establishing honest 130/130 coverage. A zero first-cell cut for
the `log (5e10)` row fails with coordinate diagnostic `401`, emits no payload,
is rejected by the replay decoder, and is separately proved false. The family
and all three Table 12 tactic records are therefore accepted after rewrite.
This remains a fixed-source acceptance table, not a general-purpose logarithm
or production batching interface.

Refreshing an upstream pin must regenerate and review the manifest. The
inventory prevents blind spots; it does not make exact-source compatibility a
release criterion. It must cover, at minimum:

- all 141 `LogTables.lean` textual occurrences, of which 136 are actual tactic
  invocations, including nested logarithms, large exponential arguments,
  square roots, pi, and tails down to `10^-100`;
- all 132 BKLNW textual occurrences across nine files, of which 128 are actual
  tactic invocations. The generated Table 10 row sources contain 87 target
  proof sites and 38 supporting `a₂`-bound proof sites. The Table 12 theorem
  expands to 130 checks: 24 ordinary rows by five columns plus two logarithmic
  rows by five columns. The row partition is structurally derived from the
  exact pinned list definition, including a first tuple placed on the opening
  bracket's line; the five-column expansion is a reviewed reading of the
  theorem's conjunction and tactic structure. Table 10 is currently recorded
  at executable call-site granularity; complete row/column expansion is part
  of its D9 shard work. Both families are recorded separately from their
  aggregate source counts; and
- all 17 remaining textual occurrences, of which 16 are actual tactic
  invocations, in `Dusart.lean`, `FKS2.lean`, `FKS2Cor23Cor14Tail.lean`,
  `FKS2Floor/Cor22Floor.lean`, and `Goldbach.lean`.

The complete 13,590-cell FKS2 stream is a generated workload in addition to
this source-occurrence inventory. Counting the 280 actual tactic invocations
while omitting that generated stream misses the main batch workload.
Conversely, importing the already-proved FKS2 result does not exercise Hex. The
network-free per-PR gate detects an inconsistent or unexplained local change to
the pinned commit, dependency revisions, occurrence inventory, or batch sizes.

The first scale probe represents exactly 128 of those 13,590 cells: source
indices `0–127` of pinned `Table4ExtData_11.lean`, covering the contiguous
intervals `b = 11010` through `b' = 11138`. The pinned shard declaration is
`cells_11 : List Cell`, followed by
`cells_11_checked : cells_11.all checkCell = true`; the package supplies the
same boolean-all shape with its own package-owned `checkCell` predicate, plus
an arbitrary-membership semantic wrapper. Every five-field rational tuple is
copied exactly, and `pnt_inventory.py --verify-source` compares all 128
normalized tuples against the pinned shard prefix. This
segment does not reach shard 11's later transition to width-five cells, and it
does not claim the remaining 872 cells of that shard or any other shard.

The provider replaces LeanCert's 64-way dyadic expression check with a
package-owned 128-way split. One Mathlib `Real.exp_bound'` theorem proves the
degree-11 Taylor polynomial plus explicit degree-12 remainder on `[0,1]`;
exact rational obligations then authenticate positivity, both square-root
endpoint enclosures, the reduced argument, and the final inequality for every
cell. The power `128` is checked by seven explicit squarings rather than 128
linear rational normalizations.

Runtime work is divided into eight independently scheduled actions of sixteen
coordinates over one shared 128-argument operation. The retained resource
envelope charges eight requests and replies, 128 candidates and chronological
facts, eight payload entries, at most sixteen candidates per outcome, 1,024
payload cells, atoms at most `10^36`, and 2,048 bounded policy traversals.
The proof-side chunk theorems each declare at most 2,000,000 heartbeats and
recursion depth 100,000; rebuilding the Mathlib companion took 8.9 seconds on
the development host. This is an observed
acceptance-fixture cost, not a stable CI budget or a linear full-family
extrapolation. Eight chunk schemas share one indexed definition, each covering
sixteen addresses; conformance directly replays one representative address in
the first, middle, and last chunks and checks that the retained program trace
has 128 events. It does not yet
retain a generic `ProofFrontend` fold over this large payload, so that closure
and the full-shard/full-family profiles remain acceptance work.

Doubling the first cell's `eps` field constructs a false source cell at
coordinate `11010`. The numeric checker returns that exact coordinate before
payload allocation, the plan contains no draft, its replay body is rejected,
and a lower Taylor enclosure proves the mutated endpoint inequality false.
There is no effort or precision retry. Consequently the generated-family inventory remains
`pending` with explicit evidence for partial `128/13590` coverage; neither the
family nor the `LeanCert.ANT` dependency is reclassified by this probe.

Because the upstream commit is immutable, checking for a deliberately updated
upstream pin is a maintainer operation: `--verify-source` regenerates from the
exact checkout and requires an explicit SPEC, constants, and fixture refresh.

The committed inventory lives at
`conformance-fixtures/HexIntervalMathlib/pnt-inventory.jsonl` and is generated
by `scripts/maintenance/pnt_inventory.py`. The generator uses an
offset-preserving lexical mask over pinned Lean sources, counts tactic
identifiers outside nested comments and string literals, records the nearest
preceding declaration header, separately records raw textual matches, audits
the six directly imported LeanCert interface families, and expands the named
generated-data families. The committed metadata pins all 232 tracked Lean
source files in the PNT+ repository, records that count in the fixture, and
stores a digest of the fixed audit-record identity. That second digest covers
source locations together with reviewed interface roles and generated-workload
annotations; it is not presented as a pure parser result. Migration
classifications are deliberately excluded so
they can be filled in without weakening audit identity. After editing
classifications, `--update-classifications` validates their schema and refreshes
only the full record digest. `--refresh` carries existing decisions forward by
exact audit identity and refuses to discard a classified record;
`--verify-source` compares audit identity while allowing those decisions to
differ from freshly generated `pending` defaults.

Per-PR CI runs the generator's unit tests and validates the committed manifest
without network access. For a pin bump, `--inspect-source --source
<exact-checkout>` reports the observed pins, digest, counts, imported modules,
and generated families without accepting or writing them. A maintainer reviews
that report, updates the constants and workload partitions, then uses
`--refresh` to reseal the fixture. Independent source verification uses
`--verify-source`; the accepting commands refuse an unreviewed difference in
HEAD, dependency pins, toolchain, Lean-source digest, counts, import surface,
or batch sizes. The artifacts exist before D8 as an audited backlog and local
integrity gate; they become a migration claim only when the classifications
and ported proof fixtures are complete.

`interval_decide` is not the complete PNT+ dependency surface. The same pinned
tree has 60 actual `interval_auto` calls in `TMEEMT.lean` and
`RosserSchoenfeld/RSPrimeLower.lean`. It also has sixteen direct LeanCert import
statements covering these six public modules:

- `LeanCert.Tactic.IntervalAuto`;
- `LeanCert.CertifiedBounds.Li2`;
- `LeanCert.CertifiedBounds.Chebyshev`;
- `LeanCert.CertifiedBounds.BKLNW`;
- `LeanCert.ANT`; and
- `LeanCert.Validity.AffineCover`.

The certified-bound imports are load-bearing theorem dependencies, not merely
convenient tactic imports. PNT+ uses the Li(2) integrand, positivity, boundedness,
value, and upper/lower integral results; Chebyshev and BKLNW certified bounds;
the ANT expression evaluator and whole-interval checker behind the extended
FKS2 table; and an affine-cover certificate for its small-`x` floor. Some of
these current PNT+ glue proofs evaluate LeanCert checkers with `native_decide`.
They therefore belong to the audit even though they do not spell
`interval_decide`. `LeanCert.Tactic.IntervalAuto` re-exports both
`interval_decide` and `interval_auto`, so the six-module import list covers the
tactic entry points as well as the certified-bound interfaces.

The compatibility manifest records every `interval_auto` invocation, every
direct LeanCert import, and every qualified `LeanCert.<component>` reference
outside comments and string literals,
the load-bearing role of each of the six imported public interface families,
and every executable textual `native_decide` occurrence as a starting list of
compiler-trusting proof sites. This lexical list is not the authoritative
trust audit: macro expansion and transitive dependencies are checked from the
ported theorems' axiom sets under the Axiom contract below. A lexical scan
cannot soundly name-resolve an
unqualified theorem used after `open`; the corresponding import/interface
record is the durable backlog item, and migration review must classify that
interface before it can leave `pending`. Qualified-reference occurrences are
inventory-only evidence beneath that decision. Each record names its reviewed
interface provenance; `LeanCert.Core` is reached through `LeanCert.ANT` or
`LeanCert.Validity.AffineCover`, while the parent `LeanCert.Validity` namespace
is attributed to the latter. The checker rejects a namespace absent from this
reviewed provenance table. This prevents the fixture from claiming semantic
name resolution it has not performed while still making every source-level
dependency site and imported role explicit. The 107 qualified-reference
occurrences include namespace opens; they are not 107 distinct declaration
dependencies. A migration may
classify a finite natural-number `interval_auto` call as ordinary arithmetic
automation rather than route it through the real interval engine. A direct
certified-bound dependency may remain outside the interval migration or be
replaced by a differently stated shared theorem. When a migrated PNT+ theorem
mentions a LeanCert-specific definition, the port must either restate the
theorem in PNT+ vocabulary or prove the required equivalence or implication;
Hex need not mimic the old API.

The PNT+ migration criterion is therefore a source-pinned port, not a build of
the upstream source with tactic names mechanically substituted. The port may
change imports, consolidate repeated calls into shared lemmas, reorganize
generated tables, and adjust proof statements through explicit equivalences.
Its selected numerical corpus must include the logarithm and exponential tail
families, the large BKLNW sums and recorded false targets, Table 10, Table 12,
and the complete 13,590-cell FKS2 stream. The selected BKLNW and FKS2 results
must also replace the load-bearing roles of the old BKLNW certified bounds and
ANT whole-interval checker, either by porting those results or by proving the
same required statements through a different Hex route. This is an obligation
on the resulting proof, not a requirement to clone either API. Additional
Li(2), integration, Chebyshev, or affine-cover cases are added when they support
a claimed Hex workload; surveying them does not commit `HexInterval` to
feature-for-feature LeanCert parity.

The migration claim is earned when that port reproduces or strengthens the
selected mathematical statements with ordinary kernel-checked proofs and the
performance comparison below. The transitive axiom set of every claimed ported
theorem satisfies the full Axiom contract above: it excludes `sorryAx`, every
project-local axiom, `Lean.ofReduceBool`, `Lean.trustCompiler`, and generated
`*.native_decide.ax_*` declarations. A retained dependency that reintroduces
one of them is recorded as explicit trust residue and prevents that theorem
from satisfying the kernel-only migration claim; it cannot be hidden behind a
textually clean wrapper. PNT+ is allowed to adapt to Hex; Hex is
not advertised as a drop-in LeanCert replacement. Newer LeanCert algebraic,
integration, optimization, root-finding, and routing APIs remain outside the
claim unless a later workload explicitly selects them.

- [LogTables.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/21998bb6196b56789f72a52656a781a75e134eb0/PrimeNumberTheoremAnd/IEANTN/LogTables.lean)
  contains hundreds of `exp` and `log` point bounds, nested logs, large
  arguments, and errors down to about `10^-100`.
- [BKLNW_a2_bounds.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/21998bb6196b56789f72a52656a781a75e134eb0/PrimeNumberTheoremAnd/IEANTN/BKLNW/BKLNW_a2_bounds.lean)
  contains finite sums whose certified upper limits reach 433.
- BKLNW Table 10 contains sums of exponentials with small margins. PNT+ PR
  [#1510](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1510)
  records a false target exposed numerically. Failure diagnostics must report
  the incompatible enclosure rather than only request more precision.
- PNT+ PR [#1405](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1405)
  records manual treatment of `exp (-log N / k)` and describes the Table 12
  batch as roughly 135 checks. At the pinned source, this audit counts 24
  ordinary rows and two logarithmic rows, each expanded across five columns,
  for exactly 130 checks. The PR also
  records four false original boundary
  rows, at `b = log(5e10)`, `25`, `log(3.2e13)`, and `32`; at least one
  original row remains an expected-failure regression. These cases motivate
  certified normalization, batch replay, and useful failure bounds.
- [Table4ExtCore.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/21998bb6196b56789f72a52656a781a75e134eb0/PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4ExtCore.lean)
  defines the generic cell checker and its transport theorem. The 13,590 cells
  live in
  [fourteen `Table4ExtData_*` shards](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/21998bb6196b56789f72a52656a781a75e134eb0/PrimeNumberTheoremAnd/IEANTN/FKS2Tables),
  thirteen of size 1,000 and one of size 590, and
  [Table4Ext.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/21998bb6196b56789f72a52656a781a75e134eb0/PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4Ext.lean)
  assembles them. Their manual exponential range-reduction rewrite motivates
  shared certificates, local effort, arbitrary partitions, and bounded object
  size. PNT+ PR
  [#1563](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1563)
  records the rewrite and batching rationale.
- LeanCert's
  [Li2Verified.lean](https://github.com/alerad/leancert/blob/31579b55618d11e4fbe622a6b5e30b0359b2ee6d/LeanCert/Examples/Li2Verified.lean)
  uses a cancellation-preserving integrand rewrite, seven main pieces, exactly
  2,300 middle cells, four 100-cell numerical side intervals, and analytic
  endpoint pieces. It is a later challenge for removable behavior, open
  endpoints, adaptive partitions, and verified integration. Integration
  itself is not part of the first interval tactic release.

### RealPaver

RealPaver is the closest operational model for the constraint-solving half of
this design. The inspected historical description is
[Algorithm 852](https://hal.science/hal-00480813); the current
implementation is
[`realpaver/realpaver` at `f9d4223`](https://github.com/realpaver/realpaver/tree/f9d422354c67daf9fcc292ff599acbe8d66cceec),
described by the
[RealPaver 1.1 JOSS paper](https://doi.org/10.21105/joss.09331). It does not
provide Lean certificates, but its decomposition supplies concrete scheduler
and contractor hypotheses to test.

- RealPaver builds a shared DAG of constraint expressions, records parent and
  child links, variable dependencies, and occurrence counts, and attaches one
  contractor per constraint. This supports the shared SSA program and suggests
  that repeated-occurrence count is useful policy input.
- Its HC4 path evaluates a constraint forward and applies inverse operations
  backward. A dependency queue reactivates only contractors mentioning a
  variable whose domain improved past a configurable relative threshold. The
  first Lean contractor milestone implements this recognizable baseline before
  more elaborate learning policies.
- Box-consistency contractors perform a one-variable search when repeated
  occurrences make direct inversion weak. RealPaver's 3B contractor scans
  boundary slices until it finds a survivor on each side; CID contracts every
  slice and hulls all nonempty contracted boxes in its scope. Both temporarily
  run another contractor on slices. They map to local `shave` actions with
  branch certificates, not automatically to global proof-state splits.
- ACID orders variable contractors by derivative-based smear and alternates
  learning and exploitation phases, adapting how many expensive contractors it
  applies from observed contraction gain. This is a particularly relevant
  comparison for `balancedV1`: learning from gain is promising, but RealPaver's
  constants and phase lengths are benchmark inputs, not Lean defaults.
- RealPaver combines HC4 or BC4 propagation with interval Newton, interval
  Gauss-Seidel, affine or Taylor linear relaxations, and polytope-hull
  contraction. These become separately registered actions so the policy can
  compare cost, contraction, and generated proof size.
- It separates node exploration order from split-variable selection and offers
  depth-first, breadth-first, distant-most, largest-domain, round-robin, and
  derivative-smear choices. Even its ordinary split point is configurable and
  need not be the midpoint. Lean therefore benchmarks these choices instead of
  baking one tree discipline into soundness.
- Its result lattice distinguishes proved empty, proved feasible/existence,
  wholly inner, and unresolved boxes. The first interval tactic needs only
  universal closure, contradiction, and `unknown`, but later root isolation and
  verified graphing should preserve room for existence and inner-box
  certificates.
- Current RealPaver supports real variables with interval unions plus integer,
  Boolean, conditional, table, and piecewise constraints. Those domains do not
  enter the first release, but the operation-key and scoped-constraint design
  must not assume every future fact is one closed real interval.

One historical profile is especially instructive: inverse propagation applied
`log` while solving constraints whose input syntax used `exp`, so the inverse
operator did not occur in the original expression. This is a direct precedent
for bounded expression instantiation. The Lean design compares keeping such an
inverse expression inside a rule payload against adding a reusable validated
node to the network.

What does not translate is equally important. RealPaver relies on GAOL and
directed hardware floating-point rounding, represents closed numerical boxes,
and reports numerical solver status rather than proof objects. Lean uses exact
certificate endpoints and ordinary kernel replay, retains open and unbounded
cuts, and charges local branching and contractor work by proof size as well as
runtime.

The source-pinned comparison corpus starts with:

- [`DescartesFolium.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/DescartesFolium.rp),
  a small polynomial-plus-exponential dependency case;
- [`Caprasse.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/Caprasse.rp),
  a four-variable polynomial system;
- [`Transistor.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/Transistor.rp),
  a repeated-occurrence exponential system for HC4 versus shaving;
- the sparse
  [`BroydenBanded-10.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/BroydenBanded-10.rp)
  and larger generated variants for worklist scaling;
- [`Bratu-10.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/Bratu-10.rp),
  [`Troesch-10.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/Troesch-10.rp),
  and their larger discretizations as bridges toward certified differential
  equations;
- [`Trigexp1-10.rp`](https://github.com/realpaver/realpaver/blob/f9d422354c67daf9fcc292ff599acbe8d66cceec/benchmarks/csp/Trigexp1-10.rp)
  for sparse mixed trigonometric/exponential propagation.

Early translated fixtures prove contraction and contradiction for small boxes.
Whole-system root enumeration and existence certificates are later milestones;
the benchmark statements are not misleadingly marked as first-release tactic
successes.

### Lessons from other systems

| System or method | Adopted lesson | Deliberate limit |
| --- | --- | --- |
| IEEE 1788 | Separate mathematical sets, finite endpoint data, and encoding. Include empty and unbounded cases. | Its set flavor does not represent open endpoints, so it does not determine the Lean type. |
| CoqInterval | Shared straight-line programs, reflection, automatic differentiation, Taylor bounds, and subdivision are all practical in a proof assistant. | The initial implementation uses a hybrid replay rather than copying one monolithic evaluator. |
| Gappa and Sollya | Untrusted search can propose rewrites, polynomial bounds, and subdivisions for a small proof checker. Best-bound diagnostics are valuable. | They are optional proposal sources only. Lean replay remains independent. |
| MPFR and MPFI | Arbitrary precision, directed rounding, and argument reduction guide endpoint algorithms. | Hardware rounding state and foreign results are not trusted. |
| Arb | Midpoint-radius balls and cached high-precision point evaluation are efficient for narrow inputs. | Balls are an internal candidate representation. Public semantics remain endpoint intervals because balls do not express open or half-infinite sets. |
| IBEX HC4 | Dependency worklists, forward-backward contractors, contraction thresholds, smear scores, and split policies transfer directly. | Constraint solving heuristics never justify a Lean fact by themselves. |
| RealPaver | HC4/BC4, 3B/CID shaving, gain-adaptive ACID, interval Newton, and independent choices of node order, split variable, and split point form a concrete contractor-policy ladder. | Hardware-directed rounding, closed numerical boxes, and numerical status codes are replaced by exact replayable certificates and open/unbounded cuts. |
| HOL Light nonlinear verification | Monotonicity, convexity, boundary reuse, and certificate DAGs can scale to hard inequalities. | Full Flyspeck-style second-order verification is a later milestone. |
| Affine arithmetic | Noise symbols retain first-order correlations and are formally verifiable. | Open and unbounded sets stay in the endpoint layer. Affine forms are a later method. |
| Taylor models | Polynomial plus rigorous remainder is the strongest planned dependency-control method. | Full multivariate Taylor models do not block the first release. |
| dReal-style interval constraint propagation | Counterexample boxes, contractor scheduling, and influence-based branching are useful search ideas. | The tactic proves exact Lean propositions. It does not use delta weakening. |

## Regression and challenge corpus

Each case records the required feature, expected success or safe failure,
selected policy, search statistics, replay time, certificate size, and axiom
set. Exact imported statements are pinned to upstream commits when licensing
permits copying them into test modules.

Every executable fixture also records its earliest development milestone
`D1`–`D10`, the exact rule set and budget configuration, and one of
`success`, `unknown`, or `rejectedCertificate`. An expected `unknown` belongs
to that pinned configuration, not to the mathematical statement forever; a
later milestone may promote the same statement to `success` without deleting
the diagnostic fixture. This prevents an aspirational challenge from silently
becoming a per-PR release gate, and prevents a current limitation from being
mistaken for an architectural prohibition.

### Endpoint semantics

The endpoint-shape and exact-operation cases below default to `D1`; logarithm
domain behavior is the `D7` override.

- `[D1]` all four closure combinations at finite ends;
- `[D1]` both one-sided unbounded shapes and the whole interval;
- `[D1]` singleton normalization and the three empty equal-endpoint shapes;
- strict conclusion from one open summand, such as
  `x ∈ (0,1), y ∈ [0,1] ⟹ x + y < 2`;
- reciprocal on positive open and half-open intervals, including the outward
  dyadic enclosure of `{3}⁻¹ = {1/3}` at two precisions;
- inverse and division across zero, including Lean's value at zero;
- logarithm at, below, and just above zero;
- a split whose cut equals a parent endpoint.

The `D1` table is exhaustive about emptiness: every unary operation preserves
empty; arithmetic binary image and intersection operations absorb empty; hull
uses empty as an identity; an empty split returns two empty pieces; and
`pow empty n = empty`, including `n = 0`, while `pow I 0 = {1}` for every
nonempty `I`. It separately checks `{0} * whole = {0}` so an
implementation cannot confuse an empty operand with a zero singleton, and
checks `whole * {0} = {0}` independently to catch operand-order mistakes in
sign partitioning.

### Arithmetic and dependency

Unless a later override is stated, the shared arithmetic cases in this block
are `D3` fixtures.

```lean
x - x = 0
x ∈ [0,1]             ⟹ x * (1 - x) ≤ 1/4
x ∈ [0,1]             ⟹ x * (2 - 3*x) ≤ 1/3
x ∈ [-1,1]            ⟹ x^2 ≤ 1
x ∈ (0,+∞)            ⟹ 0 < x / (x + 1)
x ∈ [0,1], y ∈ [0,1]  ⟹ (x+y)*x + (x+y) ≥ 0
```

These cases distinguish proved same-node cancellation, centered forms,
contractors, and subdivision from naive repeated interval evaluation. Sharing
alone does not prove `x - x = 0`; the exact cancellation alternate does.
The first sharp quadratic is a `D6` success without a global split, through
the exact centered identity `x*(1-x) = 1/4 - (x-1/2)^2`; merely observing that
its extremum is dyadic is not the certificate. The second is retained as
`unknown` under a pinned `D9` diagnostic using `bisectV1`, exactly the natural
and derivative-sign rule filters, `maxSplits := 16`, `maxDepth := 16`,
`maxSteps := 1000`, and `maxEffort := 32`, with no symbolic square completion
or polynomial certificate. Its sharp maximizer is `1/3`, so every finite
dyadic partition leaves one cell containing it. It becomes an expected `D10`
success through exact square completion/SOS or a certified symbolic rational
critical-point partition. Bernstein remains a comparison method; by itself on
finite dyadic cells it is not promised to attain the sharp nondyadic maximum.

Additional coordination and handoff cases are:

- `[D4]` `x^2 + y^2 = 1 ⟹ x^4 + y^4 ≤ 1`, using a certified contextual
  alternate such as `x^4 + y^4 = 1 - 2*x^2*y^2`; this is not advertised as a
  natural-interval consequence;
- `[D4]` a sparse-registry instantiation regression modeled on the public
  `grind` case: the input program contains `a*(b-c)` with facts `0 ≤ a` and
  `b ≤ c`, while a registered trigger proposes `a*b`, `a*c`, and a proved
  distributive equality edge. With instantiation disabled the pinned registry
  returns `unknown`; with it enabled the generated nodes are deduplicated and
  replay closes the same goal;
- `[D7]` `y * 2 - y * Real.sqrt 2 ^ 2 ≤ 0`, using
  `Real.sq_sqrt zero_le_two` before the linear arithmetic handoff;
- `[D3]` the four-corner multiplication theorem: from `a ≤ u ≤ b`,
  `c ≤ v ≤ d`,
  and a lower bound below all four products `a*c`, `a*d`, `b*c`, `b*d`, prove
  that it is below `u*v`;
- `[D10 unknown]` `0 ≤ 1 - 3*x^2*y^2 + x^2*y^4 + x^4*y^2` as a handoff
  case. This is the
  Motzkin polynomial, which is nonnegative but not a sum of polynomial
  squares; an ordinary SOS certificate is therefore not an honest expected
  solver. Plain intervals over unbounded variables must decline it. A later
  multiplier/Positivstellensatz-style or dedicated polynomial certificate may
  solve the residual;
- `[D9]` a deterministic synthetic generator parameterized by variable count,
  irrelevant linear constraints, and constraints of the form `ν ≤ max a b`.
  Its known solution uses a small active subset while the number of apparent
  max branches grows rapidly. It tests split planning without reproducing an
  unpublished application statement or its identifying dimensions.

### Elementary functions

These are `D7` fixtures unless marked otherwise.

- `[D5]` the sine experiment's point bounds
  `-25/48 ≤ sin (-1/2)` and `sin (1/3) ≤ 637/1944`;
- `[D5]` `|sin x| ≤ 1` on an unbounded input;
- a narrow sine interval crossing a critical point;
- a large-argument sine that uses periodic reduction;
- `[D7]` `Real.sin 10 < 0` through certified periodic reduction;
- `[D7]` exact dyadic `0 < lo ≤ Real.cos (10 ^ 10) ≤ hi` with
  `hi - lo ≤ 2 ^ (-80)`, including rejection of an off-by-one reduction;
- exact `sin π = 0` through a symbolic rewrite;
- `exp x ≥ 1 + x` on `[0,+∞)` through derivative monotonicity;
- `[D7]` an enclosure of `Real.exp (1 / 8)` of width at most
  `2 ^ (-100)` from a package-owned series and remainder theorem;
- `[D7]` a 1,000-bit Machin-style pi enclosure, plus provider fallback and
  agreement checks against a second independently proved Machin-style identity;
- `[D7]` a registered series with coefficients supplied entirely by its
  function package rather than the interval library;
- `[D8]` the ordered 257-entry table of
  `Real.log (1 + (i : ℝ) / 256)` for `i ≤ 256`, each entry of width at most
  `2 ^ (-128)`, with shared coefficients and remainder proofs;
- `x < 1 + x^3` on `[-1,+∞)`, matching the
  [pinned CoqInterval example](https://gitlab.inria.fr/coqinterval/interval/-/blob/dcdffc06d31e8e3646829b948c137ff140756b80/README.md#L334);
- `sin x ≤ 0` on `[3.2,6.2]`;
- high-precision bounds for `sin 100`, `π`, `log 2`, and `sqrt 2`;
- `exp (0.117^2) ≤ 1.013879`, `π ≤ 3.15`, and `4 * log 11 < 11`. The last
  appears in PNT+ issue
  [#1129](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/issues/1129);
- compatibility with the `lean-interval-bounds` examples
  `2718/1000 < exp 1 < 2719/1000`, `log 2 < 694/1000`,
  `-694/1000 < log (1/2)`, `968/1000 < cos (1/4)`,
  `exp (3/2) < 5`, and `exp (4 / exp 1) ≤ 7`.

The first huge-argument cosine acceptance probe delivers the weaker but
load-bearing ordinary theorem `0 < Real.cos (10^10)`. A Mathlib-free package
retains the exact quotient `3183098861` and residual endpoints `13/5`, `27/10`;
the Mathlib companion checks those values against a provider-agnostic pi
enclosure claim, proves the local sign, and replays periodicity through the
generic proof frontend. Wrong-quotient and wrong-residual payloads pass
structural decoding and fail semantic replay. The current claim provider uses
Mathlib's 20-decimal pi bounds, and all numeric choices are fixed fixture data.
Consequently this probe does not yet satisfy the listed 80-bit enclosure,
computed reduction, 1,000-bit package-owned constant, provider-selection, or
precision-refinement requirements.

The bounded precision-indexed logarithm experiment supplies both 20- and
50-decimal requests for `Real.log 2`. The requests select different term
counts, 22 and 53, and replay authenticates the precision, term count, exact
source input, and rational output window. The Mathlib companion derives the
window from its recorded term count using the two-sided odd-power partial-sum
bounds at `1/3` and a checked geometric tail bound; the 50-decimal request
closes an ordinary strict enclosure of width `10^(-50)` through the generic
proof frontend. Insufficient-term,
wrong-endpoint, wrong-precision, and wrong-source mutations reject. This does
not yet provide arbitrary log arguments, adaptive runtime endpoint generation,
the ordered 257-entry table, persistence, caching, or performance evidence.

### PNT+ compatibility

The committed compatibility subset is `D8` unless marked `D9`:

- two-sided `log 2` and `log 3` bounds;
- the one-sided nested bound `0.633415 < log (log 6.58)` and the two-sided
  bound `-0.366513 ≤ log (log 2) ≤ -0.366512`;
- `exp (-1)`, `exp (-1/2)`, and `exp (-2/3)`;
- `log 11723 ≤ 9.37`, `exp 20 ≤ 485165196`, and
  `10^9 ≤ exp 22`;
- representative `10^-20` and `10^-100` tail bounds;
- BKLNW sums with upper limits 29, 37, 63, 145, 289, and 433;
- `[D9]` one Table 10 shard and the recorded false target as an expected
  failure. The shard fixture must bind the intended paper row/column
  coordinates and generated theorem family, not merely replay 87 target and 38
  supporting source-level tactic sites;
- `[D9]` the 130-case Table 12 batch, plus one of its four false
  original boundary rows as an expected failure;
- `[D9]` a small deterministic FKS2 sample in per-PR `core`, a measured medium
  shard in per-PR `ci`, and all 13,590 cells in the `local`/release profile;
- mutated Taylor, range-reduction, fold, and split certificates, all rejected.

The [PNT+ log-table generator](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/21998bb6196b56789f72a52656a781a75e134eb0/scripts/gen_log_tables.py)
is a model for optional untrusted candidate generation. The committed tests
still exercise the compiled Lean planner and kernel replay path.

### Quadrature and algebraic-provider clients

These are later Mathlib-facing or cross-library fixtures rather than first
release requirements:

- `[D10]` the strict rational bounds
  `7468 / 10000 < ∫ x in 0..1, Real.exp (-(x ^ 2))` and
  `∫ x in 0..1, Real.exp (-(x ^ 2)) < 7469 / 10000`, obtained from a checked
  adaptive quadrature or Taylor partition rather than samples;
- `[D10 cross-library: hex-interval-algebraic]` isolate the unique real root of
  `x ^ 5 - x - 1` with `hex-real-roots`, then consume its certified interval
  in an interval goal;
- `[D10 cross-library: hex-interval-algebraic]` return disjoint certified complex regions for all
  roots of `z ^ 5 - z + 1` with `hex-roots`; and
- `[D10 cross-library: hex-interval-algebraic]` a mixed case in which exact algebraic candidate
  intervals are refined or eliminated by independently registered sine or
  logarithm packages.

The `IntegralCanary` experiment realizes the first fixed D10 quadrature leaf
without treating the integral as a known constant.  Its Mathlib-free package
emits an exact fixed one-cell record for `[0, 1]` containing the cell endpoints,
eight Taylor terms, the integrated polynomial value
`1009219 / 1351350`, the integrated remainder `1 / 609280`, and the requested
four-decimal endpoints.  Kernel replay applies `Real.exp_bound` pointwise to
`exp (-x^2)`, integrates the resulting `x^16` remainder, integrates each
polynomial monomial exactly, and then closes the strict window through the
generic chronology and `ProofFrontend`.  The replay theorem proves those fixed
values rather than interpreting arbitrary numeric record fields.  Conformance
therefore rejects any different record, including an omitted cell, an unproved
tighter error denominator, and a changed right endpoint.

This is deliberately a bounded one-cell canary, not the general integration
provider.  It does not yet choose partitions or Taylor orders, accept an
arbitrary integrand or interval, combine multiple cell certificates, perform
adaptive refinement, persist quadrature tables, or establish useful
performance.  Those capabilities, along with composite Simpson or higher
order local models, remain D10 work; the canary establishes the certificate,
analytic-error, and ordinary-theorem replay boundary they must reuse. A general
provider must make decoded cell/order/approximation/remainder fields inputs to
its proof rather than extend this fixed-record decoder.

The bounded dispatcher canary already exercises the intended proof boundary
on smaller polynomials. It reconstructs one `ZPoly` from a distinguished
variable and registered integer-constant, addition, subtraction, and
multiplication operation keys. The real route runs `hex-real-roots` Sturm
isolation plus refinement for `x ^ 3 - 2` and proves that every real root lies
in `(5/4, 21/16]`. The complex route runs the `hex-roots` NK/Pellet isolator
for `z ^ 3 - z - 1` and proves that its three certified squares cover every
complex root. In both routes the planner's finite payload is only a candidate:
exact graph, coefficient, precision, and region replay must reach the
specialized engine's Mathlib correspondence theorem before `Evidence` is
constructed. Mutated variables, operand order, coefficients, and regions are
rejected.

This is not yet a general algebraic interval package. Recognition does not
cover rational coefficients, division, powers as primitive operations,
multivariate graphs, shared-polynomial normalization, multiplicities, or
arbitrary result fact schemas. The payload formats recognize only the two
canaries, and no performance-based routing or cache policy yet compares the
specialized engines with general interval propagation. The degree-five and
mixed-function fixtures above remain the acceptance targets for that general
layer.

### Zulip and downstream challenge sets

The [IMO 2020 Q2 interval thread](https://leanprover.zulipchat.com/#narrow/channel/208328-IMO-grand-challenge/topic/IMO.202020/near/211282511)
is the main adaptive-subdivision corpus. Early experiments bisected a cube into
eight children, then found that the boundary behavior of `x^x` prevents a
pure compactness argument from guaranteeing success. Later runs combined an
analytic boundary lemma with hundreds of boxes. The attached
[generated Lean proof](https://leanprover.zulipchat.com/user_uploads/3121/3HBLKR994JFwvm3gxr6XWEAn/imo2020_q2_intervals.lean)
contains the exact lemma
`x ∈ [1/4,11/32] ⟹ x^x ≤ 1569/2048`. Extracted tests cover:

- a small box solved after a registered unary `x ↦ x^x` enclosure supplies
  the leaf bound;
- a box where recognizing unary `x ↦ x^x` is tighter than a generic `x^y`;
- a boundary box that must request an analytic lemma instead of subdividing
  indefinitely;
- the complete generated partition as a proof-size comparison.

Bhavik Mehta's
[exponential Ramsey logarithm file](https://github.com/b-mehta/exponential-ramsey/blob/2cdad383b3235eff3a8e039566b8a600c1b8949b/src/necessary_log_estimates.lean#L465)
contains more than a thousand lines of manual interval propagation. It includes
high-precision bounds for `1 / log 2`, `log 3`, `log 5`, logarithms of rational
ratios, entropy expressions, derivatives, and local maxima. Its long chains of
weakened rational bounds form a regularization and certificate-planning
benchmark.

Pinned Ramsey fixtures include
`logb 2 (30991/17356) ∈ [0.8364148,0.8364149]`,
`g' 0.4339 ∈ [1.99928,1.99929]`, and
`g'_deriv 0.4339 ∈ [0,10^-6]`. Together they test nested logarithms,
outward regularization, and certification of a local maximum.

The following specialized computations are stretch tests, not baseline
requirements for a general rule:

- a Chudnovsky pi enclosure after the Ramanujan-type identity connecting its
  series to `Real.pi` has been formalized;
- exact-`π` rational approximations following the
  [`exact-pi` interface](https://hackage.haskell.org/package/exact-pi-0.5.0.2/docs/Data-ExactPi.html#v:rationalApproximations);
- `log 2` at 30,000 and one million decimal digits, using binary splitting and
  an atanh series;
- the
  [million-digit kernel-style logarithm certificate](https://github.com/CBirkbeck/LeanBridge/blob/b136733232e200c75fcc0c3e7ba50e35f4f8d204/LeanBridge/Compute/LogSmallBig.lean#L937),
  which uses kernel `decide` rather than `native_decide`;
- the spigot, BBP-style, and AGM certificate patterns in
  [*Distant decimals of π*](https://arxiv.org/abs/1709.01743), including its
  one-million-decimal and billionth-hexadecimal-digit targets, as a specialized
  non-`native_decide` certificate benchmark rather than a tactic release gate;
- cubic convergence to `π` by iterating `x ↦ x + sin x`, with locally
  increasing Taylor effort.

The [certifying LMFDB polynomial corpus at `1db6458`](https://github.com/xgenereux/certifying-lmfdb-data/tree/1db645848ee80c91632952485f290c9a62508a32/CertifyingLmfdbData/Polynomial)
provides downstream integration tests for interval outputs used inside
Newton-Kantorovich certificates. Small cases isolate a root of
`X^6 + 7*X^5 + X^4 - 1` near `0.641564061943673` to radius `10^-10`, and a root
of `X^6 - 1` near `1` to radius `10^-30`. The larger case encloses all six
roots of `X^6 - 5*X^4 - 50*X^2 + 125` to sup-norm radius `10^-57`. The interval
tactic should discharge the rational norm inequalities in those certificates.
Root existence and uniqueness remain the responsibility of the root library.

### CoqInterval and Isabelle comparison suites

CoqInterval's MT1 through MT25 comparison changed open or unbounded domains
into finite closed intervals, normally using `ε = 2^-10`, and sometimes added
`ε` to create a visible numerical gap. The test data therefore retains two
suites:

- `mtModified`, matching the finite closed benchmark in the
  [CoqInterval paper](https://guillaume.melquiond.fr/doc/15-jar.pdf#page=25);
- `mtOriginal`, restoring the original MetiTarski domains and strictness from
  the [pinned problem collection](https://bitbucket.org/lcpaulson/metitarski-git/src/0e4da8d3dac39d8fb54554ed5c6a99683e447631/tptp/Problems/).

Representative original statements are:

```text
-1 < x       ⟹ 2*|x|/(2+x) ≤ |log (1+x)|
|x| < 1      ⟹ |log (1+x)| ≤ -log (1-|x|)
0 ≤ x        ⟹ exp (x-x^2) ≤ 1+x
x < 1        ⟹ exp (-x/(1-x)) ≤ 1-x
0 < x        ⟹ 1 < (x+1/x) * atan x
0 < x ≤ π    ⟹ cos x ≤ sin x / x
0 ≤ x        ⟹ 12 - 14.2*exp (-0.318*x)
                   + (3.25*cos (1.16*x) - 0.155*sin (1.16*x))*exp (-1.34*x) > 0
```

These explicitly exercise open cuts, unbounded ends, equality margins,
division near a boundary, and mixed transcendental expressions. The complete
25-statement table is fixed below so the later fixture module does not have to
reconstruct it from benchmark names. Here `ε = 1/1024`.

1. MT1, `-1 < x`: `2*|x|/(2+x) ≤ |log (1+x)|`. The modified domain is
   `[-1+ε,10]` and its right side is increased by `ε`.
2. MT2, `|x| < 1`: `|log (1+x)| ≤ -log (1-|x|)`. The modified domain is
   `[-1+ε,1-ε]` and its right side is increased by `ε`.
3. MT3, `|x| < 1`: `|x|/(1+|x|) ≤ |log (1+x)|`. The modified domain is
   `[-1+ε,1]` and its right side is increased by `ε`.
4. MT4, `|x| < 1`:
   `|log (1+x)| ≤ |x|*(1+|x|)/|1+x|`. The modified domain is
   `[-1+ε,1]` and its right side is increased by `ε`.
5. MT5, `|x| < 1` and `x ≠ 0`: `|x|/4 < |exp x - 1|`. The modified domain is
   `[-1,-ε] ∪ [ε,1]`.
6. MT6, `|x| < 1` and `x ≠ 0`: `|exp x - 1| < 7*|x|/4`. The modified domain
   is `[-1,-ε] ∪ [ε,1]`.
7. MT7, all real `x`: `|exp x - 1| ≤ exp |x| - 1`. The modified domain is
   `[-10,-ε]`.
8. MT8, all real `x`:
   `|exp x - (1+x)| ≤ |exp |x| - (1+|x|)|`. The modified domain is
   `[-10,-ε]`.
9. MT9, all real `x`:
   `|exp x - (1+x/2)^2| ≤ |exp |x| - (1+|x|/2)^2|`. The modified domain is
   `[-10,-ε]`.
10. MT10, `0 ≤ x`: `2*x/(2+x) ≤ log (1+x)`. The modified domain is `[0,10]`
    and its right side is increased by `ε`.
11. MT11, `-1 < x ≤ 0`: `x/sqrt (1+x) ≤ log (1+x)`. The modified domain is
    `[-1/3,0]` and its right side is increased by `ε`.
12. MT12, `0 < x`:
    `log (1+1/x) ≤ (12*x^2+12*x+1)/(12*x^3+18*x^2+6*x)`. The modified domain
    is `[1/3,10]` and rewrites the logarithm as `log ((1+x)/x)`.
13. MT13, `0 < x`: `log (1+1/x) ≤ 1/sqrt (x^2+x)`. The modified domain is
    `[1/3,10]` and uses the same logarithm rewrite.
14. MT14, `0 ≤ x`: `exp (x-x^2) ≤ 1+x`. The modified domain is `[0,1]` and
    its right side is increased by `ε`.
15. MT15, `x < 1`: `exp (-x/(1-x)) ≤ 1-x`. The modified domain is
    `[-10,1/2]` and its right side is increased by `ε`.
16. MT16, `|x| < 1`: `|sin x| ≤ 6*|x|/5`. The modified domain is `[-1,1]`
    and its right side is increased by `ε`.
17. MT17, `0 < x < 1/2`: `1-2*x < cos (π*x)`. The modified domain is
    `[ε,100/201]`.
18. MT18, all real `x`: `0 ≤ cos x - 1 + x^2/2`. The modified domain is
    `[-10,10]` and adds `ε` to the right-hand expression.
19. MT19, `0 < x`:
    `8*sqrt 3*x/(3*sqrt 3 + sqrt (75+80*x^2)) < atan x`. The modified domain
    is `[0,10]`, changes `<` to `≤`, and adds `ε` to `atan x`.
20. MT20, `0 < x`: `1 < (x+1/x)*atan x`. The modified domain is `[ε,10]`.
21. MT21, `0 < x`: `3*x/(1+2*sqrt (1+x^2)) < atan x`. The modified domain
    is `[0,10]`, changes `<` to `≤`, and adds `ε` to `atan x`.
22. MT22, `0 < x ≤ π`: `cos x ≤ sin x/x`. The modified domain is `[ε,π]`.
23. MT23, `0 < x < π/2`: `cos x < (sin x/x)^2`. The modified domain is
    `[ε,π/2]`.
24. MT24, `x ∈ [π/3,2*π/3]`: `0 < sin x/3 + sin (3*x)/6`. The modified
    domain is `[π/3,2*π/3-ε]`.
25. MT25, `0 ≤ x`:
    `12 - 14.2*exp (-0.318*x)
      + (3.25*cos (1.16*x) - 0.155*sin (1.16*x))*exp (-1.34*x) > 0`.
    The modified domain is `[0,2]`.

Each fixture links its original TPTP file and records whether it belongs to
the original or modified suite. Decimal constants are parsed exactly before
any outward rounding.

MT19 through MT21 enter only after the `atan` rule milestone. The original
unbounded versions of MT7 through MT9, MT18, and MT25 require global analytic
or tail rules; finite subdivision of their modified boxes is not evidence for
the original statements.

The pinned
[Isabelle `Approximation_Ex` page](https://isabelle.in.tum.de/website-Isabelle2011/dist/library/HOL/Decision_Procs/Approximation_Ex.html)
adds the following exact strict enclosures. Decimal literals remain exact
rationals during reification.

```text
|log 2 - 544531980202654583340825686620847
           / 785593587443817081832229725798400| < 1/2^51
|exp 1.626 - 5.083499996273| < 10^-10
|sqrt 2 - 1.4142135623730951| < 10^-16
|π - 3.1415926535897932385| < 10^-18
|sin 100 + 0.50636564110975879| < 10^-17
```

It also supplies:

```text
3.2 ≤ x ≤ 6.2  ⟹ sin x ≤ 0
0 ≤ x ≤ 1      ⟹ x^2 ≤ x
0.5 ≤ x ≤ 4.5  ⟹ |atan x - 0.91| < 0.455
```

The arctangent case is repeated upstream as a decimal conjunction, the same
decimal bounds expressed by set membership, a tighter decimal box, and a
dyadic-fraction formulation. Retaining those forms tests exact literal parsing
and hypothesis reification rather than mathematical strength.

A later `tan` registration also takes the Isabelle fixture with
`g = 9.80665`, `v = 128.61`, and `d = π/180`:

```text
g/v * tan (35*d) ∈ [3*d, 3.1*d].
```

### Later challenge problems

- the LeanCert Li2 proof, which evolved from the symmetric `[0,1]` proposal
  with target `[1.039,1.06]`: seven pieces, exactly 2,300 middle cells, four
  100-cell numerical side intervals, and analytic endpoint pieces handling
  cancellation and removable behavior;
- the sharp entropy inequality from the Zulip thread, with separate endpoint
  analysis and an interior partition;
- interval Newton problems with narrow equation solution sets;
- sparse matrix and QR consumers that request componentwise enclosures;
- verified plotting on pixel boxes, where unresolved pixels receive an
  explicit `unknown` result rather than an invented color classification;
- selected Flyspeck, Caprasse, magnetism, heart, and Schwefel inequalities;
- affine and Taylor-model comparisons on the same boxes.

These cases do not enlarge the trusted base. A new method must still finish by
producing ordinary interval facts and replay the same branch theorem.

## Downstream applications

The following applications are not gates for the first tactic release. They
do constrain a few interfaces now: best-bound queries must return proofs,
batch certificates and subdivision must be reusable outside goal closure, and
the result type must leave room for existence as well as universal enclosure.

### Verified raster graphs

A verified graphing layer takes a function `f : ℝ → ℝ`, a proved input
domain, an exact dyadic viewport, and a finite pixel grid. Pixel ownership is
defined mathematically, using a canonical half-open partition with an explicit
convention for the outermost edges; it is not inferred from a graphics
library's floating-point coordinate conversion. For horizontal cell `X_j` and
vertical cell `Y_i`, its proof-facing result is initially three-valued:

```lean
inductive PixelClass
  | miss
  | hit
  | unknown
```

The raster certificate associates each `miss` with a proof that no
`x ∈ domain ∩ X_j` has `f x ∈ Y_i`, and each `hit` with a proof that some
such `x` exists. `unknown` is an honest unresolved cell, not a colored guess.
Direct exact witnesses, a certified point enclosure wholly inside a pixel, an
intermediate-value bracket, or a root-isolation certificate may establish a
hit. Ordinary range enclosure most naturally proves misses.

Two useful output contracts are deliberately distinct:

1. An **outer raster** marks a set of pixels whose union provably contains the
   graph in the viewport. It guarantees no missing graph point but may contain
   false-positive pixels. Column-wise range enclosures already provide this.
2. An **exact raster** proves for every pixel that it is lit if and only if its
   mathematical cell intersects the graph. It can be emitted only when every
   cell has a `hit` or `miss` certificate. A three-valued raster remains fully
   verified even when this stronger binary projection is unavailable.

The planner may use adaptive horizontal subdivision, a quadtree, derivative
and monotonicity bounds, continuity, and batched evaluation of shared
subexpressions. It should refine only pixels or columns whose classification
can change. The proof object binds the exact row-major classification array,
grid dimensions, viewport transform, and boundary convention. PNG encoding,
color selection, antialiasing, and display remain untrusted presentation; a
renderer is correct only insofar as it is shown or independently checked to
render that certified array. A hash may identify an exported array, but a hash
alone is not a theorem about a decoded image.

The first graphing milestone should target proved outer rasters plus explicit
misses and a small set of easy hits. Exact binary rasters, discontinuities,
implicit curves, and antialiased coverage are later experiments. RealPaver's
empty/feasible/inner/maybe distinction is evidence that retaining these result
classes is operationally useful.

### Certified differential equations

A later ODE layer can reuse the interval program, automatic differentiation,
Taylor payloads, local subdivision, batch checking, and gain-based policy. Its
basic certificate concerns an initial-value problem `u' = F(t,u)`. The API
distinguishes three claims: existence of at least one solution inside a tube;
an enclosure of the unique flow when an applicable uniqueness theorem covers
all solutions with the given initial data; and a universal reachable-set
enclosure for a set of initial data. Only the latter two justify saying that a
tube contains every solution of interest. A certified endpoint enclosure is
tagged by which claim proved it before adjacent step theorems are composed.

The additional mathematics is substantial and is not smuggled into the first
release requirements:

- a Picard or related inclusion proving that a solution exists in the proposed
  tube; a Lipschitz/contraction argument covering the ambient solution class
  when uniqueness is claimed; or a separate all-solutions a-priori containment
  theorem when a universal reachable tube is claimed;
- certified Taylor coefficients and a truncation/remainder enclosure over the
  whole step, not only a numerical endpoint evaluation;
- interval Jacobians, matrix bounds, and eventually affine or Taylor-model
  state to control the wrapping effect;
- exact composition of time-step domains and endpoint enclosures, including
  rejected steps and adaptive changes of step size and order;
- certified event isolation and preservation of invariants when a solver
  crosses a guard or changes regimes.

Step size, method order, preconditioning, and subdivision are untrusted search
choices. Their certificates replay through ordinary Lean theorems. The Bratu,
Troesch, and Broyden benchmark families are useful contractor and scaling
proxies before a full ODE certificate format exists, but passing their static
discretizations is not evidence by itself for existence, uniqueness, or a
validated flow. The current architecture should therefore preserve reusable
rule state and typed payloads without prematurely fixing an ODE-specific trace
format.

Step composition respects the claim tag. Two existence-only certificates do
not compose merely because their endpoint intervals overlap: the first may end
at a state different from the initial witness chosen by the second. The next
existence theorem must be uniform over every admitted predecessor endpoint, or
carry a dependent continuation theorem for the actual endpoint witness.
Unique-flow and universal-reachable certificates instead require the previous
output enclosure to be contained in the next step's certified input set.

## Conformance

The required Lean-only checks include:

- semantic theorems for every interval operation and endpoint shape;
- one direct and one certificate-backed propagator registration;
- failure of a deliberately corrupted registration payload;
- `[D4]` a dishonest compiled evaluator whose proposal is accepted into an
  untrusted retained trace and is then rejected by replay before goal
  assignment. The fixture uses a singleton whose true value lies outside the
  proposed interval, so an early heuristic rejection cannot accidentally be
  the only trust-boundary test;
- rejection of out-of-range operation, node, fact, and payload identifiers;
- `[D4]` rejection of a generated program extension with a bad topological order,
  invisible scope, duplicate canonical key, or equality edge whose proof
  recipe has different endpoints;
- rejection of a wrong input side or fact version, sibling or non-ancestor
  dependencies, cyclic or multiply-parented scopes, a mismatched split
  assumption, and a `Close.goal` whose facts do not imply the target;
- raw-expression reification for casts, decimals, powers, `abs`, shared terms,
  and finite folds;
- `[D4]` a cast regression in which intrinsic `0 ≤ (n : ℝ)` for `n : ℕ` is
  necessary inside a larger product, both normally and under `interval only`;
- goal closure for strict, non-strict, equality, disequality, membership,
  contradiction, and conjunction targets;
- safe refusal for an unsupported function and an exhausted budget;
- a proof axiom audit excluding compiler trust and `sorryAx`;
- proof sharing across repeated subexpressions and split branches;
- chunked fold replay at every chunk boundary;
- `[D2]` a `Lean.Kernel.whnf` and `decide +kernel` reduction probe in a
  downstream module for every registered kernel-facing checker, with one small
  case covering each recursive route and the complete transitive exposure
  closure rather than only the defining module;
- `[D4]` metamorphic determinism checks for `balancedV1` at a fixed step budget.
  Alpha-renaming and permutation of independent hypotheses compare normalized
  action keys and mathematical outputs, not unstable source identifiers. An
  inserted disconnected consistent fact is required to preserve only the
  result status and mathematical bound, because it legitimately changes the
  reified program and falls outside fixed-program trace determinism;
- `[D4]` one deliberately false target, `x ≤ 1` from `x ∈ [0,2]`, whose same
  exhausted `SearchResult` records a counterexample scope narrowed to `(1,2]`
  yet extracts the global best bound `[0,2]` under `ProofPlan.direct`; no fresh
  second search may satisfy the fixture, and no fact learned under the
  temporary negated target may appear in that plan.

Every malformed-trace case must fail before the tactic assigns the user's
goal metavariable.

The external oracle profile uses `python-flint` Arb for independently computed
point and elementary-function enclosures. For designated point, monotone, or
range fixtures where the pinned high-precision Arb computation is
independently known to enclose the complete original closed box more tightly
than the expected Lean result, Arb starts again from those exact inputs; after
an explicit outward conversion and stated rounding slack, its enclosure must
lie inside the enclosure returned by Lean. A separate assertion requires
Lean's enclosure to meet the fixture's width or endpoint target. Generic ball
evaluation is not required to fit inside a dependency-aware Lean enclosure:
fixtures where that premise is not justified instead use deterministic
rational samples, certified known extrema, and domain-boundary checks. Merely
placing both results inside the same coarse target is not an oracle check.
This is bug-finding evidence, not a proof and not a runtime dependency.
CoqInterval or MPFI comparison runs may be local informational tests.

The `core` profile runs on every PR. The medium FKS2 shard and available Arb
checks form `ci`; the complete 13,590-cell stream, complete translated solver
families, and expensive comparison campaigns are `local`/release tests. Split
JSONL fixtures keep generation and comparison streaming and avoid a single
large generated Lean module. “Release” means a pinned mandatory invocation of
that `local` profile, including chunked elaboration, kernel replay, and the
axiom audit; it is not a separate testing profile.

## Performance acceptance

The test harness records four times separately:

1. compiled planning and propagator execution;
2. proof expression construction;
3. elaboration and kernel replay;
4. incremental rebuild of a file importing the finished theorem.

It also records allocations, program nodes, accepted actions, rule calls,
splits, leaves, maximum endpoint heights, certificate bytes, proof nodes,
object-file size, cache hits and reused terms, and incremental work when an
existing series or table is extended to higher precision.

Initial targets, to be confirmed on the reference host during performance
validation, are:

- an exact arithmetic goal with at most 20 SSA nodes and no split: under
  200 ms end to end;
- a one-variable elementary goal with at most 50 SSA nodes: under 1 second;
- a successful proof with at most eight solver leaves: kernel replay no more
  than the compiled search time by a factor of two;
- the BKLNW case with upper limit 433 and 431 summands: proof size and replay
  grow at most linearly in the number of summands, with logarithmic proof
  depth;
- batch replay: no linear elaboration-depth growth and no chunk requiring an
  increased recursion limit;
- the per-PR FKS2 shard: bounded per-cell certificate size, shared static data,
  and no theorem or object-file blowup proportional to duplicated
  transcendental tables;
- the complete 13,590-cell FKS2 `local` run as a migration criterion,
  with the same per-cell metrics and a reported total wall-clock time.

The LeanCert version pinned by PNT+ is the migration baseline. The claim is
factual: Hex reproduces or strengthens the selected PNT+ mathematical corpus
with the transitive kernel-only trust set above, and on every large tier
improves either total time or artifact size without a serious regression on the
other measure, compared with LeanCert's trust-equivalent kernel route. A
campaign fixes the permitted regression threshold before measuring results;
the initial threshold is 20 percent. LeanCert's default native-route figures
are reported as context, not used as the pass/fail baseline, so trust and
performance remain distinct. This is a mathematical-workload and engineering
claim, not source compatibility or feature-for-feature parity.

## Development order

1. **D1 — endpoint kernel.** Prove interval semantics, normalization,
   arithmetic enclosure, rational projection, regularization, split coverage,
   and the complete empty-operation table.
2. **D2 — replay feasibility.** Before freezing representation, checker, or
   trace formats, build a narrow vertical feasibility prototype for one small
   arithmetic DAG, one bounded instantiation that adds a node and transports a
   fact across its equality edge, the BKLNW fold with
   upper limit 433, and one high-precision `exp` or `log` certificate. For each,
   record compiled checking, proof construction, kernel replay, transitive
   axioms, proof and object bytes, and incremental import time. Failure to make
   ordinary kernel replay practical changes the architecture before wider
   implementation. Compare bundled versus externally checked interval
   invariants, dyadic versus rational working facts, the branch-storage
   candidates, and direct versus reflected trace leaves. Install downstream
   kernel-reduction probes at this milestone and retain them thereafter. The
   trace schema remains provisional through D4 if this tiny extension case has
   not yet selected a representation.
3. **D3 — shared arithmetic.** Implement the production shared program,
   natural evaluator, generic soundness theorem, reifier, and scoped proof
   slicer for arithmetic over `ℝ`.
4. **D4 — extensible network.** Add the explicit rule registry, multiple
   methods per head, bounded expression instantiation, equality transport,
   contextual polynomial alternates, diagnostics, and the `interval` and
   `interval_bound` frontends. Compare eager, epoch-based, and lazy generation
   before selecting a default.
5. **D5 — first analytic rules.** Port the sine experiment to exact endpoints,
   add the paired cosine enclosure, stateful Taylor certificates, and the
   triple-angle rewrite.
6. **D6 — contractors.** Add centered automatic differentiation,
   derivative-sign monotonicity, and a recognizable HC4 forward/backward
   baseline with event-driven reactivation. Prototype 3B/CID-style local
   shaving and compare relative-improvement thresholds against unconditional
   worklist wakeups.
7. **D7 — elementary portfolio.** Add `π`, `exp`, `log`, square root, `atan`,
   positive-base real powers, certified range reduction, and symbolic special
   values.
8. **D8 — large certificates.** Add production chunked folds and the selected
   PNT+ point and sum migration corpus. Ensure every claimed ported theorem's
   transitive axiom set excludes everything forbidden by the Axiom contract,
   without requiring unchanged PNT+ tactic syntax or unrelated LeanCert APIs.
9. **D9 — branch search.** Add arbitrary and function-suggested subdivision,
   plus the Table 10, Table 12, and tiered FKS2 tests. Compare split variable,
   point, and node-order strategies rather than coupling them. Local shaving,
   interval Newton, the complete IMO partition, the full FKS2 run, and small
   translated RealPaver benchmarks are separately labeled prototype or
   migration-acceptance subtargets within this milestone.
10. **D10 — advanced dependency control.** Compare Bernstein,
    second-order, affine, and Taylor-model methods, plus gain-adaptive ACID-like
    contractor scheduling, on the challenge corpus before selecting further
    defaults. Exercise clean handoff to `hex-rcf` for genuinely univariate
    real-closed-field residuals; multivariate cases such as Motzkin remain
    outside that tactic's contract.

Every stage has real executable definitions and tests for its advertised
surface. Unimplemented methods remain absent rather than returning ceremonial
wide answers that masquerade as the intended algorithm.

`D1`–`D10` is a dependency order, not ten uniform release milestones. The first
public release target is D1–D8 plus the basic arbitrary/function-suggested
split path and small per-PR D9 samples. The PNT+ migration claim additionally
requires the source-pinned profile and comparison above, including the complete
FKS2 stream and whichever D9 contractor prototypes those cases actually need.
It does not require exact-source compatibility or replacement of every
LeanCert feature PNT+ currently imports. D10 is comparative follow-on work and
does not block the claim unless the measured migration corpus demonstrates
that one of its methods is necessary.

Verified raster graphing begins only after the `interval_bound` and batch APIs
are stable; certified ODE integration is a later client of D6/D10 machinery.
Neither application is a release or migration criterion above.

## Open design questions

The following choices require prototypes and measurements. They do not weaken
the fixed soundness and trust contracts.

1. Which elementary and user-registered approximation rules should spend
   extra work to prove an open cut, and which should return a sound closed
   enclosure? Exact arithmetic primitives already preserve tight endpoint
   attainment.
2. Is a two-component `IntervalSet` needed for the first contractor release,
   or are certified splits sufficient?
3. Which leaf classes are smaller with reflected Boolean checks, and which are
   smaller as direct theorem applications?
4. What batch chunk size minimizes combined construction and replay time on
   the reference host?
5. Should centered refinement visit only the output and high-influence nodes,
   or should a measured policy also offer an all-nodes pass?
6. Which functions beyond `exp`, `log`, `sin`, `cos`, `atan`, `Real.rpow`,
   square root, and `π` are required before the first public release?
7. Should optional MPFR, Arb, Sollya, or Gappa planners be supported in the
   first release, or only after the native planner meets the PNT+ corpus?
8. Which parts of a successful derivation should be serializable as a stable
   certificate format for generated tables?
9. Does the dyadic-working and exact-rational-source hybrid beat an exact
   rational working backend with regularization on real tactic workloads?
10. For the initial rule portfolio, do function-specific subdivision
    suggestions produce better gain per proof node than HC4, box consistency,
    3B/CID shaving, or interval Newton? Which RealPaver-style improvement
    thresholds and ACID learning signals remain useful after proof-construction
    cost is included?
11. Does `Hex.Interval` internally bundle the cut-consistency proof, or use
    plain normalized data with Boolean validation at construction and replay
    boundaries?
12. Which branch-state representation wins at the observed sizes: array
    copy-on-write, a persistent paged trie, chunked parent/delta overlays, or
    depth-first mutation with a rollback trail? Is a hybrid crossover useful?
13. What is the smallest stable derivation language after the D2 vertical
    prototype: explicit equality transport and program-extension constructors,
    or validated tables referenced by fewer generic constructors?
14. Should bounded expression instantiation be eager, propagation-epoch based,
    or fully lazy? Which triggers need congruence/E-matching, which should make
    direct structural proposals, and when should generated nodes be global
    rather than branch-local?
15. Which deterministic policy becomes the release default after comparing the
    staged `balancedV1` prototype, simple fair queues, RealPaver-style
    gain-adaptive scheduling, and bandit-like scores? The answer may differ by
    pinned policy name without altering proof validity.
16. For verified graphs, is the most useful first artifact a certified outer
    cover, a ternary raster with local hit/miss proofs, or both? Which hit
    certificates justify the cost of exact binary pixels?
17. Which interval, affine, or Taylor payload API can later serve validated ODE
    steps without freezing an ODE trace or complicating the first tactic?

## File organization

- `HexIntervalMathlib/Semantics.lean`: real membership and cut/set lemmas.
- `HexIntervalMathlib/Arithmetic.lean`: soundness of exact interval operations.
- `HexIntervalMathlib/Program.lean`: real program evaluation and natural
  evaluator soundness.
- `HexIntervalMathlib/Rule.lean`: registration environment and theorem-schema
  validation.
- `HexIntervalMathlib/Proof.lean`: derivation slicing, certificate checks, and
  proof construction.
- `HexIntervalMathlib/Reify.lean`: expressions, hypotheses, targets, and folds.
- `HexIntervalMathlib/Derivative.lean`: automatic differentiation and centered
  enclosures.
- `HexIntervalMathlib/Elementary/{SinCos,ExpLog,Sqrt,Constants}.lean`:
  elementary point and range rules.
- `HexIntervalMathlib/Contractor.lean`: backwards propagation theorems.
- `HexIntervalMathlib/Tactic.lean`: `interval`, `interval?`, and
  `interval_bound`.
- `HexIntervalMathlib/Examples.lean`: small user-facing examples.
- `conformance/HexInterval/Conformance.lean`: Mathlib-free computational
  checks for `hex-interval` only.
- `conformance/HexInterval/EmitFixtures.lean`: Mathlib-free arithmetic oracle
  fixtures.
- `conformance/HexIntervalMathlib/Conformance.lean`: tactic, replay, axiom, and
  small migrated downstream regressions in the per-PR `core` profile.
- `conformance/HexIntervalMathlib/CrossCheck.lean`: the measured deterministic
  medium FKS2 shard, included in the per-PR `HexConformance` target under the
  repository's standard heavier-check module name.
- `conformance/HexIntervalMathlib/EmitFixtures.lean`: elementary-function
  fixtures for the external oracle.
- `conformance-fixtures/HexIntervalMathlib/`: split JSONL inputs and pinned
  release manifests for the elementary and full-corpus campaigns.
- `conformance/HexIntervalMathlib/Generated/`: gitignored Lean chunk modules
  materialized only for a full local run. They belong to the explicit
  non-default `HexIntervalLocalConformance` Lake target, not the per-PR
  `HexConformance` globs.
- `scripts/conformance/run_hex_interval_local.sh`: stream the split JSONL,
  first regenerate the complete fixed set of chunk modules plus a balanced
  aggregator under that `Generated/` directory, then run
  `lake build HexIntervalLocalConformance`, and finally audit every resulting
  theorem. The target is never invoked without this generation step. The
  pinned release invocation records fixture hashes, chunk size, config, and
  toolchain.

Unlike a correspondence-only companion, `hex-interval-mathlib` contains an
executable reifier, rule registry, and tactic. Its own conformance target tests
that runtime-facing API while keeping the released Mathlib-free conformance
target free of Mathlib imports. Small explanatory examples remain in
`Examples.lean`; the bulk PNT+, nonlinear, and challenge corpus belongs in the
companion conformance project. Its `core` and measured `ci` profiles are built
on every PR; complete FKS2 and other full campaigns remain `local` campaigns,
with pinned invocations used as release gates. The generated local modules are
proof-bearing inputs to an ordinary Lake build, not a compiled fixture-only
shortcut, and no additional workflow or CI job is introduced.

## References

- Kim Morrison, [Interval arithmetic research note](https://hackmd.io/ZagrUv95RFSU-7WP9TNxUQ).
- Kim Morrison,
  [interval propagator and sine experiment](https://github.com/kim-em/mathlib4/blob/f174f3188252c99f17be96feee42b242cc465b2d/Mathlib/Analysis/SpecialFunctions/Trigonometric/Intervals.lean).
- Guillaume Melquiond,
  [The Coq Interval library](https://guillaume.melquiond.fr/doc/15-jar.pdf).
- [IEEE Standard for Interval Arithmetic](https://grouper.ieee.org/groups/1788/).
- [GNU MPFR algorithms](https://www.mpfr.org/algorithms.pdf).
- [Sollya evaluation and rewriting documentation](https://sollya.org/sollya-2.9/help.php).
- Alexey Solovyev and Thomas Hales,
  [Formal verification of nonlinear inequalities with Taylor interval approximations](https://arxiv.org/abs/1301.1702).
- Florent de Dinechin, Christoph Lauter, and Guillaume Melquiond,
  [Certifying the floating-point implementation of an elementary function using Gappa](https://arxiv.org/abs/cs/0701186).
- Russell O'Connor,
  [Certified exact transcendental real number computation in Coq](https://arxiv.org/abs/0805.2438).
- Robbert Krebbers and Bas Spitters,
  [Computer certified efficient exact reals in Coq](https://arxiv.org/abs/1105.2751).
- Fredrik Johansson,
  [Arb: efficient arbitrary-precision midpoint-radius interval arithmetic](https://arxiv.org/abs/1611.02831).
- [IBEX contractors](https://ibex-team.github.io/ibex-lib/contractor.html)
  and [IBEX strategies](https://ibex-team.github.io/ibex-lib/strategy.html).
- Laurent Granvilliers and Frédéric Benhamou,
  [Algorithm 852: RealPaver](https://hal.science/hal-00480813),
  together with the
  [RealPaver 1.1 paper](https://doi.org/10.21105/joss.09331) and
  [source repository](https://github.com/realpaver/realpaver).
- [Isabelle verified affine arithmetic](https://isa-afp.org/entries/Affine_Arithmetic.html)
  and [verified Taylor models](https://isa-afp.org/entries/Taylor_Models.html).
- Lawrence Paulson,
  [MetiTarski: past and future](https://www.cl.cam.ac.uk/~lp15/papers/Arith/calculemus2008.pdf).
- Sicun Gao, Jeremy Avigad, and Edmund Clarke,
  [Delta-complete decision procedures for satisfiability over the reals](https://arxiv.org/abs/1204.3513).
- [IntervalArithmetic.jl documentation](https://juliaintervals.github.io/IntervalArithmetic.jl/stable/).
- LeanCert at the original detailed-audit snapshot
  [`31579b5`](https://github.com/alerad/leancert/tree/31579b55618d11e4fbe622a6b5e30b0359b2ee6d),
  the current PNT+ LeanCert pin
  [`58edbea`](https://github.com/alerad/leancert/tree/58edbea59458e9b010262238eaca27b6e0240dae),
  and PNT+ at
  [`21998bb`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/21998bb6196b56789f72a52656a781a75e134eb0).
